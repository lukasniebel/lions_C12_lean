module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Lions' projection theorem

This file contains the abstract functional-analytic core of J.-L. Lions' existence theorem:
a Lax–Milgram type statement in which the bilinear form is only assumed to be continuous and
coercive with respect to a *smaller* test space `Φ` carrying a "size" function `N`.

The proof follows the classical route: represent the form by a Riesz vector `T φ`, define the
linear functional `T φ ↦ L φ` on the range of `T` (well defined and bounded thanks to the
coercivity estimate `α * N φ ≤ ‖T φ‖`), extend it to the whole space by Hahn–Banach and
represent the extension by a vector `u`.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open scoped InnerProductSpace

/-- **Lions' projection theorem** (Lax–Milgram with a smaller test space).  `F` is a real Hilbert
space, `Φ` a real vector space with a "size" `N : Φ → ℝ` (no axioms on `N` are needed),
`ι : Φ →ₗ F` with `‖ι φ‖ ≤ N φ`, `E φ : F →L ℝ` continuous linear in `u`, linear in `φ`,
coercive `α (N φ)² ≤ E φ (ι φ)`, and `L` linear with `|L φ| ≤ C N φ`.  Then some `u ∈ F` with
`‖u‖ ≤ C/α` satisfies `E φ u = L φ` for all `φ`. -/
theorem lions_projection {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F]
    {Φ : Type*} [AddCommGroup Φ] [Module ℝ Φ]
    (ι : Φ →ₗ[ℝ] F) (N : Φ → ℝ) (hN : ∀ φ, 0 ≤ N φ) (hιN : ∀ φ, ‖ι φ‖ ≤ N φ)
    (E : Φ → F →L[ℝ] ℝ) (hE : ∀ u, IsLinearMap ℝ (fun φ => E φ u))
    {α : ℝ} (hα : 0 < α) (hcoer : ∀ φ, α * N φ ^ 2 ≤ E φ (ι φ))
    (L : Φ →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C) (hL : ∀ φ, |L φ| ≤ C * N φ) :
    ∃ u : F, (∀ φ, E φ u = L φ) ∧ ‖u‖ ≤ C / α := by
  classical
  -- The Riesz representative of the form `E φ`.
  obtain ⟨T, hT⟩ : ∃ T : Φ →ₗ[ℝ] F, ∀ (φ : Φ) (y : F), ⟪T φ, y⟫_ℝ = E φ y := by
    refine ⟨{ toFun := fun φ => (InnerProductSpace.toDual ℝ F).symm (E φ)
              map_add' := ?_
              map_smul' := ?_ }, fun φ y => InnerProductSpace.toDual_symm_apply⟩
    · intro φ ψ
      refine ext_inner_right ℝ fun v => ?_
      have h1 : ⟪(InnerProductSpace.toDual ℝ F).symm (E (φ + ψ)), v⟫_ℝ = E (φ + ψ) v :=
        InnerProductSpace.toDual_symm_apply
      have h2 : ⟪(InnerProductSpace.toDual ℝ F).symm (E φ), v⟫_ℝ = E φ v :=
        InnerProductSpace.toDual_symm_apply
      have h3 : ⟪(InnerProductSpace.toDual ℝ F).symm (E ψ), v⟫_ℝ = E ψ v :=
        InnerProductSpace.toDual_symm_apply
      rw [h1, inner_add_left, h2, h3]
      exact (hE v).map_add φ ψ
    · intro c φ
      refine ext_inner_right ℝ fun v => ?_
      have h1 : ⟪(InnerProductSpace.toDual ℝ F).symm (E (c • φ)), v⟫_ℝ = E (c • φ) v :=
        InnerProductSpace.toDual_symm_apply
      have h2 : ⟪(InnerProductSpace.toDual ℝ F).symm (E φ), v⟫_ℝ = E φ v :=
        InnerProductSpace.toDual_symm_apply
      rw [RingHom.id_apply, h1, real_inner_smul_left, h2]
      simpa using (hE v).map_smul c φ
  -- Coercivity gives the lower bound `α * N φ ≤ ‖T φ‖`.
  have hTnorm : ∀ φ, α * N φ ≤ ‖T φ‖ := by
    intro φ
    rcases eq_or_lt_of_le (hN φ) with h0 | hpos
    · rw [← h0, mul_zero]; exact norm_nonneg _
    · have h1 : α * N φ ^ 2 ≤ ⟪T φ, ι φ⟫_ℝ := by rw [hT]; exact hcoer φ
      have h2 : ⟪T φ, ι φ⟫_ℝ ≤ ‖T φ‖ * ‖ι φ‖ := real_inner_le_norm _ _
      have h3 : ‖T φ‖ * ‖ι φ‖ ≤ ‖T φ‖ * N φ :=
        mul_le_mul_of_nonneg_left (hιN φ) (norm_nonneg _)
      have h4 : α * N φ * N φ ≤ ‖T φ‖ * N φ := by nlinarith
      exact le_of_mul_le_mul_right h4 hpos
  have hCα : 0 ≤ C / α := div_nonneg hC hα.le
  -- Hence `L` is bounded by `(C/α) ‖T φ‖`.
  have hLT : ∀ φ, |L φ| ≤ C / α * ‖T φ‖ := by
    intro φ
    have h1 : |L φ| ≤ C * N φ := hL φ
    have h2 : C / α * (α * N φ) ≤ C / α * ‖T φ‖ :=
      mul_le_mul_of_nonneg_left (hTnorm φ) hCα
    have h3 : C / α * (α * N φ) = C * N φ := by field_simp
    linarith
  -- `L` kills the kernel of `T`, so it descends to the range of `T`.
  have hker : LinearMap.ker T ≤ LinearMap.ker L := by
    intro φ hφ
    have h0 : T φ = 0 := LinearMap.mem_ker.mp hφ
    have h1 := hLT φ
    rw [h0, norm_zero, mul_zero] at h1
    exact LinearMap.mem_ker.mpr (abs_nonpos_iff.mp h1)
  obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ₀ : (LinearMap.range T) →ₗ[ℝ] ℝ,
      ∀ (x : LinearMap.range T) (φ : Φ), (x : F) = T φ → ℓ₀ x = L φ := by
    refine ⟨((LinearMap.ker T).liftQ L hker).comp
      (T.quotKerEquivRange.symm : (LinearMap.range T) →ₗ[ℝ] (Φ ⧸ LinearMap.ker T)), ?_⟩
    intro x φ hφ
    have hx : x = T.quotKerEquivRange (Submodule.Quotient.mk φ) := by
      apply Subtype.ext
      rw [hφ, LinearMap.quotKerEquivRange_apply_mk]
    rw [hx]
    show ((LinearMap.ker T).liftQ L hker)
        (T.quotKerEquivRange.symm (T.quotKerEquivRange (Submodule.Quotient.mk φ))) = L φ
    rw [LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  have hℓbound : ∀ x : LinearMap.range T, ‖ℓ₀ x‖ ≤ C / α * ‖x‖ := by
    intro x
    obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp x.2
    rw [hℓ₀ x φ hφ.symm, Real.norm_eq_abs, ← Submodule.norm_coe, ← hφ]
    exact hLT φ
  -- Hahn–Banach extension.
  obtain ⟨g, hg, hgnorm⟩ :=
    exists_extension_norm_eq (LinearMap.range T) (ℓ₀.mkContinuous (C / α) hℓbound)
  have hgle : ‖g‖ ≤ C / α := by
    rw [hgnorm]; exact ℓ₀.mkContinuous_norm_le hCα hℓbound
  refine ⟨(InnerProductSpace.toDual ℝ F).symm g, fun φ => ?_, ?_⟩
  · rw [← hT φ, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    have h2 : g (T φ) = (ℓ₀.mkContinuous (C / α) hℓbound) ⟨T φ, ⟨φ, rfl⟩⟩ :=
      hg ⟨T φ, ⟨φ, rfl⟩⟩
    rw [h2, LinearMap.mkContinuous_apply]
    exact hℓ₀ _ φ rfl
  · rw [LinearIsometryEquiv.norm_map]
    exact hgle

end LionsC12

end
