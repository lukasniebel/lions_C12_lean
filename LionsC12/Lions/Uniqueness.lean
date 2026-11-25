module

public import LionsC12.Lions.Gelfand
public import LionsC12.Lions.WeakDeriv
public import LionsC12.Lions.Energy
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Lions' theorem: uniqueness and the continuous representative

This file completes the abstract parabolic theory.  Given the existence part
(`LionsC12.lions_existence`, proved in `LionsC12.Lions.Gelfand`), the weak-derivative toolbox
(`LionsC12.Lions.WeakDeriv`) and the Lions–Magenes energy identity (`LionsC12.Lions.Energy`), we
prove

* `lions_uniqueness` — two variational solutions with the same data agree a.e.;
* `lions_theorem` — the combined existence-and-uniqueness statement;
* `variational_continuous` — the variational solution has a representative in `C([0,T); H)`
  which attains the initial value and satisfies the energy identity.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set
open scoped InnerProductSpace

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ### Auxiliary facts -/

/-- Almost every `t ∈ (0,T]` lies in the open interval `(0,T)`. -/
theorem ae_mem_Ioo_μT (T : ℝ) : ∀ᵐ t ∂(μT T), t ∈ Set.Ioo 0 T := by
  rw [μT_eq_restrict_Ioo]
  exact ae_restrict_mem measurableSet_Ioo

/-- Almost every `t ∈ (0,T]` lies in `[0,T)`. -/
theorem ae_mem_Ico_μT (T : ℝ) : ∀ᵐ t ∂(μT T), t ∈ Set.Ico 0 T := by
  filter_upwards [ae_mem_Ioo_μT T] with t ht using ⟨ht.1.le, ht.2⟩

/-- The integrand of the variational identity is interval integrable on `[0,T]`. -/
theorem intervalIntegrable_variational (G : GelfandTriple V H) {T : ℝ} (hT : 0 < T)
    {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α : ℝ} (hA : IsFormFamily T A M α)
    {u : ℝ → V} (hu : MeasureTheory.MemLp u 2 (μT T)) {φ : ℝ → V} (hφ : IsTestV T φ) :
    IntervalIntegrable
      (fun t => -(⟪G.j (u t), G.j (deriv φ t)⟫_ℝ) + A t (u t) (φ t)) volume 0 T := by
  have hu1 : MeasureTheory.Integrable u (μT T) := hu.integrable one_le_two
  have hflat : MeasureTheory.Integrable (fun t => G.flat (G.j (u t))) (μT T) :=
    ContinuousLinearMap.integrable_comp (G.flat ∘L G.j) hu1
  have h1 : MeasureTheory.Integrable
      (fun t => -(⟪G.j (u t), G.j (deriv φ t)⟫_ℝ)) (μT T) := by
    have h := integrable_apply_of_continuous hflat hφ.continuous_deriv
    simpa using h.neg
  have h2 : MeasureTheory.Integrable (fun t => A t (u t) (φ t)) (μT T) :=
    integrable_apply_of_continuous (integrable_form_apply_left hA hu1) hφ.continuous
  exact intervalIntegrable_of_integrable_μT hT.le (h1.add h2)

omit [CompleteSpace V] in
/-- Coercivity makes `τ ↦ A τ (w τ) (w τ)` nonnegative, hence its integral is nonnegative. -/
theorem integral_form_self_nonneg {T : ℝ} {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α : ℝ}
    (hA : IsFormFamily T A M α) (w : ℝ → V) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∫ τ in (0 : ℝ)..t, A τ (w τ) (w τ) := by
  refine intervalIntegral.integral_nonneg ht fun τ _ => ?_
  exact le_trans (mul_nonneg hA.α_pos.le (sq_nonneg _)) (hA.coercive τ (w τ))

/-- Linearity of the variational formulation: the difference of two variational solutions with
the same data `(f, u₀)` is a variational solution with data `(0, 0)`. -/
theorem isVariationalSolution_sub (G : GelfandTriple V H) {T : ℝ} (hT : 0 < T)
    {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α : ℝ} (hA : IsFormFamily T A M α)
    {f : ℝ → StrongDual ℝ V} {u₀ : H} {u₁ u₂ : ℝ → V}
    (h₁ : IsVariationalSolution G T A f u₀ u₁) (h₂ : IsVariationalSolution G T A f u₀ u₂) :
    IsVariationalSolution G T A (0 : ℝ → StrongDual ℝ V) (0 : H) (fun t => u₁ t - u₂ t) := by
  obtain ⟨hL₁, hv₁⟩ := h₁
  obtain ⟨hL₂, hv₂⟩ := h₂
  refine ⟨hL₁.sub hL₂, ?_⟩
  intro φ hφ
  have hi₁ := intervalIntegrable_variational G hT hA hL₁ hφ
  have hi₂ := intervalIntegrable_variational G hT hA hL₂ hφ
  have hsplit : (∫ t in (0 : ℝ)..T,
        (-(⟪G.j ((fun t => u₁ t - u₂ t) t), G.j (deriv φ t)⟫_ℝ)
          + A t ((fun t => u₁ t - u₂ t) t) (φ t)))
      = (∫ t in (0 : ℝ)..T, (-(⟪G.j (u₁ t), G.j (deriv φ t)⟫_ℝ) + A t (u₁ t) (φ t)))
        - ∫ t in (0 : ℝ)..T, (-(⟪G.j (u₂ t), G.j (deriv φ t)⟫_ℝ) + A t (u₂ t) (φ t)) := by
    rw [← intervalIntegral.integral_sub hi₁ hi₂]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [map_sub, inner_sub_left, sub_apply]
    ring
  rw [hsplit, hv₁ φ hφ, hv₂ φ hφ]
  simp

/-! ### Uniqueness -/

/-- **Lions' theorem, uniqueness part**: two variational solutions with the same data agree a.e.
on `(0,T)`. -/
theorem lions_uniqueness (G : GelfandTriple V H) {T : ℝ} (hT : 0 < T)
    {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α : ℝ} (hA : IsFormFamily T A M α)
    {f : ℝ → StrongDual ℝ V} {u₀ : H} {u₁ u₂ : ℝ → V}
    (h₁ : IsVariationalSolution G T A f u₀ u₁) (h₂ : IsVariationalSolution G T A f u₀ u₂) :
    ∀ᵐ t ∂(μT T), u₁ t = u₂ t := by
  -- `w := u₁ - u₂` solves the problem with data `(0, 0)`.
  set w : ℝ → V := fun t => u₁ t - u₂ t with hwdef
  have hw : IsVariationalSolution G T A (0 : ℝ → StrongDual ℝ V) (0 : H) w :=
    isVariationalSolution_sub G hT hA h₁ h₂
  have hzeroLp : MeasureTheory.MemLp (0 : ℝ → StrongDual ℝ V) 2 (μT T) :=
    memLp_const (0 : StrongDual ℝ V)
  obtain ⟨hweak, hgL2⟩ := hasWeakDerivV'_of_variational G hT hA hzeroLp hw
  set g : ℝ → StrongDual ℝ V := fun t => (0 : ℝ → StrongDual ℝ V) t - A t (w t) with hgdef
  have hW : MemW G T w g := ⟨hw.1, hgL2, hweak⟩
  obtain ⟨wt, c, _hcont, hae, hflat, hen⟩ := lions_magenes G hT hW
  -- The constant of the absolutely continuous representative vanishes.
  have hc0 : c = 0 := by
    have hac : ∀ᵐ t ∂(μT T), G.flat (G.j (w t))
        = c + ∫ τ in (0 : ℝ)..t, (fun τ => (0 : ℝ → StrongDual ℝ V) τ - A τ (w τ)) τ := by
      filter_upwards [hae, ae_mem_Ico_μT T] with t h1 h2
      rw [← h1]
      exact hflat t h2
    have h := const_eq_flat_of_variational G hT hA hzeroLp hw hac
    simpa using h
  have h0mem : (0 : ℝ) ∈ Set.Ico 0 T := ⟨le_refl 0, hT⟩
  -- The representative starts at `0`.
  have hwt0 : wt 0 = 0 := by
    refine G.flat_injective ?_
    rw [hflat 0 h0mem, hc0, map_zero, intervalIntegral.integral_same, add_zero]
  -- The energy identity plus coercivity force the representative to vanish.
  have hvanish : ∀ t ∈ Set.Ico 0 T, wt t = 0 := by
    intro t ht
    have he := hen 0 h0mem t ht
    rw [hwt0, norm_zero] at he
    have hrw : (∫ τ in (0 : ℝ)..t, g τ (w τ))
        = -∫ τ in (0 : ℝ)..t, A τ (w τ) (w τ) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun τ _ => ?_
      simp [hgdef]
    rw [hrw] at he
    have hnn : 0 ≤ ∫ τ in (0 : ℝ)..t, A τ (w τ) (w τ) :=
      integral_form_self_nonneg hA w ht.1
    have hle : ‖wt t‖ ^ 2 ≤ 0 := by
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, sub_zero] at he
      rw [he]
      linarith
    have : ‖wt t‖ = 0 := by nlinarith [norm_nonneg (wt t)]
    exact norm_eq_zero.mp this
  -- Hence `w = 0` a.e.
  filter_upwards [hae, ae_mem_Ico_μT T] with t h1 h2
  have hj : G.j (w t) = 0 := by rw [← h1]; exact hvanish t h2
  have hw0 : w t = 0 := G.injective (by rw [hj, map_zero])
  exact sub_eq_zero.mp hw0

/-- **Lions' theorem.** -/
theorem lions_theorem (G : GelfandTriple V H) {T : ℝ} (hT : 0 < T)
    {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α : ℝ} (hA : IsFormFamily T A M α)
    {f : ℝ → StrongDual ℝ V} (hf : MeasureTheory.MemLp f 2 (μT T)) (u₀ : H) :
    (∃ u : ℝ → V, IsVariationalSolution G T A f u₀ u) ∧
    ∀ u₁ u₂ : ℝ → V, IsVariationalSolution G T A f u₀ u₁ →
      IsVariationalSolution G T A f u₀ u₂ → ∀ᵐ t ∂(μT T), u₁ t = u₂ t :=
  ⟨lions_existence G hT hA hf u₀, fun _ _ h₁ h₂ => lions_uniqueness G hT hA h₁ h₂⟩

/-! ### The continuous representative -/

/-- The variational solution is continuous into `H` and attains the initial value: `ũ(0) = u₀`. -/
theorem variational_continuous (G : GelfandTriple V H) {T : ℝ} (hT : 0 < T)
    {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α : ℝ} (hA : IsFormFamily T A M α)
    {f : ℝ → StrongDual ℝ V} (hf : MeasureTheory.MemLp f 2 (μT T)) {u₀ : H} {u : ℝ → V}
    (hu : IsVariationalSolution G T A f u₀ u) :
    ∃ ũ : ℝ → H, ContinuousOn ũ (Set.Ico 0 T) ∧ (∀ᵐ t ∂(μT T), ũ t = G.j (u t)) ∧ ũ 0 = u₀ ∧
      ∀ t ∈ Set.Ico 0 T,
        ‖ũ t‖ ^ 2 = ‖u₀‖ ^ 2 + 2 * ∫ τ in (0 : ℝ)..t, (f τ (u τ) - A τ (u τ) (u τ)) := by
  obtain ⟨hweak, hgL2⟩ := hasWeakDerivV'_of_variational G hT hA hf hu
  set g : ℝ → StrongDual ℝ V := fun t => f t - A t (u t) with hgdef
  have hW : MemW G T u g := ⟨hu.1, hgL2, hweak⟩
  obtain ⟨ũ, c, hcont, hae, hflat, hen⟩ := lions_magenes G hT hW
  have hc : c = G.flat u₀ := by
    refine const_eq_flat_of_variational G hT hA hf hu ?_
    filter_upwards [hae, ae_mem_Ico_μT T] with t h1 h2
    rw [← h1]
    exact hflat t h2
  have h0mem : (0 : ℝ) ∈ Set.Ico 0 T := ⟨le_refl 0, hT⟩
  have hũ0 : ũ 0 = u₀ := by
    refine G.flat_injective ?_
    rw [hflat 0 h0mem, hc, intervalIntegral.integral_same, add_zero]
  refine ⟨ũ, hcont, hae, hũ0, ?_⟩
  intro t ht
  have he := hen 0 h0mem t ht
  rw [hũ0] at he
  have hrw : (∫ τ in (0 : ℝ)..t, g τ (u τ))
      = ∫ τ in (0 : ℝ)..t, (f τ (u τ) - A τ (u τ) (u τ)) := by
    refine intervalIntegral.integral_congr fun τ _ => ?_
    simp [hgdef]
  rw [hrw] at he
  linarith

end LionsC12

end
