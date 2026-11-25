module

public import LionsC12.Construction.Defs
public import LionsC12.Coefficient.Blocks
public import LionsC12.Coefficient.Support
public import LionsC12.Modes.Trig
public import LionsC12.Solution.Basic
public import LionsC12.Solution.Divergence
public import LionsC12.Forcing.Cancellation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral

/-!
# The elliptic part: `𝒜(t) u(t) ∈ H` pointwise, but not in `L²(0,1;H)`

For every fixed time `t` the function `x ↦ (𝒜(t)u(t))(x)` is continuous on `[0, π]`,
hence lies in `H = L²(0,π)`; concretely `u(t) ∈ D(A_H(t))`.

The forcing `f` is uniformly bounded (`abs_f_le` in `LionsC12.Forcing.Cancellation`), so
`‖f(t)‖_H² ≤ π C_f²` for every `t`.  Since `∂_t u = f - 𝒜u` pointwise, we get
`‖∂_t u(t)‖_H² ≤ 2 ‖f(t)‖_H² + 2 ‖𝒜(t)u(t)‖_H²`, and the divergence of
`∫₀¹ ‖∂_t u‖_H²` proved in `LionsC12.Solution.Divergence` forces
`∫₀¹ ‖𝒜(t)u(t)‖_H² dt = ∞`, i.e. `A_H(·)u(·) ∉ L²(0,1;H)`.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ### Block dichotomy -/

/-- Either `t` lies in some block `I_j`, or it lies in none. -/
theorem mem_block_or_not (t : ℝ) : (∃ j, t ∈ I j) ∨ (∀ i, t ∉ I i) := by
  by_cases h : ∃ j, t ∈ I j
  · exact Or.inl h
  · exact Or.inr fun i hi => h ⟨i, hi⟩

/-! ### Continuity in the space variable -/

theorem continuous_βxblock_x (j : ℕ) (t : ℝ) : Continuous fun x => βxblock D j t x := by
  show Continuous fun x : ℝ =>
    ∑ m ∈ Finset.Icc 1 (M j), -(ηj D j t * sin (θ j m t) * sin (K j m * x))
  exact continuous_finsetSum _ fun m _ =>
    (continuous_const.mul (continuous_sin_mul ((K j m : ℕ) : ℝ))).neg

theorem continuous_vxxblock_x (ε : ℝ) (j : ℕ) (t : ℝ) :
    Continuous fun x => vxxblock D ε j t x := by
  show Continuous fun x : ℝ => ∑ m ∈ Finset.Icc 1 (M j), y D ε j m t * p'' (K j m) x
  exact continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_p'' (K j m))

theorem continuous_vtblock_x (ε : ℝ) (j : ℕ) (t : ℝ) :
    Continuous fun x => vtblock D ε j t x := by
  show Continuous fun x : ℝ => ∑ m ∈ Finset.Icc 1 (M j), y' D ε j m t * p (K j m) x
  exact continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_p (K j m))

theorem continuous_βx_x (t : ℝ) : Continuous fun x => βx D t x := by
  rcases mem_block_or_not t with ⟨j, hj⟩ | h
  · have e : (fun x => βx D t x) = fun x => βxblock D j t x :=
      funext fun x => βx_eq_block D hj x
    rw [e]; exact continuous_βxblock_x D j t
  · have e : (fun x => βx D t x) = fun _ => (0 : ℝ) := funext fun x => βx_eq_zero D h x
    rw [e]; exact continuous_const

theorem continuous_vxx_x (ε t : ℝ) : Continuous fun x => vxx D ε t x := by
  rcases mem_block_or_not t with ⟨j, hj⟩ | h
  · have e : (fun x => vxx D ε t x) = fun x => vxxblock D ε j t x :=
      funext fun x => vxx_eq_block D ε hj x
    rw [e]; exact continuous_vxxblock_x D ε j t
  · have e : (fun x => vxx D ε t x) = fun _ => (0 : ℝ) := funext fun x => vxx_eq_zero D ε h x
    rw [e]; exact continuous_const

theorem continuous_vt_x (ε t : ℝ) : Continuous fun x => vt D ε t x := by
  rcases mem_block_or_not t with ⟨j, hj⟩ | h
  · have e : (fun x => vt D ε t x) = fun x => vtblock D ε j t x :=
      funext fun x => vt_eq_block D ε hj x
    rw [e]; exact continuous_vtblock_x D ε j t
  · have e : (fun x => vt D ε t x) = fun _ => (0 : ℝ) := funext fun x => vt_eq_zero D ε h x
    rw [e]; exact continuous_const

theorem continuous_β_x (t : ℝ) : Continuous fun x => β D t x :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_β_x D t x).continuousAt

theorem continuous_a_x (ε t : ℝ) : Continuous fun x => a D ε t x := by
  show Continuous fun x : ℝ => 1 + ε * β D t x
  exact continuous_const.add (continuous_const.mul (continuous_β_x D t))

theorem continuous_ux_x (ε t : ℝ) : Continuous fun x => ux D ε t x :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_ux_x D ε t x).continuousAt

theorem continuous_uxx_x (ε t : ℝ) : Continuous fun x => uxx D ε t x := by
  show Continuous fun x : ℝ => D.ρ t * φ'' x + vxx D ε t x
  exact (continuous_const.mul continuous_φ'').add (continuous_vxx_x D ε t)

/-- For every `t`, `x ↦ (𝒜(t)u(t))(x)` is continuous (so `𝒜(t)u(t) ∈ H`, i.e.
`u(t) ∈ D(A_H(t))`, concretely). -/
theorem continuous_Au_x (ε t : ℝ) : Continuous (fun x => Au D ε t x) := by
  show Continuous fun x : ℝ => -(ε * βx D t x * ux D ε t x) - a D ε t x * uxx D ε t x
  exact (((continuous_const.mul (continuous_βx_x D t)).mul (continuous_ux_x D ε t)).neg).sub
    ((continuous_a_x D ε t).mul (continuous_uxx_x D ε t))

theorem continuous_ut_x (ε t : ℝ) : Continuous (fun x => ut D ε t x) := by
  show Continuous fun x : ℝ => D.ρ' t * φ x + vt D ε t x
  exact (continuous_const.mul continuous_φ).add (continuous_vt_x D ε t)

theorem continuous_f_x (ε t : ℝ) : Continuous (fun x => f D ε t x) := by
  have e : (fun x => f D ε t x) = fun x => ut D ε t x + Au D ε t x :=
    funext fun x => (pde D ε t x).symm
  rw [e]
  exact (continuous_ut_x D ε t).add (continuous_Au_x D ε t)

/-! ### The `H`-norms -/

theorem normSq_f_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : ℝ) :
    normSq (f D ε t) ≤ π * (Cf D) ^ 2 := by
  have hint1 : IntervalIntegrable (fun x => (f D ε t x) ^ 2) MeasureTheory.volume 0 π :=
    ((continuous_f_x D ε t).pow 2).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun _ : ℝ => (Cf D) ^ 2) MeasureTheory.volume 0 π :=
    intervalIntegrable_const
  have hmono : (∫ x in (0 : ℝ)..π, (f D ε t x) ^ 2) ≤ ∫ _ in (0 : ℝ)..π, (Cf D) ^ 2 := by
    refine intervalIntegral.integral_mono_on Real.pi_pos.le hint1 hint2 fun x _ => ?_
    have h := abs_f_le D hε0 hε1 t x
    nlinarith [abs_nonneg (f D ε t x), sq_abs (f D ε t x)]
  rw [intervalIntegral.integral_const] at hmono
  simpa [normSq, smul_eq_mul] using hmono

/-- `‖∂_t u‖² ≤ 2 ‖f‖² + 2 ‖𝒜u‖²` pointwise in `t` (from `∂_t u = f - 𝒜u`). -/
theorem utNormSq_le (ε t : ℝ) : utNormSq D ε t ≤ 2 * normSq (f D ε t) + 2 * normSq (Au D ε t) := by
  have hfi : IntervalIntegrable (fun x => (f D ε t x) ^ 2) MeasureTheory.volume 0 π :=
    ((continuous_f_x D ε t).pow 2).intervalIntegrable _ _
  have hAi : IntervalIntegrable (fun x => (Au D ε t x) ^ 2) MeasureTheory.volume 0 π :=
    ((continuous_Au_x D ε t).pow 2).intervalIntegrable _ _
  have hui : IntervalIntegrable (fun x => (ut D ε t x) ^ 2) MeasureTheory.volume 0 π :=
    ((continuous_ut_x D ε t).pow 2).intervalIntegrable _ _
  have hgi : IntervalIntegrable
      (fun x => 2 * (f D ε t x) ^ 2 + 2 * (Au D ε t x) ^ 2) MeasureTheory.volume 0 π :=
    (hfi.const_mul 2).add (hAi.const_mul 2)
  have hmono : (∫ x in (0 : ℝ)..π, (ut D ε t x) ^ 2)
      ≤ ∫ x in (0 : ℝ)..π, (2 * (f D ε t x) ^ 2 + 2 * (Au D ε t x) ^ 2) := by
    refine intervalIntegral.integral_mono_on Real.pi_pos.le hui hgi fun x _ => ?_
    have hut : ut D ε t x = f D ε t x - Au D ε t x := by linarith [pde D ε t x]
    rw [hut]
    nlinarith [sq_nonneg (f D ε t x + Au D ε t x)]
  have heq : (∫ x in (0 : ℝ)..π, (2 * (f D ε t x) ^ 2 + 2 * (Au D ε t x) ^ 2))
      = 2 * normSq (f D ε t) + 2 * normSq (Au D ε t) := by
    rw [intervalIntegral.integral_add (hfi.const_mul 2) (hAi.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rfl
  rw [heq] at hmono
  simpa [utNormSq, normSq] using hmono

/-! ### Divergence of the elliptic part -/

theorem lintegral_normSq_Au_eq_top {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (normSq (Au D ε t)) = ⊤ := by
  by_contra htop
  set C : ℝ := 2 * (π * (Cf D) ^ 2) with hCdef
  have hCnn : 0 ≤ C := by
    have : (0 : ℝ) ≤ π := Real.pi_pos.le
    rw [hCdef]; positivity
  have hpt : ∀ t : ℝ, ENNReal.ofReal (utNormSq D ε t)
      ≤ ENNReal.ofReal C + ENNReal.ofReal 2 * ENNReal.ofReal (normSq (Au D ε t)) := by
    intro t
    have h1 : utNormSq D ε t ≤ C + 2 * normSq (Au D ε t) := by
      have h2 := utNormSq_le D ε t
      have h3 := normSq_f_le D hε0.le hε1 t
      rw [hCdef]; linarith
    have h4 : (0 : ℝ) ≤ 2 * normSq (Au D ε t) := by
      have := normSq_nonneg (Au D ε t); linarith
    calc ENNReal.ofReal (utNormSq D ε t)
        ≤ ENNReal.ofReal (C + 2 * normSq (Au D ε t)) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal C + ENNReal.ofReal (2 * normSq (Au D ε t)) :=
          ENNReal.ofReal_add hCnn h4
      _ = ENNReal.ofReal C + ENNReal.ofReal 2 * ENNReal.ofReal (normSq (Au D ε t)) := by
          congr 1
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hbound : (⊤ : ENNReal)
      ≤ ENNReal.ofReal C * MeasureTheory.volume (Set.Icc (0 : ℝ) 1)
        + ENNReal.ofReal 2 * ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (normSq (Au D ε t)) := by
    rw [← lintegral_utNormSq_eq_top D (ne_of_gt hε0)]
    calc ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (utNormSq D ε t)
        ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1,
            (ENNReal.ofReal C + ENNReal.ofReal 2 * ENNReal.ofReal (normSq (Au D ε t))) :=
          MeasureTheory.lintegral_mono hpt
      _ = _ := by
          rw [MeasureTheory.lintegral_add_left measurable_const,
            MeasureTheory.lintegral_const,
            MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            MeasureTheory.Measure.restrict_apply_univ]
  have hfin : ENNReal.ofReal C * MeasureTheory.volume (Set.Icc (0 : ℝ) 1)
      + ENNReal.ofReal 2 * (∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (normSq (Au D ε t)))
      ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop⟩
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  exact hfin (top_le_iff.mp hbound)

/-- `A_H(·)u(·) ∉ L²(0,1;H)`. -/
theorem not_integrableOn_normSq_Au {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ¬ MeasureTheory.IntegrableOn (fun t => normSq (Au D ε t)) (Set.Icc (0 : ℝ) 1) := by
  intro hint
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)]
      fun t => normSq (Au D ε t) :=
    Filter.Eventually.of_forall fun t => normSq_nonneg (Au D ε t)
  have hfin := (MeasureTheory.hasFiniteIntegral_iff_ofReal hnn).mp
    (MeasureTheory.Integrable.hasFiniteIntegral hint)
  rw [lintegral_normSq_Au_eq_top D hε0 hε1] at hfin
  exact (lt_irrefl _ hfin)

end LionsC12

end
