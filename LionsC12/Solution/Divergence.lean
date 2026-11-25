module

public import LionsC12.Construction.Defs
public import LionsC12.Coefficient.Blocks
public import LionsC12.Coefficient.Support
public import LionsC12.Modes.Trig
public import LionsC12.Solution.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Lemma 4.1: the time derivative is not square integrable

This file contains the last part of the proof of Lemma 4.1 of the paper:
`∂_t u ∉ L²(0,1;H)`.

On the middle third `J_j = [τ_j + ℓ_j/3, τ_j + 2ℓ_j/3]` of the `j`-th block we have
`ρ' = 0`, `η_j = 1` and `η_j' = 0`, so that (equation (4.6))
`∂_t u(t) = -(ε/2) ∑_{m=1}^{M_j} (cos θ_{j,m}(t) + sin θ_{j,m}(t)) p_{K_{j,m}}`.
Since the modes `p_{K_{j,m}}` are pairwise orthogonal with `‖p_K‖²_H = π/4`, Pythagoras gives
`‖∂_t u(t)‖²_H = (π ε²/16) ∑_m (cos θ_{j,m}(t) + sin θ_{j,m}(t))²`.
Using `(cos θ + sin θ)² = 1 + sin(2θ)` and the explicit antiderivative of
`t ↦ sin (2 K²(t - τ_j))` one gets `∫_{J_j} (cos θ + sin θ)² ≥ ℓ_j/3 - K⁻² ≥ ℓ_j/6`,
whence `∫_{J_j} ‖∂_t u‖²_H ≥ (π ε²/96) M_j ℓ_j = π ε²/(1536 (j+1))`.
Summing over the pairwise disjoint blocks and using the divergence of `∑ 1/(j+1)`
yields the claim.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ### Elementary continuity facts -/

private lemma continuous_cs (j m : ℕ) :
    Continuous fun t : ℝ => (cos (θ j m t) + sin (θ j m t)) ^ 2 := by
  have hθ := continuous_θ j m
  have h : Continuous fun t : ℝ => cos (θ j m t) + sin (θ j m t) :=
    (Real.continuous_cos.comp' hθ).add (Real.continuous_sin.comp' hθ)
  exact (continuous_pow 2).comp' h

/-! ### Pythagoras on the middle third -/

/-- Pythagoras on `J_j`: `‖∂_t u(t)‖²_H = (π ε²/16) ∑_m (cos θ_m(t) + sin θ_m(t))²`. -/
theorem utNormSq_on_J (ε : ℝ) {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ J j) :
    utNormSq D ε t
      = π * ε ^ 2 / 16 * ∑ m ∈ Finset.Icc 1 (M j), (cos (θ j m t) + sin (θ j m t)) ^ 2 := by
  have hfun : ut D ε t = fun x => ∑ m ∈ Finset.Icc 1 (M j),
      (-(ε / 2) * (cos (θ j m t) + sin (θ j m t))) * p (K j m) x := by
    funext x
    exact ut_on_J D ε hj ht x
  have hK : ∀ m ∈ Finset.Icc 1 (M j), 2 < K j m := by
    intro m hm
    exact two_lt_K hj (Finset.mem_Icc.mp hm).1
  have hsep : ∀ m ∈ Finset.Icc 1 (M j), ∀ m' ∈ Finset.Icc 1 (M j), m < m' →
      K j m + 4 < K j m' := by
    intro m hm m' _ hmm'
    have h1 : 16 * K j m ≤ K j m' := K_le_of_lt hmm'
    have h2 : 2 < K j m := two_lt_K hj (Finset.mem_Icc.mp hm).1
    omega
  have key : normSq (ut D ε t)
      = π / 4 * ∑ m ∈ Finset.Icc 1 (M j),
          (-(ε / 2) * (cos (θ j m t) + sin (θ j m t))) ^ 2 := by
    rw [hfun]
    exact normSq_sum_p (Finset.Icc 1 (M j)) (K j)
      (fun m => -(ε / 2) * (cos (θ j m t) + sin (θ j m t))) hK hsep
  show normSq (ut D ε t) = _
  rw [key, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

/-! ### The lower bound for one mode on the middle third -/

/-- `∫_{J_j} (cos θ + sin θ)² dt ≥ ℓ_j/6` (uses `(cos θ+sin θ)² = 1 + sin 2θ`
and `K² ℓ_j ≥ 6`). -/
theorem integral_J_lower {j : ℕ} (hj : 1 ≤ j) {m : ℕ} (hm : 1 ≤ m) :
    ℓ j / 6 ≤ ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3),
      (cos (θ j m t) + sin (θ j m t)) ^ 2 := by
  have hℓ : 0 < ℓ j := ℓ_pos hj
  have hKn : 0 < K j m := K_pos hj
  have hKpos : (0 : ℝ) < (K j m : ℝ) := by exact_mod_cast hKn
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 2 * (K j m : ℝ) ^ 2 := ⟨_, rfl⟩
  have hcpos : 0 < c := by
    rw [hcdef]
    have hsq : (0 : ℝ) < (K j m : ℝ) ^ 2 := pow_pos hKpos 2
    linarith
  have hcne : c ≠ 0 := ne_of_gt hcpos
  -- the pointwise identity `(cos θ + sin θ)² = 1 + sin (2θ)`
  have hid : ∀ t : ℝ, (cos (θ j m t) + sin (θ j m t)) ^ 2 = 1 + sin (c * (t - τ j)) := by
    intro t
    have hθt : θ j m t = (K j m : ℝ) ^ 2 * (t - τ j) := rfl
    have h1 : c * (t - τ j) = 2 * θ j m t := by rw [hcdef, hθt]; ring
    rw [h1, Real.sin_two_mul]
    linear_combination Real.sin_sq_add_cos_sq (θ j m t)
  have hcont : Continuous fun t : ℝ => sin (c * (t - τ j)) :=
    Real.continuous_sin.comp' (continuous_const.mul (continuous_id.sub continuous_const))
  -- the antiderivative of `t ↦ sin (c (t - τ j))`
  have hF : ∀ t ∈ Set.uIcc (τ j + ℓ j / 3) (τ j + 2 * ℓ j / 3),
      HasDerivAt (fun s : ℝ => -(1 / c) * cos (c * (s - τ j))) (sin (c * (t - τ j))) t := by
    intro t _
    have h0 : HasDerivAt (fun s : ℝ => s - τ j) 1 t := (hasDerivAt_id t).sub_const (τ j)
    have h1 : HasDerivAt (fun s : ℝ => c * (s - τ j)) c t := by
      simpa using h0.const_mul c
    have h2 : HasDerivAt (fun s : ℝ => -(1 / c) * cos (c * (s - τ j)))
        (-(1 / c) * (-sin (c * (t - τ j)) * c)) t := h1.cos.const_mul (-(1 / c))
    have h3 : -(1 / c) * (-sin (c * (t - τ j)) * c) = sin (c * (t - τ j)) := by
      have hcc : c / c = 1 := div_self hcne
      linear_combination sin (c * (t - τ j)) * hcc
    rwa [h3] at h2
  have hsin : ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), sin (c * (t - τ j))
      = -(1 / c) * cos (c * (τ j + 2 * ℓ j / 3 - τ j))
        - -(1 / c) * cos (c * (τ j + ℓ j / 3 - τ j)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable _ _)
  have hval : ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), (cos (θ j m t) + sin (θ j m t)) ^ 2
      = (τ j + 2 * ℓ j / 3 - (τ j + ℓ j / 3))
        + (-(1 / c) * cos (c * (τ j + 2 * ℓ j / 3 - τ j))
            - -(1 / c) * cos (c * (τ j + ℓ j / 3 - τ j))) := by
    have h1 : ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), (cos (θ j m t) + sin (θ j m t)) ^ 2
        = ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), ((1 : ℝ) + sin (c * (t - τ j))) :=
      intervalIntegral.integral_congr fun t _ => hid t
    rw [h1, intervalIntegral.integral_add intervalIntegrable_const
      (hcont.intervalIntegrable _ _), intervalIntegral.integral_const, hsin]
    simp only [smul_eq_mul, mul_one]
  rw [hval]
  -- the quantitative bound
  have h6 : (6 : ℝ) ≤ (K j m : ℝ) ^ 2 * ℓ j := six_le_K_sq_mul_ℓ hj hm
  have hcℓ : 12 ≤ c * ℓ j := by
    have hx : c * ℓ j = 2 * ((K j m : ℝ) ^ 2 * ℓ j) := by rw [hcdef]; ring
    rw [hx]; linarith
  have hu : 12 * (1 / c) ≤ ℓ j := by
    rw [mul_one_div]
    exact (div_le_iff₀ hcpos).mpr (by nlinarith)
  have hu0 : (0 : ℝ) ≤ 1 / c := le_of_lt (one_div_pos.mpr hcpos)
  have hbound : -(2 * (1 / c)) ≤ -(1 / c) * cos (c * (τ j + 2 * ℓ j / 3 - τ j))
      - -(1 / c) * cos (c * (τ j + ℓ j / 3 - τ j)) := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr (Real.cos_le_one (c * (τ j + 2 * ℓ j / 3 - τ j)))),
      mul_nonneg hu0 (by linarith [Real.neg_one_le_cos (c * (τ j + ℓ j / 3 - τ j))] :
        (0 : ℝ) ≤ cos (c * (τ j + ℓ j / 3 - τ j)) + 1)]
  linarith

/-! ### Continuity and the integral of `‖∂_t u‖²_H` on the middle third -/

theorem continuousOn_utNormSq_J (ε : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    ContinuousOn (utNormSq D ε) (J j) := by
  have hc : Continuous fun t : ℝ => π * ε ^ 2 / 16 *
      ∑ m ∈ Finset.Icc 1 (M j), (cos (θ j m t) + sin (θ j m t)) ^ 2 :=
    continuous_const.mul (continuous_finsetSum _ fun m _ => continuous_cs j m)
  exact hc.continuousOn.congr fun t ht => utNormSq_on_J D ε hj ht

/-- `∫_{J_j} ‖∂_t u‖²_H dt ≥ π ε² / (1536 (j+1))`. -/
theorem integral_utNormSq_J (ε : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    π * ε ^ 2 / (1536 * ((j : ℝ) + 1)) ≤
      ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), utNormSq D ε t := by
  have hℓ : 0 < ℓ j := ℓ_pos hj
  have hab : τ j + ℓ j / 3 ≤ τ j + 2 * ℓ j / 3 := by linarith
  have hcongr : ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), utNormSq D ε t
      = ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3),
          π * ε ^ 2 / 16 * ∑ m ∈ Finset.Icc 1 (M j), (cos (θ j m t) + sin (θ j m t)) ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hab] at ht
    exact utNormSq_on_J D ε hj ht
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hintsum : ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3),
        ∑ m ∈ Finset.Icc 1 (M j), (cos (θ j m t) + sin (θ j m t)) ^ 2
      = ∑ m ∈ Finset.Icc 1 (M j), ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3),
          (cos (θ j m t) + sin (θ j m t)) ^ 2 :=
    intervalIntegral.integral_finsetSum fun m _ => (continuous_cs j m).intervalIntegrable _ _
  rw [hintsum]
  have hconst : ∑ _m ∈ Finset.Icc 1 (M j), ℓ j / 6 = (M j : ℝ) * (ℓ j / 6) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    norm_num
  have hlow : (M j : ℝ) * (ℓ j / 6) ≤ ∑ m ∈ Finset.Icc 1 (M j),
      ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), (cos (θ j m t) + sin (θ j m t)) ^ 2 := by
    rw [← hconst]
    exact Finset.sum_le_sum fun m hm => integral_J_lower hj (Finset.mem_Icc.mp hm).1
  have hcoef : (0 : ℝ) ≤ π * ε ^ 2 / 16 := by positivity
  have hMℓ : (M j : ℝ) * ℓ j = 1 / (16 * ((j : ℝ) + 1)) := M_mul_ℓ hj
  have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hrewrite : π * ε ^ 2 / (1536 * ((j : ℝ) + 1))
      = π * ε ^ 2 / 16 * ((M j : ℝ) * (ℓ j / 6)) := by
    have h1 : π * ε ^ 2 / 16 * ((M j : ℝ) * (ℓ j / 6))
        = π * ε ^ 2 / 96 * ((M j : ℝ) * ℓ j) := by ring
    rw [h1, hMℓ, mul_one_div, div_div]
    ring
  rw [hrewrite]
  exact mul_le_mul_of_nonneg_left hlow hcoef

/-! ### Divergence -/

/-- The time derivative is not square integrable: the lower Lebesgue integral of
`‖∂_t u(t)‖²_H` over `[0,1]` is infinite. -/
theorem lintegral_utNormSq_eq_top {ε : ℝ} (hε : ε ≠ 0) :
    ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (utNormSq D ε t) = ⊤ := by
  by_contra htop
  have hεsq : (0 : ℝ) < ε ^ 2 := lt_of_le_of_ne (sq_nonneg ε) (Ne.symm (pow_ne_zero 2 hε))
  have hcpos : (0 : ℝ) < π * ε ^ 2 / 1536 :=
    div_pos (mul_pos Real.pi_pos hεsq) (by norm_num)
  -- the key lower bound, for every `N`
  have key : ∀ N : ℕ,
      ENNReal.ofReal (∑ i ∈ Finset.Icc 1 N, π * ε ^ 2 / (1536 * ((i : ℝ) + 1)))
        ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (utNormSq D ε t) := by
    intro N
    have hsub : (⋃ i ∈ Finset.Icc 1 N, J i) ⊆ Set.Icc (0 : ℝ) 1 := by
      intro t ht
      simp only [Set.mem_iUnion, exists_prop] at ht
      obtain ⟨i, hi, hti⟩ := ht
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hmem := I_subset hi1 (J_subset_I hi1 hti)
      simp only [Set.mem_Icc] at hmem ⊢
      constructor <;> linarith [hmem.1, hmem.2]
    have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 N) : Set ℕ) J := by
      intro i hi i' hi' hne
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp (Finset.mem_coe.mp hi)).1
      have hi1' : 1 ≤ i' := (Finset.mem_Icc.mp (Finset.mem_coe.mp hi')).1
      exact Disjoint.mono (J_subset_I hi1) (J_subset_I hi1') (I_disjoint hne)
    have hmeas : ∀ i ∈ Finset.Icc 1 N, MeasurableSet (J i) := fun i _ => measurableSet_Icc
    have hstep : ∀ i ∈ Finset.Icc 1 N,
        ENNReal.ofReal (π * ε ^ 2 / (1536 * ((i : ℝ) + 1)))
          ≤ ∫⁻ t in J i, ENNReal.ofReal (utNormSq D ε t) := by
      intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hℓ : 0 < ℓ i := ℓ_pos hi1
      have hab : τ i + ℓ i / 3 ≤ τ i + 2 * ℓ i / 3 := by linarith
      have hJ : J i = Set.Icc (τ i + ℓ i / 3) (τ i + 2 * ℓ i / 3) := rfl
      have hcontJ : ContinuousOn (utNormSq D ε) (Set.Icc (τ i + ℓ i / 3) (τ i + 2 * ℓ i / 3)) := by
        rw [← hJ]; exact continuousOn_utNormSq_J D ε hi1
      have hint : MeasureTheory.IntegrableOn (utNormSq D ε)
          (Set.Icc (τ i + ℓ i / 3) (τ i + 2 * ℓ i / 3)) :=
        ContinuousOn.integrableOn_Icc hcontJ
      have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict
          (Set.Icc (τ i + ℓ i / 3) (τ i + 2 * ℓ i / 3))] utNormSq D ε :=
        Filter.Eventually.of_forall fun t => normSq_nonneg (ut D ε t)
      have heq : ENNReal.ofReal (∫ t in Set.Icc (τ i + ℓ i / 3) (τ i + 2 * ℓ i / 3), utNormSq D ε t)
          = ∫⁻ t in Set.Icc (τ i + ℓ i / 3) (τ i + 2 * ℓ i / 3),
              ENNReal.ofReal (utNormSq D ε t) :=
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn
      rw [hJ, ← heq]
      refine ENNReal.ofReal_le_ofReal ?_
      have hIcc : ∫ t in Set.Icc (τ i + ℓ i / 3) (τ i + 2 * ℓ i / 3), utNormSq D ε t
          = ∫ t in (τ i + ℓ i / 3)..(τ i + 2 * ℓ i / 3), utNormSq D ε t := by
        rw [intervalIntegral.integral_of_le hab]
        exact MeasureTheory.integral_Icc_eq_integral_Ioc
      rw [hIcc]
      exact integral_utNormSq_J D ε hi1
    calc ENNReal.ofReal (∑ i ∈ Finset.Icc 1 N, π * ε ^ 2 / (1536 * ((i : ℝ) + 1)))
        = ∑ i ∈ Finset.Icc 1 N, ENNReal.ofReal (π * ε ^ 2 / (1536 * ((i : ℝ) + 1))) :=
          ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity
      _ ≤ ∑ i ∈ Finset.Icc 1 N, ∫⁻ t in J i, ENNReal.ofReal (utNormSq D ε t) :=
          Finset.sum_le_sum hstep
      _ = ∫⁻ t in (⋃ i ∈ Finset.Icc 1 N, J i), ENNReal.ofReal (utNormSq D ε t) :=
          (MeasureTheory.lintegral_biUnion_finset hdisj hmeas _).symm
      _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (utNormSq D ε t) :=
          MeasureTheory.lintegral_mono_set hsub
  -- divergence of the harmonic series contradicts finiteness of the integral
  obtain ⟨N, hN⟩ := exists_sum_inv_succ_gt
    ((∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (utNormSq D ε t)).toReal / (π * ε ^ 2 / 1536))
  have hsum_eq : ∑ i ∈ Finset.Icc 1 N, π * ε ^ 2 / (1536 * ((i : ℝ) + 1))
      = (π * ε ^ 2 / 1536) * ∑ i ∈ Finset.Icc 1 N, (1 : ℝ) / ((i : ℝ) + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_one_div, div_div]
  have hle := (ENNReal.ofReal_le_iff_le_toReal htop).mp (key N)
  rw [hsum_eq] at hle
  rw [div_lt_iff₀ hcpos] at hN
  linarith

theorem not_integrableOn_utNormSq {ε : ℝ} (hε : ε ≠ 0) :
    ¬ MeasureTheory.IntegrableOn (utNormSq D ε) (Set.Icc (0 : ℝ) 1) := by
  intro hint
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)] utNormSq D ε :=
    Filter.Eventually.of_forall fun t => normSq_nonneg (ut D ε t)
  have hfin := (MeasureTheory.hasFiniteIntegral_iff_ofReal hnn).mp
    (MeasureTheory.Integrable.hasFiniteIntegral hint)
  rw [lintegral_utNormSq_eq_top D hε] at hfin
  exact (lt_irrefl _ hfin)

end LionsC12

end
