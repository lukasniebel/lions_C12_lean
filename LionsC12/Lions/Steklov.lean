module

public import Mathlib.MeasureTheory.Covering.OneDim
public import Mathlib.MeasureTheory.Covering.Differentiation
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Steklov averages

-/

@[expose] public section

noncomputable section

namespace LionsC12

open Real MeasureTheory Filter Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Steklov average `u_h(t) := (1/h) ∫_t^{t+h} u`. -/
noncomputable def steklov (h : ℝ) (u : ℝ → E) (t : ℝ) : E := (1 / h) • ∫ τ in t..(t + h), u τ

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- A locally integrable function is interval integrable on every interval. -/
theorem intervalIntegrable_of_locallyIntegrable {u : ℝ → E}
    (hu : MeasureTheory.LocallyIntegrable u) (a b : ℝ) :
    IntervalIntegrable u MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff]
  exact (hu.integrableOn_isCompact isCompact_uIcc).mono_set Set.Ioc_subset_Icc_self

omit [CompleteSpace E] in
omit [CompleteSpace E] in
theorem continuous_steklov (h : ℝ) {u : ℝ → E}
    (hu : MeasureTheory.LocallyIntegrable u) : Continuous (steklov h u) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable u MeasureTheory.volume a b :=
    intervalIntegrable_of_locallyIntegrable hu
  have hF : Continuous fun b : ℝ => ∫ x in (0 : ℝ)..b, u x :=
    intervalIntegral.continuous_primitive (fun a b => hint a b) 0
  have hrw : (steklov h u) =
      fun t => (1 / h) • ((∫ x in (0 : ℝ)..(t + h), u x) - ∫ x in (0 : ℝ)..t, u x) := by
    funext t
    unfold steklov
    congr 1
    rw [eq_sub_iff_add_eq, add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t (t + h))
  rw [hrw]
  exact ((hF.comp (continuous_id.add continuous_const)).sub hF).const_smul _

/-- Tonelli: integrating the "moving window" `Ioc t (t+h)` over `t` multiplies by `h`. -/
theorem lintegral_lintegral_Ioc_shift (h : ℝ) {F : ℝ → ENNReal}
    (hF : Measurable F) :
    ∫⁻ t, (∫⁻ τ in Set.Ioc t (t + h), F τ) = ENNReal.ofReal h * ∫⁻ τ, F τ := by
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | q.1 < q.2} ∩ {q : ℝ × ℝ | q.2 ≤ q.1 + h} with hSdef
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.add_const h))
  have hGm : Measurable (fun q : ℝ × ℝ => S.indicator (fun q : ℝ × ℝ => F q.2) q) :=
    (hF.comp measurable_snd).indicator hSm
  have hswap := MeasureTheory.lintegral_lintegral_swap
    (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
    (f := fun t τ => S.indicator (fun q : ℝ × ℝ => F q.2) (t, τ)) (by exact hGm.aemeasurable)
  have hleft : ∀ t : ℝ, (∫⁻ τ, S.indicator (fun q : ℝ × ℝ => F q.2) (t, τ))
      = ∫⁻ τ in Set.Ioc t (t + h), F τ := by
    intro t
    rw [← MeasureTheory.lintegral_indicator (measurableSet_Ioc) F]
    congr 1
  have hright : ∀ τ : ℝ, (∫⁻ t, S.indicator (fun q : ℝ × ℝ => F q.2) (t, τ))
      = F τ * ENNReal.ofReal h := by
    intro τ
    have heq : (fun t : ℝ => S.indicator (fun q : ℝ × ℝ => F q.2) (t, τ))
        = fun t : ℝ => Set.indicator (Set.Ico (τ - h) τ) (fun _ => F τ) t := by
      funext t
      simp only [hSdef, Set.indicator_apply, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ico]
      by_cases hc : t < τ ∧ τ ≤ t + h
      · rw [ite_eq_left hc, ite_eq_left ⟨by linarith [hc.2], hc.1⟩]
      · rw [ite_eq_right hc, ite_eq_right (fun hd => hc ⟨hd.2, by linarith [hd.1]⟩)]
    rw [heq, MeasureTheory.lintegral_indicator_const measurableSet_Ico]
    congr 1
    rw [Real.volume_Ico]
    congr 1
    ring
  simp only [hleft, hright] at hswap
  rw [hswap, MeasureTheory.lintegral_mul_const' _ _ (by simp), mul_comm]

omit [CompleteSpace E] in
private theorem eLpNorm_steklov_le_aux {h : ℝ} (hh : 0 < h) {u : ℝ → E}
    (hmeas : MeasureTheory.StronglyMeasurable u) (hloc : MeasureTheory.LocallyIntegrable u) :
    MeasureTheory.eLpNorm (steklov h u) 2 MeasureTheory.volume
      ≤ MeasureTheory.eLpNorm u 2 MeasureTheory.volume := by
  set F : ℝ → ENNReal := fun τ => ‖u τ‖ₑ ^ (2 : ℝ) with hFdef
  have hFm : Measurable F := hmeas.enorm.pow_const _
  have stepA : ∀ t : ℝ, ‖steklov h u t‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal (1 / h) * ∫⁻ τ in Set.Ioc t (t + h), F τ := by
    intro t
    have hle : t ≤ t + h := by linarith
    have hvol : MeasureTheory.volume (Set.Ioc t (t + h)) = ENNReal.ofReal h := by
      rw [Real.volume_Ioc]; congr 1; ring
    have e1 : ‖steklov h u t‖ₑ
        = ENNReal.ofReal (1 / h) * ‖∫ τ in Set.Ioc t (t + h), u τ‖ₑ := by
      unfold steklov
      rw [intervalIntegral.integral_of_le hle, enorm_smul]
      congr 1
      exact Real.enorm_eq_ofReal (by positivity)
    have e2 : ‖∫ τ in Set.Ioc t (t + h), u τ‖ₑ ≤ ∫⁻ τ in Set.Ioc t (t + h), ‖u τ‖ₑ :=
      MeasureTheory.enorm_integral_le_lintegral_enorm _
    have e3 : (∫⁻ τ in Set.Ioc t (t + h), ‖u τ‖ₑ)
        ≤ (∫⁻ τ in Set.Ioc t (t + h), F τ) ^ (1 / 2 : ℝ)
          * ENNReal.ofReal h ^ (1 / 2 : ℝ) := by
      have H := ENNReal.lintegral_mul_le_Lp_mul_Lq
        (MeasureTheory.volume.restrict (Set.Ioc t (t + h))) (Real.HolderConjugate.two_two)
        (f := fun τ => ‖u τ‖ₑ) (g := fun _ => (1 : ENNReal))
        hmeas.enorm.aemeasurable aemeasurable_const
      simpa [hFdef, hvol] using H
    have hX : ‖steklov h u t‖ₑ ≤ ENNReal.ofReal (1 / h)
        * ((∫⁻ τ in Set.Ioc t (t + h), F τ) ^ (1 / 2 : ℝ) * ENNReal.ofReal h ^ (1 / 2 : ℝ)) := by
      rw [e1]; gcongr; exact e2.trans e3
    calc ‖steklov h u t‖ₑ ^ (2 : ℝ)
        ≤ (ENNReal.ofReal (1 / h)
            * ((∫⁻ τ in Set.Ioc t (t + h), F τ) ^ (1 / 2 : ℝ)
              * ENNReal.ofReal h ^ (1 / 2 : ℝ))) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hX (by norm_num)
      _ = ENNReal.ofReal (1 / h) ^ (2 : ℝ) * ENNReal.ofReal h
            * ∫⁻ τ in Set.Ioc t (t + h), F τ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          norm_num
          ring
      _ = ENNReal.ofReal (1 / h) * ∫⁻ τ in Set.Ioc t (t + h), F τ := by
          congr 1
          rw [ENNReal.ofReal_rpow_of_pos (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show ((1:ℝ)/h) ^ (2:ℝ) = (1/h)^(2:ℕ) by
            rw [← Real.rpow_natCast (1/h) 2]; norm_num]
          field_simp
  have main : (∫⁻ t, ‖steklov h u t‖ₑ ^ (2 : ℝ)) ≤ ∫⁻ t, ‖u t‖ₑ ^ (2 : ℝ) := by
    calc (∫⁻ t, ‖steklov h u t‖ₑ ^ (2 : ℝ))
        ≤ ∫⁻ t, ENNReal.ofReal (1 / h) * ∫⁻ τ in Set.Ioc t (t + h), F τ :=
          MeasureTheory.lintegral_mono stepA
      _ = ENNReal.ofReal (1 / h) * ∫⁻ t, ∫⁻ τ in Set.Ioc t (t + h), F τ :=
          MeasureTheory.lintegral_const_mul' _ _ (by simp)
      _ = ENNReal.ofReal (1 / h) * (ENNReal.ofReal h * ∫⁻ τ, F τ) := by
          rw [lintegral_lintegral_Ioc_shift h hFm]
      _ = ∫⁻ t, ‖u t‖ₑ ^ (2 : ℝ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          rw [show (1 / h) * h = 1 by field_simp]
          simp [hFdef]
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (continuous_steklov h hloc).aestronglyMeasurable,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hmeas.aestronglyMeasurable]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  simpa using main

omit [CompleteSpace E] in
/-- `L²`-contraction: `‖u_h‖_{L²(ℝ)} ≤ ‖u‖_{L²(ℝ)}`. -/
theorem eLpNorm_steklov_le {h : ℝ} (hh : 0 < h) {u : ℝ → E} (hu : MeasureTheory.MemLp u 2) :
    MeasureTheory.eLpNorm (steklov h u) 2 MeasureTheory.volume
      ≤ MeasureTheory.eLpNorm u 2 MeasureTheory.volume := by
  have hmk := hu.aestronglyMeasurable.stronglyMeasurable_mk
  have hae := hu.aestronglyMeasurable.ae_eq_mk
  have hloc : MeasureTheory.LocallyIntegrable (hu.aestronglyMeasurable.mk u) :=
    ((hu.ae_eq hae).locallyIntegrable one_le_two)
  have h1 : steklov h u = steklov h (hu.aestronglyMeasurable.mk u) := by
    funext t
    unfold steklov
    congr 1
    exact intervalIntegral.integral_congr_ae (by filter_upwards [hae] with x hx using fun _ => hx)
  rw [h1]
  exact le_trans (eLpNorm_steklov_le_aux hh hmk hloc)
    (le_of_eq (MeasureTheory.eLpNorm_congr_ae hae).symm)

omit [CompleteSpace E] in
theorem memLp_steklov {h : ℝ} (hh : 0 < h) {u : ℝ → E} (hu : MeasureTheory.MemLp u 2) :
    MeasureTheory.MemLp (steklov h u) 2 := by
  have hloc : MeasureTheory.LocallyIntegrable u := hu.locallyIntegrable one_le_two
  exact lt_of_le_of_lt (eLpNorm_steklov_le hh hu) hu

/-- Uniform convergence for continuous compactly supported `u`. -/
theorem tendstoUniformly_steklov {u : ℝ → E} (hu : Continuous u) (hs : HasCompactSupport u) :
    TendstoUniformly (fun h => steklov h u) u (nhdsWithin 0 (Set.Ioi 0)) := by
  have huc : UniformContinuous u := hs.uniformContinuous_of_continuous hu
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.1 huc (ε / 2) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ] with h hmem t
  obtain ⟨hh0, hhδ⟩ := hmem
  have hbd : ∀ x ∈ Set.uIoc t (t + h), ‖u x - u t‖ ≤ ε / 2 := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have : dist x t < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith [hx.1])]
      linarith [hx.2]
    have := hδ' this
    rw [dist_eq_norm] at this
    exact this.le
  have hcst : (∫ τ in t..(t + h), u t) = h • u t := by
    rw [intervalIntegral.integral_const]
    congr 1
    ring
  have hdiff : steklov h u t - u t = (1 / h) • ∫ τ in t..(t + h), (u τ - u t) := by
    rw [intervalIntegral.integral_sub (hu.intervalIntegrable _ _)
      (intervalIntegrable_const), hcst]
    unfold steklov
    rw [smul_sub, smul_smul]
    congr 1
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hh0), one_smul]
  have hnorm : ‖∫ τ in t..(t + h), (u τ - u t)‖ ≤ ε / 2 * |t + h - t| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [dist_comm, dist_eq_norm, hdiff, norm_smul]
  have h1 : ‖(1 / h : ℝ)‖ = 1 / h := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h1]
  have h2 : |t + h - t| = h := by
    rw [show t + h - t = h by ring, abs_of_pos hh0]
  rw [h2] at hnorm
  calc 1 / h * ‖∫ τ in t..(t + h), (u τ - u t)‖ ≤ 1 / h * (ε / 2 * h) := by
        exact mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

omit [CompleteSpace E] in
/-- Linearity of the Steklov average in the function. -/
theorem steklov_sub {h : ℝ} {u v : ℝ → E} (hu : MeasureTheory.LocallyIntegrable u)
    (hv : MeasureTheory.LocallyIntegrable v) (t : ℝ) :
    steklov h u t - steklov h v t = steklov h (fun τ => u τ - v τ) t := by
  unfold steklov
  rw [← smul_sub, intervalIntegral.integral_sub (intervalIntegrable_of_locallyIntegrable hu _ _)
    (intervalIntegrable_of_locallyIntegrable hv _ _)]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- `L²` bound for a function supported in `A` and bounded by `δ`. -/
theorem eLpNorm_le_of_support_of_bound {f : ℝ → E} {A : Set ℝ} (hA : MeasurableSet A) {δ : ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) (hδ : 0 ≤ δ)
    (hsupp : ∀ t, t ∉ A → f t = 0) (hbd : ∀ t, ‖f t‖ ≤ δ) :
    MeasureTheory.eLpNorm f 2 MeasureTheory.volume
      ≤ ENNReal.ofReal δ * (MeasureTheory.volume A) ^ (1 / 2 : ℝ) := by
  have h1 : MeasureTheory.eLpNorm f 2 MeasureTheory.volume
      ≤ MeasureTheory.eLpNorm (A.indicator (fun _ => δ)) 2 MeasureTheory.volume := by
    refine MeasureTheory.eLpNorm_mono_enorm hfm (fun t => ?_)
    by_cases ht : t ∈ A
    · rw [Set.indicator_of_mem ht, Real.enorm_eq_ofReal hδ, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hbd t)
    · rw [hsupp t ht, Set.indicator_of_notMem ht]
      simp
  refine h1.trans (le_of_eq ?_)
  rw [MeasureTheory.eLpNorm_indicator_const hA.nullMeasurableSet (by norm_num) (by norm_num),
    Real.enorm_eq_ofReal hδ]
  norm_num

/-- `L²`-convergence `u_h → u` as `h → 0⁺`, for `u ∈ L²(ℝ;E)`. -/
theorem tendsto_eLpNorm_steklov_sub {u : ℝ → E} (hu : MeasureTheory.MemLp u 2) :
    Filter.Tendsto
      (fun h => MeasureTheory.eLpNorm (fun t => steklov h u t - u t) 2 MeasureTheory.volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact Filter.Eventually.of_forall fun h => le_top
  have hε3 : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' (by norm_num)).ne'
  have hε3top : ε / 3 ≠ ⊤ := by
    simp [ENNReal.div_eq_top, hεtop]
  obtain ⟨v, hvsupp, hvle, hvcont, hvmem⟩ :=
    hu.exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by norm_num) hε3
  have hloc : MeasureTheory.LocallyIntegrable u := hu.locallyIntegrable one_le_two
  have hvloc : MeasureTheory.LocallyIntegrable v := hvcont.locallyIntegrable
  have huv : MeasureTheory.MemLp (fun t => u t - v t) 2 MeasureTheory.volume := hu.sub hvmem
  have huvloc : MeasureTheory.LocallyIntegrable (fun t => u t - v t) := hloc.sub hvloc
  -- a compact interval containing the support of `v`
  obtain ⟨R₀, hR₀⟩ := (hvsupp.isCompact.isBounded).subset_closedBall (0 : ℝ)
  set R : ℝ := max R₀ 1 with hRdef
  have hR1 : (1 : ℝ) ≤ R := le_max_right _ _
  have hvzero : ∀ x : ℝ, x ∉ Set.Icc (-R) R → v x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport (fun hc => hx ?_)
    have hb := hR₀ hc
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hb
    have hb' : |x| ≤ R := hb.trans (le_max_left R₀ 1)
    exact Set.mem_Icc.2 (abs_le.1 hb')
  set A : Set ℝ := Set.Icc (-R - 1) R with hAdef
  have hAmeas : MeasurableSet A := measurableSet_Icc
  set L : ℝ := 2 * R + 1 with hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  have hvolA : MeasureTheory.volume A = ENNReal.ofReal L := by
    rw [hAdef, Real.volume_Icc]
    congr 1
    rw [hLdef]; ring
  have hArpow : (MeasureTheory.volume A) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt L) := by
    rw [hvolA, ENNReal.ofReal_rpow_of_pos hLpos, ← Real.sqrt_eq_rpow]
  set ε₃ : ℝ := (ε / 3).toReal with hε₃def
  have hε₃pos : 0 < ε₃ := ENNReal.toReal_pos hε3 hε3top
  have hsqrtpos : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  set δ : ℝ := ε₃ / (2 * Real.sqrt L) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have huniform := tendstoUniformly_steklov hvcont hvsupp
  rw [Metric.tendstoUniformly_iff] at huniform
  filter_upwards [huniform δ hδpos, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with h hunif hmem
  have hh0 : 0 < h := hmem.1
  have hh1 : h ≤ 1 := hmem.2.le
  -- the middle term vanishes outside `A`
  have hBsupp : ∀ t, t ∉ A → steklov h v t - v t = 0 := by
    intro t ht
    have hv0 : v t = 0 := by
      refine hvzero t (fun hc => ht ?_)
      have h1 := hc.1
      have h2 := hc.2
      exact Set.mem_Icc.2 ⟨by rw [hAdef] at *; linarith, by linarith⟩
    have hst : steklov h v t = 0 := by
      unfold steklov
      have hz : (∫ τ in t..(t + h), v τ) = 0 := by
        have : (∫ τ in t..(t + h), v τ) = ∫ _τ in t..(t + h), (0 : E) := by
          refine intervalIntegral.integral_congr (fun τ hτ => ?_)
          rw [Set.uIcc_of_le (by linarith)] at hτ
          refine hvzero τ (fun hc => ht ?_)
          have h1 := hc.1
          have h2 := hc.2
          have h3 := hτ.1
          have h4 := hτ.2
          exact Set.mem_Icc.2 ⟨by linarith, by linarith⟩
        rw [this]
        simp
      rw [hz, smul_zero]
    rw [hst, hv0, sub_zero]
  have hBbd : ∀ t, ‖steklov h v t - v t‖ ≤ δ := by
    intro t
    have := hunif t
    rw [dist_comm, dist_eq_norm] at this
    exact this.le
  have hB : MeasureTheory.eLpNorm (fun t => steklov h v t - v t) 2 MeasureTheory.volume
      ≤ ε / 3 := by
    refine (eLpNorm_le_of_support_of_bound hAmeas
      ((continuous_steklov h hvloc).sub hvcont).aestronglyMeasurable hδpos.le hBsupp hBbd).trans ?_
    rw [hArpow, ← ENNReal.ofReal_mul hδpos.le]
    have : δ * Real.sqrt L = ε₃ / 2 := by
      rw [hδdef]
      field_simp
    rw [this, ← ENNReal.ofReal_toReal hε3top, ← hε₃def]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- decomposition
  have hdecomp : (fun t => steklov h u t - u t)
      = (fun t => steklov h (fun τ => u τ - v τ) t) + (fun t => steklov h v t - v t)
        + (fun t => v t - u t) := by
    funext t
    simp only [Pi.add_apply]
    rw [← steklov_sub hloc hvloc t]
    abel
  have hm1 : MeasureTheory.AEStronglyMeasurable
      (fun t => steklov h (fun τ => u τ - v τ) t) MeasureTheory.volume :=
    (continuous_steklov h huvloc).aestronglyMeasurable
  have hm2 : MeasureTheory.AEStronglyMeasurable
      (fun t => steklov h v t - v t) MeasureTheory.volume :=
    ((continuous_steklov h hvloc).sub hvcont).aestronglyMeasurable
  have hm3 : MeasureTheory.AEStronglyMeasurable (fun t => v t - u t) MeasureTheory.volume :=
    (hvmem.sub hu).aestronglyMeasurable
  have hA1 : MeasureTheory.eLpNorm (fun t => steklov h (fun τ => u τ - v τ) t) 2
      MeasureTheory.volume ≤ ε / 3 :=
    (eLpNorm_steklov_le hh0 huv).trans hvle
  have hA3 : MeasureTheory.eLpNorm (fun t => v t - u t) 2 MeasureTheory.volume ≤ ε / 3 := by
    have : (fun t => v t - u t) = -(fun t => u t - v t) := by
      funext t; simp
    rw [this, MeasureTheory.eLpNorm_neg]
    exact hvle
  have hsum : ε / 3 + ε / 3 + ε / 3 = ε := by
    rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, show ε + ε + ε = ε * 3 by ring]
    exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  rw [hdecomp]
  calc MeasureTheory.eLpNorm ((fun t => steklov h (fun τ => u τ - v τ) t)
          + (fun t => steklov h v t - v t) + (fun t => v t - u t)) 2 MeasureTheory.volume
      ≤ MeasureTheory.eLpNorm ((fun t => steklov h (fun τ => u τ - v τ) t)
          + (fun t => steklov h v t - v t)) 2 MeasureTheory.volume
        + MeasureTheory.eLpNorm (fun t => v t - u t) 2 MeasureTheory.volume :=
        MeasureTheory.eLpNorm_add_le one_le_two
    _ ≤ (MeasureTheory.eLpNorm (fun t => steklov h (fun τ => u τ - v τ) t) 2 MeasureTheory.volume
        + MeasureTheory.eLpNorm (fun t => steklov h v t - v t) 2 MeasureTheory.volume)
        + MeasureTheory.eLpNorm (fun t => v t - u t) 2 MeasureTheory.volume := by
        gcongr
        exact MeasureTheory.eLpNorm_add_le one_le_two
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := hsum

/-- Steklov average of an indefinite integral: `(∫₀^· g)_h` is `C¹` with derivative `g_h`. -/
theorem hasDerivAt_steklov_integral (h : ℝ) {g : ℝ → E}
    (hg : MeasureTheory.LocallyIntegrable g) (t : ℝ) :
    HasDerivAt (steklov h (fun τ => ∫ σ in (0 : ℝ)..τ, g σ)) (steklov h g t) t := by
  have hint : ∀ a b : ℝ, IntervalIntegrable g MeasureTheory.volume a b :=
    intervalIntegrable_of_locallyIntegrable hg
  set G : ℝ → E := fun τ => ∫ σ in (0 : ℝ)..τ, g σ with hGdef
  have hGc : Continuous G := intervalIntegral.continuous_primitive (fun a b => hint a b) 0
  have hGint : ∀ a b : ℝ, IntervalIntegrable G MeasureTheory.volume a b := fun a b =>
    hGc.intervalIntegrable a b
  have hH : ∀ s : ℝ, HasDerivAt (fun s => ∫ σ in (0 : ℝ)..s, G σ) (G s) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (hGint 0 s)
      (hGc.stronglyMeasurableAtFilter _ _) hGc.continuousAt
  have hrw : (steklov h G) =
      fun t => (1 / h) • ((∫ σ in (0 : ℝ)..(t + h), G σ) - ∫ σ in (0 : ℝ)..t, G σ) := by
    funext t
    unfold steklov
    congr 1
    rw [eq_sub_iff_add_eq, add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals (hGint 0 t) (hGint t (t + h))
  rw [hrw]
  have d1 : HasDerivAt (fun t : ℝ => ∫ σ in (0 : ℝ)..(t + h), G σ) (G (t + h)) t :=
    HasDerivAt.comp_add_const t h (hH (t + h))
  have d : HasDerivAt
      (fun t : ℝ => (1 / h) • ((∫ σ in (0 : ℝ)..(t + h), G σ) - ∫ σ in (0 : ℝ)..t, G σ))
      ((1 / h) • (G (t + h) - G t)) t := (d1.sub (hH t)).const_smul (1 / h : ℝ)
  have hval : steklov h g t = (1 / h) • (G (t + h) - G t) := by
    unfold steklov
    congr 1
    rw [hGdef]
    simp only
    rw [eq_sub_iff_add_eq, add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t (t + h))
  rw [hval]
  exact d

end LionsC12

end
