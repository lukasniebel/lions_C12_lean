module

public import LionsC12.Domains.Equation
public import LionsC12.Construction.Cutoffs

/-!
# The clauses of Corollary 1.2 for the construction on a domain

For the construction of `LionsC12.Domains.Equation` (parameters `P : DomParams n Ω`):

* the coefficient: bounds `479/480 ≤ 𝔟 ≤ 481/480` (`dB_bounds`), the `L^∞`-bounds
  `‖𝔅(t) - Id‖ ≤ ε/480` and `‖𝔅(t) - 𝔅(s)‖ ≤ 2εC_β r⁻¹ |t-s|^{1/2}` in operator norm
  (`eLpNorm_isoCoeff_sub_id_le`, `eLpNorm_isoCoeff_sub_le`), and the failure of every Hölder
  exponent `α > 1/2` (`not_holder_dB`: the essential supremum on the open set `Ω` dominates the
  value at the point `p ∈ Ω`, `abs_le_of_eLpNorm_top_le`);
* `U ∈ W^{1,1}(0,1;L²(Ω))` (`integrableOn_dG`, `hasWeakDeriv_val_dU`), but
  `∂ₜU ∉ L²(0,1;L²(Ω))` (`not_memLp_dG`);
* `isLionsSolutionΩ_dU` — `U` is a Lions variational solution;
* `not_exists_L2_dU'`, `not_exists_L2_form` — neither `U'` nor the elliptic part
  `-div(𝔅∇U) = 𝒜U` is represented by an element of `L²(0,1;L²(Ω))`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped InnerProductSpace ComplexConjugate ENNReal

/-! ### Helpers -/

theorem memLp_Ioo01_of_continuous {E : Type*} [NormedAddCommGroup E] {F : ℝ → E}
    (hF : Continuous F) : MemLp F 2 (volume.restrict (Ioo 0 1)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hF.continuousOn
  refine MemLp.of_bound hF.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hC t (Ioo_subset_Icc_self ht)

theorem integrableOn_Ioo01_of_continuous {E : Type*} [NormedAddCommGroup E] {F : ℝ → E}
    (hF : Continuous F) : IntegrableOn F (Ioo 0 1) :=
  (hF.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

/-- The essential supremum on an open set of a function whose norm is `|g|`, `g` continuous,
dominates `|g(x₀)|` at every point `x₀` of the set. -/
theorem abs_le_of_eLpNorm_top_le {E F : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsOpenPosMeasure]
    [NormedAddCommGroup F] {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : AEStronglyMeasurable f (μ.restrict Ω)) {g : E → ℝ} (hg : Continuous g)
    (hfg : ∀ x, ‖f x‖ = |g x|) {M : ℝ} (hM : 0 ≤ M)
    (h : eLpNorm f ∞ (μ.restrict Ω) ≤ ENNReal.ofReal M)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) : |g x₀| ≤ M := by
  rw [eLpNorm_exponent_top hf] at h
  have hae : ∀ᵐ x ∂(μ.restrict Ω), |g x| ≤ M := by
    filter_upwards [ae_le_eLpNormEssSup (μ := μ.restrict Ω) (f := f)] with x hx
    have h1 := hx.trans h
    rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hM, hfg x] at h1
    exact h1
  by_contra hlt
  push Not at hlt
  have hmeas : MeasurableSet {x | M < |g x|} :=
    (isOpen_lt continuous_const (continuous_abs.comp hg)).measurableSet
  have hSo : IsOpen (Ω ∩ {x | M < |g x|}) :=
    hΩ.inter (isOpen_lt continuous_const (continuous_abs.comp hg))
  have hpos : 0 < μ (Ω ∩ {x | M < |g x|}) := hSo.measure_pos μ ⟨x₀, hx₀, hlt⟩
  have hzero : (μ.restrict Ω) {x | M < |g x|} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with x hx h'
    exact absurd h' (not_lt.2 hx)
  rw [Measure.restrict_apply hmeas, inter_comm] at hzero
  exact absurd hzero hpos.ne'

theorem norm_smul_id {n : ℕ} (c : ℝ) :
    ‖c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1)))‖ = |c| := by
  rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs]

theorem isSelfAdjoint_smul_id {n : ℕ} (c : ℝ) :
    IsSelfAdjoint (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) := by
  refine (IsSelfAdjoint.all c).smul ?_
  show star (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id]

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (D : Cutoffs) (P : DomParams n Ω)

/-! ### The coefficient -/

theorem continuous_dB_x (t : ℝ) : Continuous (dB D P t) := by
  have h := (continuous_domB D P.ε P.p (r := P.r)).comp (Continuous.prodMk_right (X := ℝ)
    (Y := EuclideanSpace ℝ (Fin (n + 1))) t)
  simp only [Function.comp_def, Function.uncurry] at h
  exact h

theorem dB_bounds (t : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    479 / 480 ≤ dB D P t x ∧ dB D P t x ≤ 481 / 480 :=
  ⟨a_ge D P.hε0 P.hε1 _ _, a_le D P.hε0 P.hε1 _ _⟩

theorem isBoundedCoeffΩ_dB (t : ℝ) : IsBoundedCoeffΩ (dB D P) t (481 / 480) where
  measurable := (continuous_dB_x D P t).measurable
  bound _ := abs_a_le D P.hε0 P.hε1 _ _

theorem isoCoeff_sub (𝔟 : ℝ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (s t : ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    isoCoeff 𝔟 t x - isoCoeff 𝔟 s x
      = (𝔟 t x - 𝔟 s x) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp [isoCoeff, sub_smul]

theorem isoCoeff_sub_id (𝔟 : ℝ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    isoCoeff 𝔟 t x - ContinuousLinearMap.id ℝ _
      = (𝔟 t x - 1) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp [isoCoeff, sub_smul]

theorem aestronglyMeasurable_isoCoeff_sub (s t : ℝ) :
    AEStronglyMeasurable (fun x => isoCoeff (dB D P) t x - isoCoeff (dB D P) s x)
      (volume.restrict Ω) := by
  refine Continuous.aestronglyMeasurable ?_
  simp only [isoCoeff_sub]
  exact ((continuous_dB_x D P t).sub (continuous_dB_x D P s)).smul continuous_const

theorem eLpNorm_isoCoeff_sub_id_le (t : ℝ) :
    eLpNorm (fun x => isoCoeff (dB D P) t x - ContinuousLinearMap.id ℝ _) ∞ (volume.restrict Ω)
      ≤ ENNReal.ofReal (P.ε / 480) := by
  have hm : AEStronglyMeasurable (fun x => isoCoeff (dB D P) t x - ContinuousLinearMap.id ℝ _)
      (volume.restrict Ω) := by
    refine Continuous.aestronglyMeasurable ?_
    simp only [isoCoeff_sub_id]
    exact ((continuous_dB_x D P t).sub continuous_const).smul continuous_const
  rw [eLpNorm_exponent_top hm]
  refine eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x => ?_)
  rw [isoCoeff_sub_id, norm_smul_id]
  exact abs_bR_sub_one_le D P.hε0 _ _ _ _

theorem eLpNorm_isoCoeff_sub_le (s t : ℝ) :
    eLpNorm (fun x => isoCoeff (dB D P) t x - isoCoeff (dB D P) s x) ∞ (volume.restrict Ω)
      ≤ ENNReal.ofReal (2 * |P.ε| * Cβ D / P.r * |t - s| ^ (1 / 2 : ℝ)) := by
  rw [eLpNorm_exponent_top (aestronglyMeasurable_isoCoeff_sub D P s t)]
  refine eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x => ?_)
  rw [isoCoeff_sub, norm_smul_id, ← Real.sqrt_eq_rpow]
  exact abs_bR_sub_le D P.ε P.hr _ _ _ _

theorem not_holder_dB (hΩ : IsOpen Ω) (hp : P.p ∈ Ω) (hr1 : P.r ≤ 1) (hε : 0 < P.ε) {α : ℝ}
    (hα : 1 / 2 < α) (hα1 : α < 1) :
    ¬ ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      eLpNorm (fun x => isoCoeff (dB D P) t x - isoCoeff (dB D P) s x) ∞ (volume.restrict Ω)
        ≤ ENNReal.ofReal (C * |t - s| ^ α) := by
  rintro ⟨C, hC⟩
  obtain ⟨s, t, hs, ht, -, hlt⟩ := bR_not_holder D hε P.hr hr1 (P.p 0) hα hα1 |C|
  have hle := hC s hs t ht
  have hle' : eLpNorm (fun x => isoCoeff (dB D P) t x - isoCoeff (dB D P) s x) ∞
      (volume.restrict Ω) ≤ ENNReal.ofReal (|C| * |t - s| ^ α) :=
    hle.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self C)
      (Real.rpow_nonneg (abs_nonneg _) _)))
  have key := abs_le_of_eLpNorm_top_le hΩ (aestronglyMeasurable_isoCoeff_sub D P s t)
    ((continuous_dB_x D P t).sub (continuous_dB_x D P s))
    (fun x => by rw [isoCoeff_sub, norm_smul_id]; rfl) (by positivity) hle' hp
  exact absurd key (not_le.2 hlt)

/-! ### The time derivative in `L²(Ω)` -/

theorem continuousAt_dG {t₀ : ℝ} (ht : t₀ ≠ 5 * P.r ^ 2 / 16) : ContinuousAt (dG D P) t₀ := by
  have hr2 : 0 < P.r ^ 2 := by have := P.hr; positivity
  set δ := |t₀ - 5 * P.r ^ 2 / 16| / 2 with hδ
  have hδ0 : 0 < δ := by
    have : t₀ - 5 * P.r ^ 2 / 16 ≠ 0 := sub_ne_zero.2 ht
    positivity
  have hT : ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), t / P.r ^ 2 ≠ 5 / 16 := by
    intro t htI h
    have ht' : t = 5 * P.r ^ 2 / 16 := by
      rw [div_eq_iff hr2.ne'] at h; linarith
    have h1 : |t₀ - t| ≤ δ := by
      rw [abs_le]; constructor <;> linarith [htI.1, htI.2]
    rw [ht'] at h1
    have : 0 < |t₀ - 5 * P.r ^ 2 / 16| := by positivity
    linarith
  exact continuousAt_toLp (G := fun t x => (domWt D P.ε P.r P.p t x : ℂ))
    (fun t => memLp_domWt D P.ε P.p Ω P.hr t) (measurableSet_domK P.r P.p) (domK_meas P)
    (fun t x hx => by rw [domWt_eq_zero D P.ε P.p P.hr t hx, Complex.ofReal_zero])
    (eventually_norm_sub_le_of_continuousOn (isCompact_domK P.r P.p) hδ0
      ((continuousOn_domWt D P.ε P.p P.hr hT).mono (prod_mono le_rfl (subset_univ _))))

theorem aestronglyMeasurable_dG : AEStronglyMeasurable (dG D P) (volume.restrict (Ioo 0 1)) := by
  have hc : ContinuousOn (dG D P) (Ioo 0 1 \ {5 * P.r ^ 2 / 16}) :=
    fun t ht => (continuousAt_dG D P ht.2).continuousWithinAt
  have h := hc.aestronglyMeasurable (μ := volume)
    (measurableSet_Ioo.diff (measurableSet_singleton _))
  rwa [Measure.restrict_congr_set (sdiff_null_ae_eq_self (measure_singleton _))] at h

theorem norm_dG (t : ℝ) :
    ‖dG D P t‖ = Real.sqrt (cQ P * P.r⁻¹ ^ 3) * Real.sqrt (utNormSq D P.ε (t / P.r ^ 2)) := by
  rw [← Real.sqrt_mul (by have := cQ_pos P; have := P.hr; positivity), mul_assoc,
    ← norm_dG_sq D P t, Real.sqrt_sq (norm_nonneg _)]

theorem utNormSq_eq_zero_of_time (ε : ℝ) {s : ℝ} (hs : s ∉ Ioo (1 / 8 : ℝ) (7 / 8)) :
    utNormSq D ε s = 0 := by
  rw [utNormSq, normSq]
  simp [ut_eq_zero_of_time D ε hs]

theorem integrable_sqrt_utNormSq (ε : ℝ) : Integrable (fun s => Real.sqrt (utNormSq D ε s)) := by
  have h := (integrableOn_sqrt_utNormSq' D ε)
  rw [← integrable_indicator_iff measurableSet_Icc] at h
  refine h.congr (Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hs]
  · have hs' : s ∉ Ioo (1 / 8 : ℝ) (7 / 8) := by
      intro h'
      have h1 := h'.1
      have h2 := h'.2
      exact hs ⟨by linarith, by linarith⟩
    rw [indicator_of_notMem hs]
    show (0 : ℝ) = Real.sqrt (utNormSq D ε s)
    rw [utNormSq_eq_zero_of_time D ε hs', Real.sqrt_zero]

theorem integrableOn_dG : IntegrableOn (dG D P) (Ioo 0 1) := by
  have hr2 : P.r ^ 2 ≠ 0 := by have := P.hr; positivity
  have hi : Integrable (fun t => Real.sqrt (cQ P * P.r⁻¹ ^ 3)
      * Real.sqrt (utNormSq D P.ε (t / P.r ^ 2))) :=
    ((integrable_sqrt_utNormSq D P.ε).comp_div hr2).const_mul _
  exact hi.integrableOn.mono' (aestronglyMeasurable_dG D P)
    (Eventually.of_forall fun t => (norm_dG D P t).le)

theorem hasWeakDeriv_val_dU :
    HasWeakDeriv (fun t => valΩ (n + 1) Ω (dU D P t)) (dG D P) :=
  hasWeakDeriv_of_hasDerivAt_off_countable (Set.countable_singleton (5 * P.r ^ 2 / 16))
    (continuous_val_dU D P).continuousOn (fun _ ht => hasDerivAt_val_dU D P ht.2)
    (integrableOn_dG D P)

theorem not_memLp_dG (hr1 : P.r ≤ 1) (hε : 0 < P.ε) :
    ¬ MemLp (dG D P) 2 (volume.restrict (Ioo 0 1)) := by
  intro h
  have h1 : IntegrableOn (fun t => ‖dG D P t‖ ^ 2) (Ioo 0 1) := h.norm.integrable_sq
  have hc := cQ_pos P
  have h2 : IntegrableOn (fun t => ∫ x, (P.r⁻¹ ^ 2 * utZ D P.ε (t / P.r ^ 2)
      ((x - P.p 0) / P.r)) ^ 2) (Icc 0 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    refine IntegrableOn.congr_fun (f := fun t => (cQ P)⁻¹ * ‖dG D P t‖ ^ 2)
      (h1.const_mul (cQ P)⁻¹) (fun t _ => ?_) measurableSet_Ioo
    show (cQ P)⁻¹ * ‖dG D P t‖ ^ 2 = _
    rw [norm_dG_sq, integral_sq_URt D P.ε P.hr, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  exact not_integrableOn_URt D hε.ne' P.hr hr1 (P.p 0) h2

/-! ### The Lions solution -/

theorem ofH10Ω_zero' : ofH10Ω (n + 1) Ω 0 = 0 := by
  rw [ofH10Ω_eq, map_zero, map_zero]

theorem isLionsSolutionΩ_dU : IsLionsSolutionΩ (n + 1) Ω (dB D P) (dF D P) (dU D P) := by
  have hc : Continuous fun s => ofH10Ω (n + 1) Ω (dU D P s) :=
    (ofHL (valΩ (n + 1) Ω)).continuous.comp ((valΩ (n + 1) Ω).continuous.comp (continuous_dU D P))
  refine ⟨memLp_Ioo01_of_continuous (continuous_dU D P), dU' D P,
    memLp_Ioo01_of_continuous (continuous_dU' D P), ?_, Eventually.of_forall fun t w =>
      equation_dU D P t w, fun t => ofH10Ω (n + 1) Ω (dU D P t), hc.continuousOn,
      Eventually.of_forall fun _ => rfl, by
        show ofH10Ω (n + 1) Ω (dU D P 0) = 0
        rw [dU_zero, ofH10Ω_zero']⟩
  exact hasWeakDeriv_of_hasDerivAt_off_countable Set.countable_empty hc.continuousOn
    (fun t _ => hasDerivAt_ofH10_dU D P t) (integrableOn_Ioo01_of_continuous (continuous_dU' D P))

theorem not_exists_L2_dU' (hΩ : IsOpen Ω) (hr1 : P.r ≤ 1) (hε : 0 < P.ε) :
    ¬ ∃ g : ℝ → L2Ω (n + 1) Ω, MemLp g 2 (volume.restrict (Ioo 0 1)) ∧
      ∀ᵐ t ∂(volume.restrict (Ioo 0 1)), dU' D P t = ofL2Ω (n + 1) Ω (g t) := by
  rintro ⟨g, hg, hae⟩
  refine not_memLp_dG D P hr1 hε (hg.ae_eq ?_)
  filter_upwards [hae] with t ht
  apply ofL2Ω_injective hΩ
  rw [← ht, dU'_eq, ofL2Ω_eq_ofHL]

theorem not_exists_L2_form (hΩ : IsOpen Ω) (hr1 : P.r ≤ 1) (hε : 0 < P.ε) :
    ¬ ∃ g : ℝ → L2Ω (n + 1) Ω, MemLp g 2 (volume.restrict (Ioo 0 1)) ∧
      ∀ᵐ t ∂(volume.restrict (Ioo 0 1)), ∀ w : H10Ω (n + 1) Ω,
        formΩ (n + 1) Ω (dB D P) t (dU D P t) w = ofL2Ω (n + 1) Ω (g t) w := by
  rintro ⟨g, hg, hae⟩
  refine not_exists_L2_dU' D P hΩ hr1 hε ⟨fun t => dF D P t - g t,
    (memLp_Ioo01_of_continuous (continuous_dF D P)).sub hg, ?_⟩
  filter_upwards [hae] with t ht
  ext w
  have e := equation_dU D P t w
  rw [ht w] at e
  rw [ofL2Ω_eq_ofHL, map_sub, sub_apply, ← ofL2Ω_eq_ofHL,
    ← ofL2Ω_eq_ofHL]
  linear_combination e

end LionsC12
