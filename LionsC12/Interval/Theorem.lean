module

public import LionsC12.Interval.Solution
public import LionsC12.Construction.Cutoffs

/-!
# Theorem 1.1 in the paper's function spaces

The assembly of Theorem 1.1 of the paper in the spaces `H = L²((0,π);ℂ)`, `V = H¹₀((0,π);ℂ)`,
`V' = H⁻¹((0,π);ℂ)` of `LionsC12.Paper.Statement`:

* `form_uV` — `u(t) ∈ D(A_H(t))` for every `t`: `𝔞(t)[u(t), w] = ⟨𝒜(t)u(t), w⟩` with
  `𝒜(t)u(t) = -∂ₓ(𝔞 ∂ₓu)(t) ∈ H` (integration by parts in `H¹₀`);
* `equation_uV` — `u'(t) + 𝒜(t)u(t) = f(t)` in `V'` for every `t`;
* `isLionsSolution_uV` and the uniqueness clause, from `isLionsSolution_unique`;
* the coefficient in `C^{0,1/2}([0,1];L^∞(0,π))` with the essential-supremum norm
  (`eLpNorm_a_sub_le`, `not_holder_Linfty`);
* `lions_counterexample_interval` — Theorem 1.1 with the statement of `Challenge.lean`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped InnerProductSpace ComplexConjugate ENNReal

variable (D : Cutoffs)

/-! ### Helpers -/

theorem memLp_of_continuousOn_Icc {E : Type*} [NormedAddCommGroup E] {F : ℝ → E}
    (hF : ContinuousOn F (Icc 0 1)) : MemLp F 2 (volume.restrict (Ioo 0 1)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hF
  refine MemLp.of_bound ((hF.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo) C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hC t (Ioo_subset_Icc_self ht)

theorem integrableOn_of_continuousOn_Icc {E : Type*} [NormedAddCommGroup E] {F : ℝ → E}
    (hF : ContinuousOn F (Icc 0 1)) : IntegrableOn F (Ioo 0 1) :=
  (hF.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

theorem integrableOn_norm_sq_of_memLp {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hg : MemLp g 2 (volume.restrict (Ioo 0 1))) :
    IntegrableOn (fun t => ‖g t‖ ^ 2) (Ioo 0 1) :=
  hg.norm.integrable_sq

theorem eLpNorm_top_le_of_forall {μ : Measure ℝ} {g : ℝ → ℝ} (hm : AEStronglyMeasurable g μ)
    {C : ℝ} (h : ∀ x, |g x| ≤ C) : eLpNorm g ∞ μ ≤ ENNReal.ofReal C := by
  rw [eLpNorm_exponent_top hm]
  exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact h x)

/-- The essential supremum on `(0,π)` of a continuous function is at least `|g(x₀)|` for every
`x₀ ∈ [0,π]`. -/
theorem ofReal_abs_le_eLpNorm_top {g : ℝ → ℝ} (hg : Continuous g) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc 0 π) : ENNReal.ofReal |g x₀| ≤ eLpNorm g ∞ (volume.restrict Iπ) := by
  rw [eLpNorm_exponent_top hg.aestronglyMeasurable]
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hc0, hc1, hc2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hlt
  have hcx : c < |g x₀| := by
    by_contra h
    push Not at h
    exact absurd (ENNReal.ofReal_le_ofReal h) (not_le.2 hc2)
  set S : Set ℝ := Iπ ∩ {x | c < |g x|} with hS
  have hSo : IsOpen S := isOpen_Ioo.inter (isOpen_lt continuous_const (continuous_abs.comp hg))
  have hSne : S.Nonempty := by
    have hcl : x₀ ∈ closure Iπ := by rw [closure_Ioo pi_pos.ne]; exact hx₀
    have hnb : {x | c < |g x|} ∈ 𝓝 x₀ :=
      (isOpen_lt continuous_const (continuous_abs.comp hg)).mem_nhds hcx
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.1 hcl _ hnb
    exact ⟨y, hy2, hy1⟩
  have hpos : 0 < volume S := hSo.measure_pos volume hSne
  have hae := (ae_le_eLpNormEssSup (μ := volume.restrict Iπ) (f := g))
  rw [ae_restrict_iff' measurableSet_Ioo] at hae
  have hzero : volume S = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with x hx hxS
    have h1 := hx hxS.1
    have h2 : ‖g x‖ₑ < ENNReal.ofReal c := lt_of_le_of_lt h1 hc1
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _)] at h2
    exact absurd hxS.2 (not_lt.2 h2.le)
  exact absurd hzero hpos.ne'

/-! ### The coefficient -/

theorem isBoundedCoeff_a {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : ℝ) :
    IsBoundedCoeff (a D ε) t (481 / 480) where
  measurable := (continuous_a_x D ε t).measurable
  bound x := by
    rw [abs_of_pos (lt_of_lt_of_le (by norm_num) (a_ge D hε0 hε1 t x))]
    exact a_le D hε0 hε1 t x

theorem a_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t x : ℝ) : 0 ≤ a D ε t x :=
  le_trans (by norm_num) (a_ge D hε0 hε1 t x)

/-- The coefficient increments in `L^∞(0,π)`: `‖𝔞(t) - 𝔞(s)‖_∞ ≤ 2ε C_β |t-s|^{1/2}`. -/
theorem eLpNorm_a_sub_le {ε : ℝ} (hε0 : 0 ≤ ε) (s t : ℝ) :
    eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict Iπ)
      ≤ ENNReal.ofReal (2 * ε * Cβ D * |t - s| ^ (1 / 2 : ℝ)) := by
  refine eLpNorm_top_le_of_forall
    ((continuous_a_x D ε t).sub (continuous_a_x D ε s)).aestronglyMeasurable fun x => ?_
  have := abs_a_sub_le D ε s t x
  rw [abs_of_nonneg hε0, ← Real.sqrt_eq_rpow] at *
  exact this

theorem eLpNorm_a_sub_one_le {ε : ℝ} (hε0 : 0 ≤ ε) (t : ℝ) :
    eLpNorm (fun x => a D ε t x - 1) ∞ (volume.restrict Iπ) ≤ ENNReal.ofReal (ε / 480) :=
  eLpNorm_top_le_of_forall ((continuous_a_x D ε t).sub continuous_const).aestronglyMeasurable
    fun x => abs_a_sub_one_le D hε0 t x

/-- Proposition 3.3 with the essential-supremum norm: `𝔞 ∉ C^{0,α}([0,1];L^∞(0,π))`. -/
theorem not_holder_Linfty {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) :
    ¬ ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict Iπ)
        ≤ ENNReal.ofReal (C * |t - s| ^ α) := by
  rintro ⟨C, hC⟩
  obtain ⟨s, t, hs, ht, -, hlt⟩ := not_holder D hε hα hα1 (max C 0)
  have h1 := ofReal_abs_le_eLpNorm_top ((continuous_a_x D ε t).sub (continuous_a_x D ε s))
    (x₀ := 0) ⟨le_rfl, pi_pos.le⟩
  have hCC : ENNReal.ofReal (C * |t - s| ^ α) ≤ ENNReal.ofReal (max C 0 * |t - s| ^ α) :=
    ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _)
  have h2 := h1.trans ((hC s hs t ht).trans hCC)
  have hpos : 0 ≤ max C 0 * |t - s| ^ α := by positivity
  have h3 := ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hlt, lt_of_le_of_lt hpos hlt⟩
  exact absurd (lt_of_lt_of_le h3 h2) (lt_irrefl _)

/-! ### The equation in `V'` -/

/-- `𝒜(t)u(t) = -∂ₓ(𝔞(t,·)∂ₓu(t)) ∈ H`. -/
def AuH (ε t : ℝ) : L2 Iπ := toL2c (Au D ε t) (continuous_Au_x D ε t)

/-- The forcing `f(t) ∈ H`. -/
def fH (ε t : ℝ) : L2 Iπ := toL2c (f D ε t) (continuous_f_x D ε t)

theorem norm_fH_sub_sq (ε s t : ℝ) :
    ‖fH D ε s - fH D ε t‖ ^ 2 = normSq (fun x => f D ε s x - f D ε t x) := by
  rw [fH, fH, ← toL2c_sub, norm_toL2c_sq]

theorem continuous_fH (ε : ℝ) : Continuous (fH D ε) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h := (f_tendsto_H D ε t).sqrt
  rw [Real.sqrt_zero] at h
  refine h.congr fun s => ?_
  rw [← norm_fH_sub_sq, Real.sqrt_sq (norm_nonneg _)]

theorem im_fH (ε t : ℝ) : ∀ᵐ x ∂(volume.restrict (Ioo 0 π)), (fH D ε t x).im = 0 :=
  im_toL2c _

theorem im_val_uV (ε t : ℝ) :
    ∀ᵐ x ∂(volume.restrict (Ioo 0 π)), (val (Ioo 0 π) (uV D ε t) x).im = 0 := by
  rw [val_uV]; exact im_toL2c _

/-- `u(t) ∈ D(A_H(t))`: `𝔞(t)[u(t), w] = ⟨𝒜(t)u(t), w⟩` with `𝒜(t)u(t) = -∂ₓ(𝔞 ∂ₓu) ∈ H`. -/
theorem form_uV (ε t : ℝ) (w : H10 Iπ) :
    form Iπ (a D ε) t (uV D ε t) w = ofL2 Iπ (AuH D ε t) w := by
  set G : ℝ → ℂ := fun x => ((a D ε t x * ux D ε t x : ℝ) : ℂ) with hGdef
  set g : ℝ → ℂ := fun x => ((-(Au D ε t x) : ℝ) : ℂ) with hgdef
  have hG : ∀ x, HasDerivAt G (g x) x := fun x => (hasDerivAt_flux D ε t x).ofReal_comp
  have hgc : Continuous g := continuous_cplx (continuous_Au_x D ε t).neg
  have hGc : Continuous G := continuous_cplx ((continuous_a_x D ε t).mul (continuous_ux_x D ε t))
  have hG2 := memLp_Ioo_of_continuous (a := 0) (b := π) hGc
  have hg2 := memLp_Ioo_of_continuous (a := 0) (b := π) hgc
  have key := inner_dx_eq hG hgc hG2 hg2 w
  have e1 : form Iπ (a D ε) t (uV D ε t) w = ⟪dx Iπ w, toL2 Iπ G hG2⟫_ℂ := by
    rw [inner_L2_eq, form]
    refine integral_congr_ae ?_
    have hdx := dx_uV D ε t
    filter_upwards [coe_toL2c (continuous_ux_x D ε t), coe_toL2 G hG2] with x h1 h2
    rw [hdx, h1, h2, hGdef]
    simp only [Complex.ofReal_mul]
    ring
  have e2 : toL2 Iπ g hg2 = -AuH D ε t := by
    apply Lp.ext
    filter_upwards [coe_toL2 g hg2, coe_toL2c (continuous_Au_x D ε t),
      Lp.coeFn_neg (AuH D ε t)] with x h1 h2 h3
    rw [h1, h3, Pi.neg_apply, AuH, h2]
    simp only [hgdef, Complex.ofReal_neg]
  rw [e1, key, e2, inner_neg_right, neg_neg]
  rfl

theorem utH_add_AuH (ε t : ℝ) : utH D ε t + AuH D ε t = fH D ε t := by
  rw [utH, AuH, fH, ← toL2c_add]
  exact toL2c_congr _ _ fun x _ => pde D ε t x

/-- The equation `u'(t) + 𝒜(t)u(t) = f(t)` in `V'`, for every `t`. -/
theorem equation_uV (ε t : ℝ) (w : H10 Iπ) :
    uV' D ε t w + form Iπ (a D ε) t (uV D ε t) w = ofL2 Iπ (fH D ε t) w := by
  rw [form_uV, uV', ← utH_add_AuH D ε t, ofL2_add']
  rfl

theorem ofH10_zero : ofH10 Iπ 0 = 0 := by
  rw [ofH10, map_zero, ofL2_eq_ofHL, map_zero]

theorem hasWeakDeriv_ofH10_uV {ε : ℝ} (hε0 : 0 ≤ ε) :
    HasWeakDeriv (fun t => ofH10 Iπ (uV D ε t)) (uV' D ε) :=
  hasWeakDeriv_of_hasDerivAt_off_countable Set.countable_empty
    (fun t _ => (hasDerivAt_ofH10_uV D hε0 t).continuousAt.continuousWithinAt)
    (fun t _ => hasDerivAt_ofH10_uV D hε0 t)
    (integrableOn_of_continuousOn_Icc (continuous_uV' D hε0).continuousOn)

/-- `u` is a Lions variational solution. -/
theorem isLionsSolution_uV {ε : ℝ} (hε0 : 0 ≤ ε) :
    IsLionsSolution Iπ (a D ε) (fH D ε) (uV D ε) :=
  ⟨memLp_of_continuousOn_Icc (continuous_uV D ε).continuousOn, uV' D ε,
    memLp_of_continuousOn_Icc (continuous_uV' D hε0).continuousOn, hasWeakDeriv_ofH10_uV D hε0,
    Eventually.of_forall fun t w => equation_uV D ε t w,
    ⟨fun t => ofH10 Iπ (uV D ε t),
      fun t _ => (hasDerivAt_ofH10_uV D hε0 t).continuousAt.continuousWithinAt,
      Eventually.of_forall fun _ => rfl, by
        show ofH10 Iπ (uV D ε 0) = 0
        rw [uV_zero, ofH10_zero]⟩⟩

/-- `u` is the unique Lions variational solution. -/
theorem eq_uV_of_isLionsSolution {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {w : ℝ → H10 Iπ}
    (hw : IsLionsSolution Iπ (a D ε) (fH D ε) w) : ∀ᵐ t ∂μ01, w t = uV D ε t :=
  isLionsSolution_unique isOpen_Ioo (fun t => isBoundedCoeff_a D hε0 hε1 t)
    (a_nonneg D hε0 hε1) hw (isLionsSolution_uV D hε0)

/-! ### The negative clauses -/

theorem AuH_eq_sub (ε t : ℝ) : AuH D ε t = fH D ε t - utH D ε t := by
  rw [← utH_add_AuH D ε t]; abel

theorem integrableOn_AuH {ε : ℝ} (hε0 : 0 ≤ ε) : IntegrableOn (AuH D ε) (Ioo 0 1) := by
  have h := (integrableOn_of_continuousOn_Icc (continuous_fH D ε).continuousOn).sub
    (integrableOn_utH D hε0)
  exact h.congr_fun (fun t _ => (AuH_eq_sub D ε t).symm) measurableSet_Ioo

theorem not_memLp_AuH {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ¬ MemLp (AuH D ε) 2 (volume.restrict (Ioo 0 1)) := by
  intro h
  have h1 := integrableOn_norm_sq_of_memLp h
  have h2 : IntegrableOn (fun t => normSq (Au D ε t)) (Ioo 0 1) :=
    h1.congr_fun (fun t _ => by simp only [AuH, norm_toL2c_sq]) measurableSet_Ioo
  exact not_integrableOn_normSq_Au D hε0 hε1
    (by rw [integrableOn_Icc_iff_integrableOn_Ioo]; exact h2)

theorem not_memLp_utH {ε : ℝ} (hε0 : 0 < ε) :
    ¬ MemLp (utH D ε) 2 (volume.restrict (Ioo 0 1)) := by
  intro h
  have h1 := integrableOn_norm_sq_of_memLp h
  have h2 : IntegrableOn (utNormSq D ε) (Ioo 0 1) :=
    h1.congr_fun (fun t _ => by simp only [utH, norm_toL2c_sq, utNormSq]) measurableSet_Ioo
  exact not_integrableOn_utNormSq D hε0.ne'
    (by rw [integrableOn_Icc_iff_integrableOn_Ioo]; exact h2)

theorem AuH_eq_of_form {ε : ℝ} {g : ℝ → L2 Iπ}
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w : H10 Iπ, form Iπ (a D ε) t (uV D ε t) w = ofL2 Iπ (g t) w)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : g t = AuH D ε t := by
  apply ofL2_injective isOpen_Ioo
  ext w
  rw [← hg t ht w, form_uV]

/-- `A_H(·)u(·) ∈ L¹(0,1;H) ∖ L²(0,1;H)`, for every representative `g` of `t ↦ 𝒜(t)u(t)`. -/
theorem AH_u_L1_not_L2 {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {g : ℝ → L2 Iπ}
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w : H10 Iπ, form Iπ (a D ε) t (uV D ε t) w = ofL2 Iπ (g t) w) :
    IntegrableOn g (Ioo 0 1) ∧ ¬ MemLp g 2 (volume.restrict (Ioo 0 1)) := by
  have hae : g =ᵐ[volume.restrict (Ioo 0 1)] AuH D ε := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact AuH_eq_of_form D hg (Ioo_subset_Icc_self ht)
  refine ⟨(integrableOn_AuH D hε0.le).congr_fun_ae hae.symm, fun h => ?_⟩
  exact not_memLp_AuH D hε0 hε1 (h.ae_eq hae)

/-- `∂ₜu ∉ L²(0,1;H)`: no `g ∈ L²(0,1;H)` represents `u'` almost everywhere. -/
theorem not_exists_L2_rep_uV' {ε : ℝ} (hε0 : 0 < ε) :
    ¬ ∃ g : ℝ → L2 Iπ, MemLp g 2 (volume.restrict (Ioo 0 1)) ∧
      ∀ᵐ t ∂(volume.restrict (Ioo 0 1)), uV' D ε t = ofL2 Iπ (g t) := by
  rintro ⟨g, hg, hrep⟩
  have hae : g =ᵐ[volume.restrict (Ioo 0 1)] utH D ε := by
    filter_upwards [hrep] with t ht
    exact (ofL2_injective isOpen_Ioo ht).symm
  exact not_memLp_utH D hε0 (hg.ae_eq hae)

/-! ### Theorem 1.1 -/

/-- **Theorem 1.1** (counterexample on an interval), with the statement of `Challenge.lean`:
see `LionsC12Challenge.lions_counterexample_interval` for the reading of the clauses. -/
theorem lions_counterexample_interval (δ : ℝ) (hδ : 0 < δ) :
    ∃ (𝔞 : ℝ → ℝ → ℝ) (f : ℝ → L2 (Ioo 0 Real.pi)) (u : ℝ → H10 (Ioo 0 Real.pi))
      (u' : ℝ → Hm1 (Ioo 0 Real.pi)),
      Measurable (Function.uncurry 𝔞) ∧
      (∃ lam Λ : ℝ, 0 < lam ∧ ∀ t x, lam ≤ 𝔞 t x ∧ 𝔞 t x ≤ Λ) ∧
      (∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ A + B < δ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, eLpNorm (fun x => 𝔞 t x - 1) ∞ (volume.restrict (Ioo 0 Real.pi))
          ≤ ENNReal.ofReal A) ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          eLpNorm (fun x => 𝔞 t x - 𝔞 s x) ∞ (volume.restrict (Ioo 0 Real.pi))
            ≤ ENNReal.ofReal (B * |t - s| ^ (1 / 2 : ℝ))) ∧
      (∀ α : ℝ, 1 / 2 < α → α < 1 → ¬ ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          eLpNorm (fun x => 𝔞 t x - 𝔞 s x) ∞ (volume.restrict (Ioo 0 Real.pi))
            ≤ ENNReal.ofReal (C * |t - s| ^ α)) ∧
      ContinuousOn f (Icc 0 1) ∧ MemLp f 2 (volume.restrict (Ioo 0 1)) ∧
      (∀ t, ∀ᵐ x ∂(volume.restrict (Ioo 0 Real.pi)), (f t x).im = 0) ∧
      ContinuousOn u (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun s => ofH10 (Ioo 0 Real.pi) (u s)) (u' t) (Icc 0 1) t) ∧
      ContinuousOn u' (Icc 0 1) ∧
      IntegrableOn (fun t => val (Ioo 0 Real.pi) (u t)) (Ioo 0 1) ∧
      (∃ g : ℝ → L2 (Ioo 0 Real.pi), IntegrableOn g (Ioo 0 1) ∧
        HasWeakDeriv (fun t => val (Ioo 0 Real.pi) (u t)) g) ∧
      (∀ t, ∀ᵐ x ∂(volume.restrict (Ioo 0 Real.pi)), (val (Ioo 0 Real.pi) (u t) x).im = 0) ∧
      u 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ w : H10 (Ioo 0 Real.pi),
        u' t w + form (Ioo 0 Real.pi) 𝔞 t (u t) w = ofL2 (Ioo 0 Real.pi) (f t) w) ∧
      IsLionsSolution (Ioo 0 Real.pi) 𝔞 f u ∧
      (∀ w : ℝ → H10 (Ioo 0 Real.pi), IsLionsSolution (Ioo 0 Real.pi) 𝔞 f w →
        ∀ᵐ t ∂(volume.restrict (Ioo 0 1)), w t = u t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∃ h : L2 (Ioo 0 Real.pi), ∀ w : H10 (Ioo 0 Real.pi),
        form (Ioo 0 Real.pi) 𝔞 t (u t) w = ofL2 (Ioo 0 Real.pi) h w) ∧
      (∀ g : ℝ → L2 (Ioo 0 Real.pi), (∀ t ∈ Icc (0 : ℝ) 1, ∀ w : H10 (Ioo 0 Real.pi),
          form (Ioo 0 Real.pi) 𝔞 t (u t) w = ofL2 (Ioo 0 Real.pi) (g t) w) →
        IntegrableOn g (Ioo 0 1) ∧ ¬ MemLp g 2 (volume.restrict (Ioo 0 1))) ∧
      ¬ ∃ g : ℝ → L2 (Ioo 0 Real.pi), MemLp g 2 (volume.restrict (Ioo 0 1)) ∧
        ∀ᵐ t ∂(volume.restrict (Ioo 0 1)), u' t = ofL2 (Ioo 0 Real.pi) (g t) := by
  let D : Cutoffs := Classical.choice Cutoffs.nonempty
  have hCβ : 0 ≤ Cβ D := by
    unfold Cβ
    have := D.Cη_nonneg
    positivity
  set ε : ℝ := min 1 (δ / (2 * (1 + 2 * Cβ D))) with hε
  have hεpos : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεδ : ε ≤ δ / (2 * (1 + 2 * Cβ D)) := min_le_right _ _
  have hε0 : 0 ≤ ε := hεpos.le
  refine ⟨a D ε, fH D ε, uV D ε, uV' D ε, (continuous_a D ε).measurable,
    ⟨479 / 480, 481 / 480, by norm_num, fun t x => ⟨a_ge D hε0 hε1 t x, a_le D hε0 hε1 t x⟩⟩,
    ⟨ε / 480, 2 * ε * Cβ D, div_nonneg hε0 (by norm_num),
      mul_nonneg (mul_nonneg zero_le_two hε0) hCβ, ?_, fun t _ => eLpNorm_a_sub_one_le D hε0 t,
      fun s _ t _ => eLpNorm_a_sub_le D hε0 s t⟩,
    fun α hα hα1 => not_holder_Linfty D hεpos hα hα1,
    (continuous_fH D ε).continuousOn, memLp_of_continuousOn_Icc (continuous_fH D ε).continuousOn,
    im_fH D ε, (continuous_uV D ε).continuousOn,
    fun t _ => (hasDerivAt_ofH10_uV D hε0 t).hasDerivWithinAt,
    (continuous_uV' D hε0).continuousOn,
    integrableOn_of_continuousOn_Icc ((val Iπ).continuous.comp (continuous_uV D ε)).continuousOn,
    ⟨utH D ε, integrableOn_utH D hε0, hasWeakDeriv_val_uV D hε0⟩, im_val_uV D ε, uV_zero D ε,
    fun t _ w => equation_uV D ε t w, isLionsSolution_uV D hε0,
    fun w hw => eq_uV_of_isLionsSolution D hε0 hε1 hw,
    fun t _ => ⟨AuH D ε t, form_uV D ε t⟩, fun g hg => AH_u_L1_not_L2 D hεpos hε1 hg,
    not_exists_L2_rep_uV' D hεpos⟩
  have h1 : ε * (1 + 2 * Cβ D) ≤ δ / 2 := by
    have hpos : 0 < 2 * (1 + 2 * Cβ D) := by positivity
    calc ε * (1 + 2 * Cβ D) ≤ δ / (2 * (1 + 2 * Cβ D)) * (1 + 2 * Cβ D) := by gcongr
      _ = δ / 2 := by field_simp
  nlinarith

end LionsC12
