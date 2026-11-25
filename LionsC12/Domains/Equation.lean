module

public import LionsC12.Domains.Construction

/-!
# The counterexample on a domain in the paper's spaces

With the functions of `LionsC12.Domains.Construction`, for parameters `P : DomParams n Ω`
(`0 ≤ ε ≤ 1`, `0 < r`, `K = closedBall p (r(π+1)) ⊆ Ω`):

* `dU t ∈ H¹₀(Ω)` (a test function), `dG t = ∂ₜU(t) ∈ L²(Ω)`, `dF t = F(t) ∈ L²(Ω)`,
  `dGv t = 𝔟(t)∇U(t) ∈ L²(Ω;ℂ^d)` and `dU' t = F(t) - 𝒜(t)U(t) ∈ H⁻¹(Ω)`;
* `continuous_dU`, `continuous_dF`, `continuous_dU'` — continuity in time;
* `hasDerivAt_val_dU` — differentiability in `L²(Ω)` off `t = 5r²/16`;
* `form_dU`, `swf` — `𝔟(t)[U(t), w] = ⟨∇w, 𝔟∇U⟩ = ⟨w, F(t) - ∂ₜU(t)⟩` for all `w ∈ H¹₀(Ω)`
  (the spatial weak formulation: `tensorΩ_weak` on test functions, then density);
* `dU'_eq`, `hasDerivAt_ofH10_dU` — `dU' t = ∂ₜU(t)` in `H⁻¹(Ω)` and it is the derivative of
  `t ↦ U(t) ∈ H⁻¹(Ω)` at every `t` (FTC across the exceptional time);
* `norm_dG_sq` — `‖∂ₜU(t)‖² = c_Q r⁻³ ‖∂ₜu(t/r²)‖²_{L²(0,π)}`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped InnerProductSpace ComplexConjugate ENNReal

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}

/-- The parameters of the construction on `Ω`. -/
structure DomParams (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) where
  /-- The amplitude `ε` of the coefficient `1 + εβ`. -/
  ε : ℝ
  /-- The radius `r` of the parabolic rescaling. -/
  r : ℝ
  /-- The centre `p` of the rescaled construction. -/
  p : EuclideanSpace ℝ (Fin (n + 1))
  hε0 : 0 ≤ ε
  hε1 : ε ≤ 1
  hr : 0 < r
  hK : domK r p ⊆ Ω

variable (D : Cutoffs) (P : DomParams n Ω)

/-- The coefficient. -/
def dB : ℝ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ := domB D P.ε P.r P.p

theorem isTest_dU (t : ℝ) : IsTestFunΩ Ω (fun x => (domW D P.ε P.r P.p t x : ℂ)) where
  contDiff := Complex.ofRealCLM.contDiff.comp (contDiff_domW D P.ε P.p P.hr t)
  hasCompactSupport := HasCompactSupport.intro (isCompact_domK P.r P.p) fun x hx => by
    rw [domW_eq_zero D P.ε P.p P.hr t hx, Complex.ofReal_zero]
  tsupport_subset := by
    refine (closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall).trans P.hK
    by_contra h
    exact hx (by
      show (domW D P.ε P.r P.p t x : ℂ) = 0
      rw [domW_eq_zero D P.ε P.p P.hr t h, Complex.ofReal_zero])

/-- The solution `U(t) ∈ H¹₀(Ω)`. -/
def dU (t : ℝ) : H10Ω (n + 1) Ω := ofTestΩ (isTest_dU D P t)

/-- The time derivative `∂ₜU(t) ∈ L²(Ω)`. -/
def dG (t : ℝ) : L2Ω (n + 1) Ω := toL2Ω Ω _ (memLp_domWt D P.ε P.p Ω P.hr t)

/-- The forcing `F(t) ∈ L²(Ω)`. -/
def dF (t : ℝ) : L2Ω (n + 1) Ω := toL2Ω Ω _ (memLp_domF D P.p Ω P.hε0 P.hε1 P.hr t)

/-- The flux `𝔟(t)∇U(t) ∈ L²(Ω;ℂ^d)`. -/
def dGv (t : ℝ) : L2Ωvec (n + 1) Ω := toL2Ωvec Ω _ (memLp_domBGrad D P.p Ω (ε := P.ε) P.hr t)

/-- The derivative `U'(t) = F(t) - 𝒜(t)U(t) ∈ H⁻¹(Ω)`. -/
def dU' (t : ℝ) : Hm1Ω (n + 1) Ω :=
  ofL2Ω (n + 1) Ω (dF D P t) - ofHL (gradΩ (n + 1) Ω) (dGv D P t)

theorem coe_val_dU (t : ℝ) :
    ⇑(valΩ (n + 1) Ω (dU D P t)) =ᵐ[volume.restrict Ω] fun x => (domW D P.ε P.r P.p t x : ℂ) :=
  coe_valΩ_ofTestΩ _

theorem coe_grad_dU (t : ℝ) :
    ⇑(gradΩ (n + 1) Ω (dU D P t)) =ᵐ[volume.restrict Ω] domGrad D P.ε P.r P.p t := by
  rw [← grad_domW D P.ε P.p P.hr t]
  exact coe_gradΩ_ofTestΩ _

theorem coe_dG (t : ℝ) :
    ⇑(dG D P t) =ᵐ[volume.restrict Ω] fun x => (domWt D P.ε P.r P.p t x : ℂ) :=
  coe_toL2Ω _ _

theorem coe_dF (t : ℝ) :
    ⇑(dF D P t) =ᵐ[volume.restrict Ω] fun x => (domF D P.ε P.r P.p t x : ℂ) :=
  coe_toL2Ω _ _

theorem coe_dGv (t : ℝ) :
    ⇑(dGv D P t) =ᵐ[volume.restrict Ω]
      fun x => (domB D P.ε P.r P.p t x : ℂ) • domGrad D P.ε P.r P.p t x :=
  coe_toL2Ωvec _ _

/-! ### Continuity in time -/

theorem domK_meas : (volume.restrict Ω) (domK P.r P.p) < ∞ := domK_measure_lt_top P.p Ω

theorem continuous_val_dU : Continuous fun t => valΩ (n + 1) Ω (dU D P t) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  refine continuousAt_toLp (fun t => (isTest_dU D P t).memLp) (measurableSet_domK P.r P.p)
    (domK_meas P) (fun t x hx => by rw [domW_eq_zero D P.ε P.p P.hr t hx, Complex.ofReal_zero])
    ?_
  exact eventually_norm_sub_le_of_continuousOn (isCompact_domK P.r P.p) (t₀ := t₀) one_pos
    (continuous_domW D P.ε P.p P.hr).continuousOn

theorem continuous_grad_dU : Continuous fun t => gradΩ (n + 1) Ω (dU D P t) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  refine continuousAt_toLp (fun t => (isTest_dU D P t).memLp_grad) (measurableSet_domK P.r P.p)
    (domK_meas P) (fun t x hx => by
      rw [grad_domW D P.ε P.p P.hr t, domGrad_eq_zero D P.ε P.p P.hr t hx]) ?_
  intro η hη
  filter_upwards [eventually_norm_sub_le_of_continuousOn (isCompact_domK P.r P.p) (t₀ := t₀)
    one_pos (continuous_domGrad D P.ε P.p P.hr).continuousOn η hη] with t ht x hx
  rw [grad_domW D P.ε P.p P.hr t, grad_domW D P.ε P.p P.hr t₀]
  exact ht x hx

theorem continuous_dU : Continuous (dU D P) := by
  have hpair : Continuous fun t => H10Ω.pair (dU D P t) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ (L2Ω (n + 1) Ω) (L2Ωvec (n + 1) Ω)).symm.continuous.comp
      ((continuous_val_dU D P).prodMk (continuous_grad_dU D P))
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h := (continuous_iff_continuousAt.1 hpair t₀)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero] at h
  refine h.congr fun t => ?_
  rw [H10Ω.norm_eq, H10Ω.pair_sub]

theorem continuous_dF : Continuous (dF D P) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  exact continuousAt_toLp (fun t => memLp_domF D P.p Ω P.hε0 P.hε1 P.hr t)
    (measurableSet_domK P.r P.p) (domK_meas P)
    (fun t x hx => by rw [domF_eq_zero D P.ε P.p P.hr t hx, Complex.ofReal_zero])
    (eventually_domF D P.ε P.p P.hr t₀)

theorem continuous_dGv : Continuous (dGv D P) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  exact continuousAt_toLp (fun t => memLp_domBGrad D P.p Ω (ε := P.ε) P.hr t)
    (measurableSet_domK P.r P.p) (domK_meas P)
    (fun t x hx => by rw [domGrad_eq_zero D P.ε P.p P.hr t hx, smul_zero])
    (eventually_norm_sub_le_of_continuousOn (isCompact_domK P.r P.p) (t₀ := t₀) one_pos
      (continuous_domBGrad D P.ε P.p P.hr).continuousOn)

theorem continuous_dU' : Continuous (dU' D P) :=
  ((ofHL (valΩ (n + 1) Ω)).continuous.comp (continuous_dF D P)).sub
    ((ofHL (gradΩ (n + 1) Ω)).continuous.comp (continuous_dGv D P))

/-! ### Differentiability in `L²(Ω)` -/

theorem hasDerivAt_val_dU {t₀ : ℝ} (ht : t₀ ≠ 5 * P.r ^ 2 / 16) :
    HasDerivAt (fun t => valΩ (n + 1) Ω (dU D P t)) (dG D P t₀) t₀ := by
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
  refine hasDerivAt_toLp (G := fun t x => (domW D P.ε P.r P.p t x : ℂ))
    (G' := fun t x => (domWt D P.ε P.r P.p t x : ℂ))
    (fun t => (isTest_dU D P t).memLp) (memLp_domWt D P.ε P.p Ω P.hr t₀)
    (measurableSet_domK P.r P.p) (domK_meas P)
    (fun t x hx => by rw [domW_eq_zero D P.ε P.p P.hr t hx, Complex.ofReal_zero])
    (fun x hx => by rw [domWt_eq_zero D P.ε P.p P.hr t₀ hx, Complex.ofReal_zero])
    (fun t x _ => ((hasDerivAt_URt_t D P.ε (r := P.r) P.p t (x 0)).mul_const _).ofReal_comp) ?_
  exact eventually_norm_sub_le_of_continuousOn (isCompact_domK P.r P.p) hδ0
    ((continuousOn_domWt D P.ε P.p P.hr hT).mono (prod_mono le_rfl (subset_univ _)))

/-! ### The form and the spatial weak formulation -/

theorem form_dU (t : ℝ) (w : H10Ω (n + 1) Ω) :
    formΩ (n + 1) Ω (dB D P) t (dU D P t) w = ⟪gradΩ (n + 1) Ω w, dGv D P t⟫_ℂ := by
  rw [inner_L2Ωvec_eq, formΩ]
  refine integral_congr_ae ?_
  filter_upwards [coe_grad_dU D P t, coe_dGv D P t] with x h1 h2
  rw [h1, h2, inner_smul_right]
  rfl

/-- **The spatial weak formulation**: `⟨∇w, 𝔟∇U(t)⟩ = ⟨w, F(t) - ∂ₜU(t)⟩` for all
`w ∈ H¹₀(Ω)`. -/
theorem swf (t : ℝ) (w : H10Ω (n + 1) Ω) :
    ⟪gradΩ (n + 1) Ω w, dGv D P t⟫_ℂ = ⟪valΩ (n + 1) Ω w, dF D P t - dG D P t⟫_ℂ := by
  set Λ : WithLp 2 (L2Ω (n + 1) Ω × L2Ωvec (n + 1) Ω) →L⋆[ℂ] ℂ :=
    (innerSLFlip ℂ (dGv D P t)).comp (WithLp.sndL 2 ℂ (L2Ω (n + 1) Ω) (L2Ωvec (n + 1) Ω)) -
      (innerSLFlip ℂ (dF D P t - dG D P t)).comp
        (WithLp.fstL 2 ℂ (L2Ω (n + 1) Ω) (L2Ωvec (n + 1) Ω)) with hΛ
  have hval : ∀ q : WithLp 2 (L2Ω (n + 1) Ω × L2Ωvec (n + 1) Ω),
      Λ q = ⟪(WithLp.ofLp q).2, dGv D P t⟫_ℂ - ⟪(WithLp.ofLp q).1, dF D P t - dG D P t⟫_ℂ := by
    intro q
    simp only [hΛ, sub_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      innerSLFlip_apply_apply, WithLp.sndL_apply, WithLp.fstL_apply]
    rfl
  have h0 : ∀ q ∈ testGraphΩ (n + 1) Ω, Λ q = 0 := by
    rintro q ⟨φ, hc1, hcs, hsub, h1, h2⟩
    have hφ : IsTestFunΩ Ω φ := ⟨hc1, hcs, hsub⟩
    rw [hval, sub_eq_zero, inner_L2Ωvec_eq, inner_L2Ω_eq]
    have e1 : ∫ x in Ω, ⟪(WithLp.ofLp q).2 x, dGv D P t x⟫_ℂ
        = ∫ x, (bR D P.ε P.r (P.p 0) t (x 0) : ℂ)
            * ⟪grad φ x, gradTens (UR D P.ε P.r (P.p 0) t) (URx D P.ε P.r (P.p 0) t)
              (Qr P.r P.p) x⟫_ℂ := by
      calc ∫ x in Ω, ⟪(WithLp.ofLp q).2 x, dGv D P t x⟫_ℂ
          = ∫ x in Ω, (bR D P.ε P.r (P.p 0) t (x 0) : ℂ)
            * ⟪grad φ x, gradTens (UR D P.ε P.r (P.p 0) t) (URx D P.ε P.r (P.p 0) t)
              (Qr P.r P.p) x⟫_ℂ := by
            refine integral_congr_ae ?_
            filter_upwards [h2, coe_dGv D P t] with x hx hx'
            rw [hx, hx', inner_smul_right]
            rfl
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
            rw [hφ.grad_eq_zero_of_notMem hx]
            simp
    have e2 : ∫ x in Ω, conj ((WithLp.ofLp q).1 x) * (dF D P t - dG D P t) x
        = ∫ x, conj (φ x) * ((ARZ D P.ε P.r (P.p 0) t (x 0) * Qr P.r P.p (tailL n x)
          - bR D P.ε P.r (P.p 0) t (x 0) * UR D P.ε P.r (P.p 0) t (x 0)
            * lapQ (Qr P.r P.p) (tailL n x) : ℝ) : ℂ) := by
      calc ∫ x in Ω, conj ((WithLp.ofLp q).1 x) * (dF D P t - dG D P t) x
          = ∫ x in Ω, conj (φ x) * ((ARZ D P.ε P.r (P.p 0) t (x 0) * Qr P.r P.p (tailL n x)
            - bR D P.ε P.r (P.p 0) t (x 0) * UR D P.ε P.r (P.p 0) t (x 0)
              * lapQ (Qr P.r P.p) (tailL n x) : ℝ) : ℂ) := by
            refine integral_congr_ae ?_
            filter_upwards [h1, Lp.coeFn_sub (dF D P t) (dG D P t), coe_dF D P t, coe_dG D P t]
              with x hx hsub' hF hG
            rw [hx, hsub', Pi.sub_apply, hF, hG, ← Complex.ofReal_sub,
              domF_sub_domWt D P.ε P.r P.p t x]
            rfl
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
            rw [hφ.eq_zero_of_notMem hx, map_zero, zero_mul]
    rw [e1, e2]
    have hε0 := P.hε0
    have hε1 := P.hε1
    exact tensorΩ_weak (continuous_UR_x D P.ε P.r (P.p 0) t).measurable
      (continuous_URx_x D P.ε P.r (P.p 0) t).measurable (measurable_ARZ_x D P.ε P.r (P.p 0) t)
      (continuous_bR_x D P.ε P.r (P.p 0) t).measurable (bdd_UR_x D hε0 hε1 P.r (P.p 0) t)
      (bdd_URx_x D hε0 hε1 P.r (P.p 0) t) (bdd_ARZ_x D P.ε P.r (P.p 0) t)
      (bdd_bR_x D hε0 hε1 P.r (P.p 0) t) (isBumpFn_Qr P.hr P.p)
      (fun ψ hψ _ => weak1D D P.ε P.hr (P.p 0) t hψ) hc1 hcs
  have := eq_zero_of_testGraphΩ Λ h0 w
  rw [hval, sub_eq_zero] at this
  exact this

theorem dU'_eq (t : ℝ) : dU' D P t = ofHL (valΩ (n + 1) Ω) (dG D P t) := by
  ext w
  simp only [dU', sub_apply, ofL2Ω, ContinuousLinearMap.coe_comp,
    Function.comp_apply, innerSLFlip_apply_apply, ofHL_apply]
  rw [swf D P t w, inner_sub_right]
  ring

theorem equation_dU (t : ℝ) (w : H10Ω (n + 1) Ω) :
    dU' D P t w + formΩ (n + 1) Ω (dB D P) t (dU D P t) w = ofL2Ω (n + 1) Ω (dF D P t) w := by
  rw [form_dU, dU']
  simp only [sub_apply, ofHL_apply]
  ring

/-! ### Differentiability in `H⁻¹(Ω)` -/

/-- A continuous function with continuous derivative off a countable set is differentiable
everywhere, by the fundamental theorem of calculus. -/
theorem hasDerivAt_of_off_countable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f f' : ℝ → E} (hf : Continuous f) (hf' : Continuous f') {s : Set ℝ}
    (hs : s.Countable) (hd : ∀ t ∉ s, HasDerivAt f (f' t) t) (t : ℝ) :
    HasDerivAt f (f' t) t := by
  have key : ∀ b, f b = f 0 + ∫ τ in (0 : ℝ)..b, f' τ := by
    intro b
    rw [integral_eq_of_hasDerivAt_off_countable f f' hs hf.continuousOn
      (fun x hx => hd x hx.2) (hf'.intervalIntegrable _ _)]
    abel
  have h := (hf'.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (f 0)
  rw [show f = fun b => f 0 + ∫ τ in (0 : ℝ)..b, f' τ from funext key]
  exact h

theorem hasDerivAt_ofH10_dU (t : ℝ) :
    HasDerivAt (fun s => ofH10Ω (n + 1) Ω (dU D P s)) (dU' D P t) t := by
  have hc : Continuous fun s => ofH10Ω (n + 1) Ω (dU D P s) :=
    (ofHL (valΩ (n + 1) Ω)).continuous.comp ((valΩ (n + 1) Ω).continuous.comp (continuous_dU D P))
  refine hasDerivAt_of_off_countable hc (continuous_dU' D P) (Set.countable_singleton
    (5 * P.r ^ 2 / 16)) (fun s hs => ?_) t
  rw [dU'_eq]
  have h := hasDerivAt_val_dU D P (t₀ := s) hs
  have h2 : HasDerivAt
      (fun s => (ofHL (valΩ (n + 1) Ω)).restrictScalars ℝ (valΩ (n + 1) Ω (dU D P s)))
      ((ofHL (valΩ (n + 1) Ω)).restrictScalars ℝ (dG D P s)) s :=
    ((ofHL (valΩ (n + 1) Ω)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h
  simpa only [ContinuousLinearMap.coe_restrictScalars', ← ofH10Ω_eq] using h2

/-! ### Norms, initial value, real values -/

/-- The constant `c_Q = ∫ Q²`. -/
def cQ : ℝ := ∫ y, Qr P.r P.p y ^ 2

theorem cQ_pos : 0 < cQ P := by
  have hQ := isBumpFn_Qr P.hr P.p
  have hc : Continuous fun y => Qr P.r P.p y ^ 2 := hQ.continuous.pow 2
  have hcs : HasCompactSupport fun y => Qr P.r P.p y ^ 2 :=
    HasCompactSupport.intro (isCompact_closedBall (tailL n P.p) P.r) fun y hy => by
      rw [Qr_eq_zero P.hr P.p hy]; ring
  have hnz : Qr P.r P.p (tailL n P.p) ^ 2 ≠ 0 := by rw [Qr_center]; norm_num
  show 0 < ∫ y, Qr P.r P.p y ^ 2
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun y => sq_nonneg _) hnz

theorem norm_dG_sq (t : ℝ) :
    ‖dG D P t‖ ^ 2 = cQ P * (P.r⁻¹ ^ 3 * utNormSq D P.ε (t / P.r ^ 2)) := by
  rw [dG, toL2Ω, norm_toLp_sq]
  have e1 : ∫ x in Ω, ‖(domWt D P.ε P.r P.p t x : ℂ)‖ ^ 2
      = ∫ x, URt D P.ε P.r (P.p 0) t (x 0) ^ 2 * Qr P.r P.p (tailL n x) ^ 2 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [domWt_eq_zero D P.ε P.p P.hr t (fun h => hx (P.hK h)), Complex.ofReal_zero, norm_zero,
        zero_pow two_ne_zero]]
    congr 1; funext x
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, domWt, tens, mul_pow]
  rw [e1, ← integral_comp_insE]
  simp only [insE_apply_zero, tailL_insE]
  rw [Measure.volume_eq_prod, integral_prod_mul (fun s => URt D P.ε P.r (P.p 0) t s ^ 2)
    (fun y => Qr P.r P.p y ^ 2), cQ, mul_comm]
  congr 1
  exact integral_sq_URt D P.ε P.hr (P.p 0) t

theorem dU_zero : dU D P 0 = 0 := by
  apply H10Ω.ext
  rw [H10Ω.pair_zero]
  have hz : ∀ x, (domW D P.ε P.r P.p 0 x : ℂ) = 0 := fun x => by
    rw [domW, tens, UR_initial, zero_mul, Complex.ofReal_zero]
  have h1 : toL2Ω Ω (fun x => (domW D P.ε P.r P.p 0 x : ℂ)) (isTest_dU D P 0).memLp = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [coe_toL2Ω _ (isTest_dU D P 0).memLp] with x hx
    rw [hx, hz]; rfl
  have h2 : toL2Ωvec Ω (grad fun x => (domW D P.ε P.r P.p 0 x : ℂ)) (isTest_dU D P 0).memLp_grad
      = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [coe_toL2Ωvec _ (isTest_dU D P 0).memLp_grad] with x hx
    rw [hx]
    have : (fun x => (domW D P.ε P.r P.p 0 x : ℂ)) = fun _ => 0 := funext hz
    rw [this]
    ext i
    simp [grad]
  show WithLp.toLp 2 (toL2Ω Ω _ (isTest_dU D P 0).memLp, toL2Ωvec Ω _ (isTest_dU D P 0).memLp_grad)
    = 0
  rw [h1, h2]
  rfl

theorem im_val_dU (t : ℝ) : ∀ᵐ x ∂(volume.restrict Ω), (valΩ (n + 1) Ω (dU D P t) x).im = 0 := by
  filter_upwards [coe_val_dU D P t] with x hx
  rw [hx, Complex.ofReal_im]

theorem im_dF (t : ℝ) : ∀ᵐ x ∂(volume.restrict Ω), (dF D P t x).im = 0 := by
  filter_upwards [coe_dF D P t] with x hx
  rw [hx, Complex.ofReal_im]

end LionsC12
