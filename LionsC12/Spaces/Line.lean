module

public import LionsC12.Lions.Complex
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The spaces `L²(U;ℂ)`, `H¹₀(U;ℂ)` and `H⁻¹(U;ℂ)` on the line

Facts about the statement-level spaces of `LionsC12.Paper.Statement` for `U ⊆ ℝ`:

* `norm_sq_H10` — `‖v‖² = ‖v‖²_{L²} + ‖∂ₓv‖²_{L²}`;
* `ofTest` — the element `(φ, φ')` of `H¹₀(U)` defined by `φ ∈ C¹_c(U;ℂ)`;
* `eq_zero_of_testGraph` — a continuous semilinear functional on `L²(U) × L²(U)` vanishing on the
  test graphs vanishes on `H¹₀(U)` (density of the test functions, by definition);
* `inner_dx_eq` — integration by parts in `H¹₀(U)`: `⟨∂ₓw, G⟩ = -⟨w, G'⟩` for `G ∈ C¹(ℝ;ℂ)`
  with `G, G'` square integrable on `U`, and no boundary condition on `G`;
* `ofL2_injective`, `val_injective`, `denseRange_val` — `L²(U) ↪ H⁻¹(U)` is injective, and
  `H¹₀(U) ↪ L²(U)` is injective with dense range, for `U` open: `(H¹₀, L², H⁻¹)` is a Gelfand
  triple;
* `ofC1Ioo` — a `C¹` function on `ℝ` vanishing outside `(a,b)` defines an element of
  `H¹₀((a,b))` (by dilation towards the centre of the interval).
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge
open scoped InnerProductSpace ComplexConjugate ContDiff ENNReal

variable {U : Set ℝ}

/-! ### Norms -/

/-- The graph `(v, ∂ₓv)` of an element of `H¹₀(U)`. -/
def H10.pair (v : H10 U) : WithLp 2 (L2 U × L2 U) :=
  @Subtype.val _ (fun x => x ∈ H10Graph U) v

/-- The element of `H¹₀(U)` with a given graph. -/
def H10.mk (p : WithLp 2 (L2 U × L2 U)) (hp : p ∈ H10Graph U) : H10 U :=
  (⟨p, hp⟩ : {x // x ∈ H10Graph U})

theorem H10.pair_mk (p : WithLp 2 (L2 U × L2 U)) (hp : p ∈ H10Graph U) :
    H10.pair (H10.mk p hp) = p := rfl

theorem H10.pair_mem (v : H10 U) : (H10.pair v) ∈ H10Graph U :=
  @Subtype.property _ (fun x => x ∈ H10Graph U) v

theorem H10.ext {v w : H10 U} (h : (H10.pair v) = (H10.pair w)) : v = w :=
  Subtype.ext (p := fun x => x ∈ H10Graph U) h

theorem val_apply (v : H10 U) : val U v = (WithLp.ofLp (H10.pair v)).1 := rfl

theorem dx_apply (v : H10 U) : dx U v = (WithLp.ofLp (H10.pair v)).2 := rfl

theorem H10.norm_eq (v : H10 U) : ‖v‖ = ‖(H10.pair v)‖ := rfl

theorem H10.pair_sub (v w : H10 U) : H10.pair (v - w) = (H10.pair v) - (H10.pair w) := rfl

theorem norm_sq_H10 (v : H10 U) : ‖v‖ ^ 2 = ‖val U v‖ ^ 2 + ‖dx U v‖ ^ 2 := by
  have := WithLp.prod_norm_sq_eq_of_L2 (H10.pair v)
  rw [H10.norm_eq, this]
  rfl

theorem norm_val_le (v : H10 U) : ‖val U v‖ ≤ ‖v‖ := by
  have h := norm_sq_H10 v
  nlinarith [norm_nonneg (val U v), norm_nonneg (dx U v), norm_nonneg v, sq_nonneg ‖dx U v‖]

theorem norm_dx_le (v : H10 U) : ‖dx U v‖ ≤ ‖v‖ := by
  have h := norm_sq_H10 v
  nlinarith [norm_nonneg (val U v), norm_nonneg (dx U v), norm_nonneg v, sq_nonneg ‖val U v‖]

/-! ### Test functions -/

/-- The class in `L²(U;ℂ)` of a function that is square integrable on `U`. -/
def toL2 (U : Set ℝ) (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict U)) : L2 U := hg.toLp g

theorem coe_toL2 (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict U)) :
    ⇑(toL2 U g hg) =ᵐ[volume.restrict U] g := hg.coeFn_toLp

/-- The data of a test function `φ ∈ C¹_c(U;ℂ)`. -/
structure IsTestFun (U : Set ℝ) (φ : ℝ → ℂ) : Prop where
  contDiff : ContDiff ℝ 1 φ
  hasCompactSupport : HasCompactSupport φ
  tsupport_subset : tsupport φ ⊆ U

namespace IsTestFun

variable {φ : ℝ → ℂ}

theorem continuous (h : IsTestFun U φ) : Continuous φ := h.contDiff.continuous

theorem continuous_deriv (h : IsTestFun U φ) : Continuous (deriv φ) :=
  h.contDiff.continuous_deriv_one

theorem hasDerivAt (h : IsTestFun U φ) (x : ℝ) : HasDerivAt φ (deriv φ x) x :=
  (h.contDiff.differentiable one_ne_zero x).hasDerivAt

theorem hasCompactSupport_deriv (h : IsTestFun U φ) : HasCompactSupport (deriv φ) :=
  h.hasCompactSupport.deriv

theorem memLp (h : IsTestFun U φ) : MemLp φ 2 (volume.restrict U) :=
  (h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport).restrict U

theorem memLp_deriv (h : IsTestFun U φ) : MemLp (deriv φ) 2 (volume.restrict U) :=
  (h.continuous_deriv.memLp_of_hasCompactSupport h.hasCompactSupport_deriv).restrict U

theorem eq_zero_of_notMem (h : IsTestFun U φ) {x : ℝ} (hx : x ∉ U) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h' => hx (h.tsupport_subset h')

theorem deriv_eq_zero_of_notMem (h : IsTestFun U φ) {x : ℝ} (hx : x ∉ U) : deriv φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h' => hx (h.tsupport_subset (tsupport_deriv_subset h'))

/-- A real `C^∞_c` function, as a complex test function. -/
theorem ofReal {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ U) : IsTestFun U (fun x => (ψ x : ℂ)) where
  contDiff := (Complex.ofRealCLM.contDiff.comp hψ).of_le (by exact_mod_cast le_top)
  hasCompactSupport := hc.comp_left Complex.ofReal_zero
  tsupport_subset := (tsupport_comp_subset Complex.ofReal_zero ψ).trans hs

end IsTestFun

theorem mem_testGraph {φ : ℝ → ℂ} (hφ : IsTestFun U φ) :
    WithLp.toLp 2 (toL2 U φ hφ.memLp, toL2 U (deriv φ) hφ.memLp_deriv) ∈ testGraph U :=
  ⟨φ, hφ.contDiff, hφ.hasCompactSupport, hφ.tsupport_subset, coe_toL2 φ hφ.memLp,
    coe_toL2 (deriv φ) hφ.memLp_deriv⟩

theorem testGraph_subset_H10 : testGraph U ⊆ H10Graph U :=
  (Submodule.subset_span).trans (Submodule.le_topologicalClosure _)

/-- The element `(φ, φ')` of `H¹₀(U;ℂ)` defined by a test function `φ ∈ C¹_c(U;ℂ)`. -/
def ofTest {φ : ℝ → ℂ} (hφ : IsTestFun U φ) : H10 U :=
  H10.mk (WithLp.toLp 2 (toL2 U φ hφ.memLp, toL2 U (deriv φ) hφ.memLp_deriv))
    (testGraph_subset_H10 (mem_testGraph hφ))

theorem val_ofTest {φ : ℝ → ℂ} (hφ : IsTestFun U φ) :
    ⇑(val U (ofTest hφ)) =ᵐ[volume.restrict U] φ := coe_toL2 φ hφ.memLp

theorem dx_ofTest {φ : ℝ → ℂ} (hφ : IsTestFun U φ) :
    ⇑(dx U (ofTest hφ)) =ᵐ[volume.restrict U] deriv φ := coe_toL2 (deriv φ) hφ.memLp_deriv

/-- A continuous semilinear map on `L²(U) × L²(U)` that vanishes on the test graphs vanishes on
`H¹₀(U)`. -/
theorem eq_zero_of_testGraph {σ : ℂ →+* ℂ} {F : Type*} [NormedAddCommGroup F] [Module ℂ F]
    (Λ : WithLp 2 (L2 U × L2 U) →SL[σ] F) (h : ∀ p ∈ testGraph U, Λ p = 0) (v : H10 U) :
    Λ (H10.pair v) = 0 := by
  have hle : H10Graph U ≤ LinearMap.ker (Λ : WithLp 2 (L2 U × L2 U) →ₛₗ[σ] F) :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 fun p hp => h p hp)
      (ContinuousLinearMap.isClosed_ker Λ)
  exact hle (H10.pair_mem v)

/-! ### Integration by parts -/

/-- A compactly supported function on `ℝ` vanishes outside some interval `[-R, R]`. -/
theorem exists_Icc_of_hasCompactSupport {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∀ x, x ∉ Ioo (-R) R → f x = 0 := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨|R| + 1, by positivity, fun x hx => image_eq_zero_of_notMem_tsupport fun h' => hx ?_⟩
  have := hR h'
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  constructor <;> [linarith [neg_abs_le x, le_abs_self R]; linarith [le_abs_self x, le_abs_self R]]

/-- Integration by parts on the line against a test function:
`∫ conj(φ') G = -∫ conj(φ) G'` for `φ ∈ C¹_c` and `G ∈ C¹`. -/
theorem integral_conj_deriv_mul {φ : ℝ → ℂ} (hφ : IsTestFun U φ) {G g : ℝ → ℂ}
    (hG : ∀ x, HasDerivAt G (g x) x) (hg : Continuous g) :
    ∫ x, conj (deriv φ x) * G x = -∫ x, conj (φ x) * g x := by
  obtain ⟨R, hR, hRφ⟩ := exists_Icc_of_hasCompactSupport hφ.hasCompactSupport
  have hφ' : ∀ x, x ∉ Ioo (-R) R → deriv φ x = 0 := by
    intro x hx
    obtain ⟨R', -, hR'⟩ := exists_Icc_of_hasCompactSupport hφ.hasCompactSupport_deriv
    by_contra hne
    have hx' : x ∈ tsupport (deriv φ) := subset_tsupport _ hne
    have := tsupport_deriv_subset hx'
    have hxs : x ∈ tsupport φ := this
    -- `tsupport φ` lies in the closed interval `[-R, R]`; on its boundary `φ` vanishes nearby
    have hcl : tsupport φ ⊆ Icc (-R) R := by
      refine closure_minimal (fun y hy => ?_) isClosed_Icc
      by_contra hy'
      exact hy (hRφ y fun h => hy' (Ioo_subset_Icc_self h))
    have hxI := hcl hxs
    have hbd : x = -R ∨ x = R := by
      rcases eq_or_lt_of_le hxI.1 with h | h
      · exact Or.inl h.symm
      rcases eq_or_lt_of_le hxI.2 with h' | h'
      · exact Or.inr h'
      exact absurd ⟨h, h'⟩ hx
    -- near `±R`, `φ` vanishes on one side; derivative at a boundary point of the support
    have hzero : ∀ᶠ y in 𝓝 x, φ y = 0 ∨ y ∈ Ioo (-R) R := by
      filter_upwards with y
      by_cases hy : y ∈ Ioo (-R) R
      · exact Or.inr hy
      · exact Or.inl (hRφ y hy)
    -- the derivative of `φ` at `x` vanishes since `φ` has a local extremum of `‖φ‖`? use limits
    have hcont := hφ.continuous_deriv
    have hd0 : ∀ y, y ∉ Icc (-R) R → deriv φ y = 0 := by
      intro y hy
      have hev : φ =ᶠ[𝓝 y] fun _ => 0 := by
        have : (Icc (-R) R)ᶜ ∈ 𝓝 y := isClosed_Icc.isOpen_compl.mem_nhds hy
        filter_upwards [this] with z hz
        exact hRφ z fun h => hz (Ioo_subset_Icc_self h)
      rw [hev.deriv_eq]; simp
    have hclos : x ∈ closure (Icc (-R) R)ᶜ := by
      rcases hbd with h | h
      · rw [h]
        have : Tendsto (fun n : ℕ => -R - 1 / ((n : ℝ) + 1)) atTop (𝓝 (-R)) := by
          have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (-R)
          simpa using this
        exact mem_closure_of_tendsto this (Eventually.of_forall fun n => by
          simp only [mem_compl_iff, mem_Icc, not_and_or, not_le]
          left; have : 0 < 1 / ((n : ℝ) + 1) := by positivity
          linarith)
      · rw [h]
        have : Tendsto (fun n : ℕ => R + 1 / ((n : ℝ) + 1)) atTop (𝓝 R) := by
          have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add R
          simpa using this
        exact mem_closure_of_tendsto this (Eventually.of_forall fun n => by
          simp only [mem_compl_iff, mem_Icc, not_and_or, not_le]
          right; have : 0 < 1 / ((n : ℝ) + 1) := by positivity
          linarith)
    have : deriv φ x = 0 :=
      (isClosed_eq hcont continuous_const).closure_subset_iff.2 (fun y hy => hd0 y hy) hclos
    exact hne this
  have e1 : ∫ x, conj (deriv φ x) * G x = ∫ x in (-(R + 1))..(R + 1), conj (deriv φ x) * G x := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo (-(R + 1)) (R + 1))]
    intro x hx
    rw [hφ' x fun h => hx ⟨by linarith [h.1], by linarith [h.2]⟩, map_zero, zero_mul]
  have e2 : ∫ x, conj (φ x) * g x = ∫ x in (-(R + 1))..(R + 1), conj (φ x) * g x := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo (-(R + 1)) (R + 1))]
    intro x hx
    rw [hRφ x fun h => hx ⟨by linarith [h.1], by linarith [h.2]⟩, map_zero, zero_mul]
  have hconj : ∀ x, HasDerivAt (fun y => conj (φ y)) (conj (deriv φ x)) x :=
    fun x => (hφ.hasDerivAt x).star
  have hIBP := intervalIntegral.integral_deriv_mul_eq_sub (a := -(R + 1)) (b := R + 1)
    (fun x _ => hconj x) (fun x _ => hG x)
    ((hφ.continuous_deriv.star).intervalIntegrable _ _) (hg.intervalIntegrable _ _)
  rw [hRφ (-(R + 1)) (fun h => by linarith [h.1]), hRφ (R + 1) (fun h => by linarith [h.2]),
    map_zero, zero_mul, zero_mul, sub_zero] at hIBP
  have hi1 : IntervalIntegrable (fun x => conj (deriv φ x) * G x) volume (-(R + 1)) (R + 1) :=
    ((hφ.continuous_deriv.star).mul (continuous_iff_continuousAt.2
      fun x => (hG x).continuousAt)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => conj (φ x) * g x) volume (-(R + 1)) (R + 1) :=
    ((hφ.continuous.star).mul hg).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2] at hIBP
  rw [e1, e2]
  exact eq_neg_of_add_eq_zero_left hIBP

theorem integral_restrict_test {φ : ℝ → ℂ} (hφ : IsTestFun U φ) (F : ℝ → ℂ) :
    ∫ x in U, conj (φ x) * F x = ∫ x, conj (φ x) * F x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [hφ.eq_zero_of_notMem hx, map_zero, zero_mul]

theorem integral_restrict_test_deriv {φ : ℝ → ℂ} (hφ : IsTestFun U φ) (F : ℝ → ℂ) :
    ∫ x in U, conj (deriv φ x) * F x = ∫ x, conj (deriv φ x) * F x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [hφ.deriv_eq_zero_of_notMem hx, map_zero, zero_mul]

theorem inner_L2_eq (f g : L2 U) : ⟪f, g⟫_ℂ = ∫ x in U, conj (f x) * g x := by
  rw [MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply, mul_comm]

/-- **Integration by parts in `H¹₀(U)`**: `⟨∂ₓw, G⟩ = -⟨w, G'⟩` for every `w ∈ H¹₀(U)` and every
`G ∈ C¹(ℝ;ℂ)` with `G, G'` square integrable on `U`.  No boundary condition is imposed on `G`:
the boundary terms vanish on the test functions, which are dense in `H¹₀(U)`. -/
theorem inner_dx_eq {G g : ℝ → ℂ} (hG : ∀ x, HasDerivAt G (g x) x)
    (hg : Continuous g) (hG2 : MemLp G 2 (volume.restrict U)) (hg2 : MemLp g 2 (volume.restrict U))
    (w : H10 U) : ⟪dx U w, toL2 U G hG2⟫_ℂ = -⟪val U w, toL2 U g hg2⟫_ℂ := by
  set Λ : WithLp 2 (L2 U × L2 U) →L⋆[ℂ] ℂ :=
    (innerSLFlip ℂ (toL2 U G hG2)).comp (WithLp.sndL 2 ℂ (L2 U) (L2 U)) +
      (innerSLFlip ℂ (toL2 U g hg2)).comp (WithLp.fstL 2 ℂ (L2 U) (L2 U)) with hΛ
  have h0 : ∀ p ∈ testGraph U, Λ p = 0 := by
    rintro p ⟨φ, hc, hcs, hsub, h1, h2⟩
    have hφ : IsTestFun U φ := ⟨hc, hcs, hsub⟩
    simp only [hΛ, add_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, innerSLFlip_apply_apply, WithLp.sndL_apply, WithLp.fstL_apply]
    rw [inner_L2_eq, inner_L2_eq]
    have e1 : ∫ x in U, conj (p.snd x) * toL2 U G hG2 x
        = ∫ x in U, conj (deriv φ x) * G x := by
      refine integral_congr_ae ?_
      filter_upwards [h2, coe_toL2 G hG2] with x hx hx'
      change conj ((WithLp.ofLp p).2 x) * _ = _
      rw [hx, hx']
    have e2 : ∫ x in U, conj (p.fst x) * toL2 U g hg2 x
        = ∫ x in U, conj (φ x) * g x := by
      refine integral_congr_ae ?_
      filter_upwards [h1, coe_toL2 g hg2] with x hx hx'
      change conj ((WithLp.ofLp p).1 x) * _ = _
      rw [hx, hx']
    rw [e1, e2, integral_restrict_test_deriv hφ, integral_restrict_test hφ,
      integral_conj_deriv_mul hφ hG hg, neg_add_cancel]
  have := eq_zero_of_testGraph Λ h0 w
  simp only [hΛ, add_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, innerSLFlip_apply_apply, WithLp.sndL_apply, WithLp.fstL_apply] at this
  exact eq_neg_of_add_eq_zero_left this

/-! ### The Gelfand triple -/

/-- An element of `L²(U)`, `U` open, orthogonal to every real `C^∞_c(U)` function vanishes. -/
theorem eq_zero_of_forall_smooth (hU : IsOpen U) (h : L2 U)
    (H : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x in U, (ψ x : ℂ) * h x = 0) : h = 0 := by
  have hloc : LocallyIntegrableOn (⇑h) U volume := by
    rw [locallyIntegrableOn_iff hU.isLocallyClosed]
    intro K hKU hK
    have hfin : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_ne_top
    have h2 : MemLp (⇑h) 2 (volume.restrict K) :=
      (Lp.memLp h).mono_measure (Measure.restrict_mono hKU le_rfl)
    exact h2.integrable one_le_two
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun ψ hψ hc hs => by
    have := H ψ hψ hc hs
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)]
    · simpa [Complex.real_smul] using this
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport fun h' => hx (hs h'), zero_smul])
  rw [Lp.eq_zero_iff_ae_eq_zero]
  rw [EventuallyEq, ae_restrict_iff' hU.measurableSet]
  filter_upwards [hae] with x hx hxU
  simpa using hx hxU

/-- `L²(U) ↪ H⁻¹(U)` is injective, `U` open. -/
theorem ofL2_injective (hU : IsOpen U) : Function.Injective (ofL2 U) := by
  intro h h' heq
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_smooth hU _ fun ψ hψ hc hs => ?_
  have hψ' := IsTestFun.ofReal hψ hc hs
  have e : ofL2 U h (ofTest hψ') - ofL2 U h' (ofTest hψ') = 0 := by rw [heq, sub_self]
  simp only [ofL2, ContinuousLinearMap.coe_comp, Function.comp_apply,
    innerSLFlip_apply_apply] at e
  rw [← inner_sub_right, inner_L2_eq] at e
  rw [← e]
  refine integral_congr_ae ?_
  filter_upwards [val_ofTest hψ'] with x hx
  rw [hx, Complex.conj_ofReal]

/-- The weak derivative of an element of `H¹₀(U)` is determined by the element, `U` open:
`H¹₀(U) ↪ L²(U)` is injective. -/
theorem val_injective (hU : IsOpen U) : Function.Injective (val U) := by
  intro w w' heq
  rw [← sub_eq_zero] at heq ⊢
  rw [← map_sub] at heq
  set v := w - w'
  have hdx : dx U v = 0 := by
    refine eq_zero_of_forall_smooth hU _ fun ψ hψ hc hs => ?_
    have hψ' := IsTestFun.ofReal hψ hc hs
    have hG : ∀ x, HasDerivAt (fun y => (ψ y : ℂ)) ((deriv ψ x : ℝ) : ℂ) x := fun x =>
      ((hψ.differentiable (by simp) x).hasDerivAt).ofReal_comp
    have hg : Continuous fun x => ((deriv ψ x : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (hψ.continuous_deriv (by simp))
    have hgm : MemLp (fun x => ((deriv ψ x : ℝ) : ℂ)) 2 (volume.restrict U) :=
      (hg.memLp_of_hasCompactSupport (hc.deriv.comp_left Complex.ofReal_zero)).restrict U
    have key := inner_dx_eq hG hg hψ'.memLp hgm v
    rw [heq, inner_zero_left, neg_zero, inner_L2_eq] at key
    have : ∫ x in U, conj ((ψ x : ℂ) * dx U v x) = 0 := by
      rw [← key]
      refine integral_congr_ae ?_
      filter_upwards [coe_toL2 (fun y => (ψ y : ℂ)) hψ'.memLp] with x hx
      rw [hx, map_mul, Complex.conj_ofReal, mul_comm]
    rw [integral_conj] at this
    simpa using this
  apply H10.ext
  have h1 : (H10.pair v) = WithLp.toLp 2 (val U v, dx U v) := rfl
  rw [h1, heq, hdx]
  rfl

/-- `H¹₀(U) ↪ L²(U)` has dense range, `U` open. -/
theorem denseRange_val (hU : IsOpen U) : DenseRange (val U) := by
  have : (LinearMap.range (val U : H10 U →ₗ[ℂ] L2 U)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro h hh
    apply ofL2_injective hU
    ext w
    rw [Submodule.mem_orthogonal'] at hh
    have := hh (val U w) ⟨w, rfl⟩
    simp only [ofL2, ContinuousLinearMap.coe_comp, Function.comp_apply, innerSLFlip_apply_apply,
      map_zero, zero_apply]
    rw [← inner_conj_symm, this, map_zero]
  have hd := (Submodule.dense_iff_topologicalClosure_eq_top).2 this
  exact hd

/-! ### `C¹` functions vanishing outside a bounded interval -/

section Dilation

variable {a b : ℝ}

/-- A continuous function is square integrable on a bounded interval. -/
theorem memLp_Ioo_of_continuous {g : ℝ → ℂ} (hg : Continuous g) :
    MemLp g 2 (volume.restrict (Ioo a b)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    hg.continuousOn
  refine MemLp.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hC x (Ioo_subset_Icc_self hx)

/-- Uniform convergence on `(a,b)` gives convergence in `L²((a,b))`. -/
theorem tendsto_toL2_of_uniform {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hF : ∀ n, MemLp (F n) 2 (volume.restrict (Ioo a b)))
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (h : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ Ioo a b, ‖F n x - f x‖ ≤ ε) :
    Tendsto (fun n => toL2 (Ioo a b) (F n) (hF n)) atTop (𝓝 (toL2 (Ioo a b) f hf)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set M : ℝ := (measureUnivNNReal (volume.restrict (Ioo a b)) : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹
  have hM : 0 ≤ M := by positivity
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h (δ / (2 * (M + 1))) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_norm]
  have hsub : toL2 (Ioo a b) (F n) (hF n) - toL2 (Ioo a b) f hf
      = toL2 (Ioo a b) (fun x => F n x - f x) ((hF n).sub hf) := by
    simp only [toL2]
    rw [← MemLp.toLp_sub]
    rfl
  rw [hsub]
  have hle : ‖toL2 (Ioo a b) (fun x => F n x - f x) ((hF n).sub hf)‖
      ≤ M * (δ / (2 * (M + 1))) := by
    refine Lp.norm_le_of_ae_bound (by positivity) ?_
    filter_upwards [coe_toL2 (fun x => F n x - f x) ((hF n).sub hf),
      ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [hx]
    exact hN n hn x hxI
  calc _ ≤ M * (δ / (2 * (M + 1))) := hle
    _ < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

/-- The dilation `x ↦ c + (x - c)/λ` towards the centre `c = (a+b)/2`. -/
def dil (a b l : ℝ) (x : ℝ) : ℝ := (a + b) / 2 + (x - (a + b) / 2) / l

theorem hasDerivAt_dil (a b : ℝ) {l : ℝ} (x : ℝ) : HasDerivAt (dil a b l) (1 / l) x := by
  have h1 : HasDerivAt (fun x : ℝ => x - (a + b) / 2) 1 x := (hasDerivAt_id x).sub_const _
  exact (h1.div_const l).const_add ((a + b) / 2)

theorem contDiff_dil (a b l : ℝ) : ContDiff ℝ ⊤ (dil a b l) := by
  unfold dil; fun_prop

theorem abs_dil_sub_le {l : ℝ} (hl : 0 < l) {x : ℝ} (hx : x ∈ Ioo a b) :
    |dil a b l x - x| ≤ (b - a) / 2 * |1 / l - 1| := by
  have : dil a b l x - x = (x - (a + b) / 2) * (1 / l - 1) := by
    unfold dil; field_simp; ring
  rw [this, abs_mul]
  gcongr
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-- The dilated function `φ_λ(x) = φ(c + (x - c)/λ)` of a `C¹` function vanishing outside
`(a,b)` is a test function on `(a,b)` for `0 < λ < 1`. -/
theorem isTestFun_dil (hab : a < b) {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (h0 : ∀ x ∉ Ioo a b, φ x = 0) {l : ℝ} (hl : 0 < l) (hl1 : l < 1) :
    IsTestFun (Ioo a b) (fun x => φ (dil a b l x)) := by
  set c := (a + b) / 2 with hc
  have hsupp : ∀ x, x ∉ Icc (c - l * ((b - a) / 2)) (c + l * ((b - a) / 2)) →
      φ (dil a b l x) = 0 := by
    intro x hx
    apply h0
    rintro ⟨h1, h2⟩
    apply hx
    have e : dil a b l x - c = (x - c) / l := by simp [dil, c]
    have h1' : -((b - a) / 2) < (x - c) / l := by rw [← e]; simp only [c]; linarith
    have h2' : (x - c) / l < (b - a) / 2 := by rw [← e]; simp only [c]; linarith
    rw [lt_div_iff₀ hl] at h1'
    rw [div_lt_iff₀ hl] at h2'
    constructor <;> nlinarith
  refine ⟨hφ.comp ((contDiff_dil a b l).of_le le_top), ?_, ?_⟩
  · exact HasCompactSupport.intro isCompact_Icc hsupp
  · refine (closure_minimal (t := Icc (c - l * ((b - a) / 2)) (c + l * ((b - a) / 2)))
      (fun x hx => ?_) isClosed_Icc).trans ?_
    · by_contra hx'; exact hx (hsupp x hx')
    · intro x hx
      have hba : 0 < b - a := by linarith
      have : l * ((b - a) / 2) < (b - a) / 2 := by nlinarith
      constructor
      · linarith [hx.1]
      · linarith [hx.2]

theorem deriv_dil_comp {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {l : ℝ} (x : ℝ) :
    deriv (fun y => φ (dil a b l y)) x = (1 / l) • deriv φ (dil a b l x) := by
  have hd := ((hφ.differentiable one_ne_zero (dil a b l x)).hasDerivAt).scomp x
    (hasDerivAt_dil a b (l := l) x)
  exact hd.deriv

/-- **`C¹` functions vanishing outside `(a,b)` belong to `H¹₀((a,b))`.**  They are the limits,
in the graph norm, of their dilations towards the centre of the interval, which are test
functions. -/
theorem mem_H10_Ioo (hab : a < b) {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (h0 : ∀ x ∉ Ioo a b, φ x = 0) :
    WithLp.toLp 2 (toL2 (Ioo a b) φ (memLp_Ioo_of_continuous hφ.continuous),
      toL2 (Ioo a b) (deriv φ) (memLp_Ioo_of_continuous hφ.continuous_deriv_one))
      ∈ H10Graph (Ioo a b) := by
  set l : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hldef
  have hl : ∀ n, 0 < l n := fun n => by
    have : 1 / ((n : ℝ) + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
    simp only [hldef]; linarith
  have hl1 : ∀ n, l n < 1 := fun n => by
    simp only [hldef]
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hinv : ∀ n, 1 / l n - 1 = 1 / ((n : ℝ) + 1) := fun n => by
    have h1 : (n : ℝ) + 2 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 ≠ 0 := by positivity
    have e : l n = ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
      simp only [hldef]; field_simp; ring
    rw [e, one_div_div]
    field_simp
    ring
  have htest : ∀ n, IsTestFun (Ioo a b) (fun x => φ (dil a b (l n) x)) :=
    fun n => isTestFun_dil hab hφ h0 (hl n) (hl1 n)
  -- uniform continuity of `φ` and `φ'`
  have hcs : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun x hx =>
    h0 x fun h => hx (Ioo_subset_Icc_self h)
  have huc : UniformContinuous φ := hcs.uniformContinuous_of_continuous hφ.continuous
  have huc' : UniformContinuous (deriv φ) :=
    hcs.deriv.uniformContinuous_of_continuous hφ.continuous_deriv_one
  obtain ⟨M, hM⟩ := hφ.continuous_deriv_one.bounded_above_of_compact_support hcs.deriv
  have hsmall : ∀ δ > 0, ∀ᶠ n : ℕ in atTop, (b - a) / 2 * |1 / l n - 1| < δ := by
    intro δ hδ
    have ht : Tendsto (fun n : ℕ => (b - a) / 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((b - a) / 2)
    filter_upwards [ht.eventually (gt_mem_nhds hδ)] with n hn
    rw [hinv, abs_of_pos (by positivity)]
    exact hn
  have hconv1 : Tendsto (fun n => toL2 (Ioo a b) _ (htest n).memLp) atTop
      (𝓝 (toL2 (Ioo a b) φ (memLp_Ioo_of_continuous hφ.continuous))) := by
    refine tendsto_toL2_of_uniform _ _ fun ε hε => ?_
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.1 huc ε hε
    filter_upwards [hsmall δ hδ] with n hn x hx
    have := @hδε (dil a b (l n) x) x (by
      rw [Real.dist_eq]; exact lt_of_le_of_lt (abs_dil_sub_le (hl n) hx) hn)
    rw [dist_eq_norm] at this
    exact this.le
  have hconv2 : Tendsto (fun n => toL2 (Ioo a b) _ (htest n).memLp_deriv) atTop
      (𝓝 (toL2 (Ioo a b) (deriv φ) (memLp_Ioo_of_continuous hφ.continuous_deriv_one))) := by
    refine tendsto_toL2_of_uniform _ _ fun ε hε => ?_
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.1 huc' (ε / 2) (by positivity)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    filter_upwards [hsmall δ hδ, hsmall (ε / (2 * (M + 1)) * ((b - a) / 2)) (by
      have : 0 < b - a := by linarith
      positivity)] with n hn hn' x hx
    rw [deriv_dil_comp hφ]
    have e : (1 / l n) • deriv φ (dil a b (l n) x) - deriv φ x
        = (1 / l n - 1) • deriv φ (dil a b (l n) x)
          + (deriv φ (dil a b (l n) x) - deriv φ x) := by
      rw [sub_smul, one_smul]; abel
    rw [e]
    have h1 : ‖(1 / l n - 1) • deriv φ (dil a b (l n) x)‖ ≤ ε / 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      have hba : 0 < (b - a) / 2 := by linarith
      have hlt : |1 / l n - 1| < ε / (2 * (M + 1)) := by
        have := hn'
        rw [mul_comm] at this
        exact lt_of_mul_lt_mul_left
          (by linarith [mul_comm ((b - a) / 2) (ε / (2 * (M + 1)))]) hba.le
      calc |1 / l n - 1| * ‖deriv φ (dil a b (l n) x)‖ ≤ ε / (2 * (M + 1)) * M := by
            gcongr; exact hM _
        _ ≤ ε / 2 := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
    have h2 : ‖deriv φ (dil a b (l n) x) - deriv φ x‖ ≤ ε / 2 := by
      have := @hδε (dil a b (l n) x) x (by
        rw [Real.dist_eq]; exact lt_of_le_of_lt (abs_dil_sub_le (hl n) hx) hn)
      rw [dist_eq_norm] at this
      exact this.le
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
      _ = ε := by ring
  have hpair : Tendsto (fun n => WithLp.toLp 2 (toL2 (Ioo a b) _ (htest n).memLp,
      toL2 (Ioo a b) _ (htest n).memLp_deriv)) atTop
      (𝓝 (WithLp.toLp 2 (toL2 (Ioo a b) φ (memLp_Ioo_of_continuous hφ.continuous),
        toL2 (Ioo a b) (deriv φ) (memLp_Ioo_of_continuous hφ.continuous_deriv_one)))) :=
    ((WithLp.prodContinuousLinearEquiv 2 ℂ (L2 (Ioo a b)) (L2 (Ioo a b))).symm.continuous.tendsto
      _).comp (hconv1.prodMk_nhds hconv2)
  exact (Submodule.span ℂ (testGraph (Ioo a b))).isClosed_topologicalClosure.mem_of_tendsto hpair
    (Eventually.of_forall fun n => testGraph_subset_H10 (mem_testGraph (htest n)))

/-- The element of `H¹₀((a,b))` defined by a `C¹` function vanishing outside `(a,b)`. -/
def ofC1Ioo (hab : a < b) {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) (h0 : ∀ x ∉ Ioo a b, φ x = 0) :
    H10 (Ioo a b) :=
  H10.mk _ (mem_H10_Ioo hab hφ h0)

theorem val_ofC1Ioo (hab : a < b) {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (h0 : ∀ x ∉ Ioo a b, φ x = 0) :
    ⇑(val (Ioo a b) (ofC1Ioo hab hφ h0)) =ᵐ[volume.restrict (Ioo a b)] φ :=
  coe_toL2 φ (memLp_Ioo_of_continuous hφ.continuous)

theorem dx_ofC1Ioo (hab : a < b) {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (h0 : ∀ x ∉ Ioo a b, φ x = 0) :
    ⇑(dx (Ioo a b) (ofC1Ioo hab hφ h0)) =ᵐ[volume.restrict (Ioo a b)] deriv φ :=
  coe_toL2 (deriv φ) (memLp_Ioo_of_continuous hφ.continuous_deriv_one)

end Dilation

end LionsC12
