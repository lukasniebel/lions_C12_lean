module

public import LionsC12.Spaces.Forms
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The spaces `L²(Ω;ℂ)`, `H¹₀(Ω;ℂ)` and `H⁻¹(Ω;ℂ)` on a domain `Ω ⊆ ℝ^d`

The `d`-dimensional analogue of `LionsC12.Spaces.Line` and `LionsC12.Spaces.Forms`, for the
statement-level spaces `L2Ω`, `H10Ω`, `Hm1Ω` of `LionsC12.Paper.Statement`:

* `norm_sq_H10Ω` — `‖v‖² = ‖v‖²_{L²} + ‖∇v‖²_{L²}`;
* `ofTestΩ` — the element `(φ, ∇φ)` of `H¹₀(Ω)` defined by `φ ∈ C¹_c(Ω;ℂ)`;
* `eq_zero_of_testGraphΩ` — density of the test functions (by definition of the closure);
* `inner_gradΩ_single` — integration by parts against a smooth test function;
* `ofL2Ω_injective`, `valΩ_injective`, `denseRange_valΩ` — `(H¹₀(Ω), L²(Ω), H⁻¹(Ω))` is a
  Gelfand triple for `Ω` open;
* `formΩ_sub`, `formΩ_self_re_nonneg` and `isLionsSolutionΩ_unique` — uniqueness of the Lions
  variational solution for a bounded measurable nonnegative scalar coefficient.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge
open scoped InnerProductSpace ComplexConjugate ContDiff ENNReal

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Norms -/

/-- The graph `(v, ∇v)` of an element of `H¹₀(Ω)`. -/
def H10Ω.pair (v : H10Ω d Ω) : WithLp 2 (L2Ω d Ω × L2Ωvec d Ω) :=
  @Subtype.val _ (fun x => x ∈ H10ΩGraph d Ω) v

/-- The element of `H¹₀(Ω)` with a given graph. -/
def H10Ω.mk (p : WithLp 2 (L2Ω d Ω × L2Ωvec d Ω)) (hp : p ∈ H10ΩGraph d Ω) : H10Ω d Ω :=
  (⟨p, hp⟩ : {x // x ∈ H10ΩGraph d Ω})

theorem H10Ω.pair_mk (p : WithLp 2 (L2Ω d Ω × L2Ωvec d Ω)) (hp : p ∈ H10ΩGraph d Ω) :
    H10Ω.pair (H10Ω.mk p hp) = p := rfl

theorem H10Ω.pair_mem (v : H10Ω d Ω) : H10Ω.pair v ∈ H10ΩGraph d Ω :=
  @Subtype.property _ (fun x => x ∈ H10ΩGraph d Ω) v

theorem H10Ω.ext {v w : H10Ω d Ω} (h : H10Ω.pair v = H10Ω.pair w) : v = w :=
  Subtype.ext (p := fun x => x ∈ H10ΩGraph d Ω) h

theorem valΩ_apply (v : H10Ω d Ω) : valΩ d Ω v = (WithLp.ofLp (H10Ω.pair v)).1 := rfl

theorem gradΩ_apply (v : H10Ω d Ω) : gradΩ d Ω v = (WithLp.ofLp (H10Ω.pair v)).2 := rfl

theorem H10Ω.norm_eq (v : H10Ω d Ω) : ‖v‖ = ‖H10Ω.pair v‖ := rfl

theorem H10Ω.pair_sub (v w : H10Ω d Ω) : H10Ω.pair (v - w) = H10Ω.pair v - H10Ω.pair w := rfl

theorem H10Ω.pair_zero : H10Ω.pair (0 : H10Ω d Ω) = 0 := rfl

theorem norm_sq_H10Ω (v : H10Ω d Ω) : ‖v‖ ^ 2 = ‖valΩ d Ω v‖ ^ 2 + ‖gradΩ d Ω v‖ ^ 2 := by
  have := WithLp.prod_norm_sq_eq_of_L2 (H10Ω.pair v)
  rw [H10Ω.norm_eq, this]
  rfl

theorem norm_gradΩ_le (v : H10Ω d Ω) : ‖gradΩ d Ω v‖ ≤ ‖v‖ := by
  have h := norm_sq_H10Ω v
  nlinarith [norm_nonneg (valΩ d Ω v), norm_nonneg (gradΩ d Ω v), norm_nonneg v,
    sq_nonneg ‖valΩ d Ω v‖]

instance instCompleteSpaceH10ΩGraph (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    CompleteSpace (H10ΩGraph d Ω) :=
  (Submodule.span ℂ (testGraphΩ d Ω)).isClosed_topologicalClosure.completeSpace_coe

instance instCompleteSpaceH10Ω (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    CompleteSpace (H10Ω d Ω) :=
  inferInstanceAs (CompleteSpace (H10ΩGraph d Ω))

/-! ### Test functions -/

/-- The class in `L²(Ω;ℂ)` of a function that is square integrable on `Ω`. -/
def toL2Ω (Ω : Set (EuclideanSpace ℝ (Fin d))) (g : EuclideanSpace ℝ (Fin d) → ℂ)
    (hg : MemLp g 2 (volume.restrict Ω)) : L2Ω d Ω := hg.toLp g

/-- The class in `L²(Ω;ℂ^d)` of a vector field that is square integrable on `Ω`. -/
def toL2Ωvec (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℂ (Fin d))
    (hg : MemLp g 2 (volume.restrict Ω)) : L2Ωvec d Ω := hg.toLp g

theorem coe_toL2Ω (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : MemLp g 2 (volume.restrict Ω)) :
    ⇑(toL2Ω Ω g hg) =ᵐ[volume.restrict Ω] g := hg.coeFn_toLp

theorem coe_toL2Ωvec (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℂ (Fin d))
    (hg : MemLp g 2 (volume.restrict Ω)) : ⇑(toL2Ωvec Ω g hg) =ᵐ[volume.restrict Ω] g :=
  hg.coeFn_toLp

/-- The data of a test function `φ ∈ C¹_c(Ω;ℂ)`. -/
structure IsTestFunΩ (Ω : Set (EuclideanSpace ℝ (Fin d))) (φ : EuclideanSpace ℝ (Fin d) → ℂ) :
    Prop where
  contDiff : ContDiff ℝ 1 φ
  hasCompactSupport : HasCompactSupport φ
  tsupport_subset : tsupport φ ⊆ Ω

/-- The gradient of a test function vanishes where its derivative does. -/
theorem grad_eq_zero_of_fderiv {φ : EuclideanSpace ℝ (Fin d) → ℂ} {x : EuclideanSpace ℝ (Fin d)}
    (h : fderiv ℝ φ x = 0) : grad φ x = 0 := by
  ext i
  simp [grad, h]

theorem continuous_grad {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (grad φ) := by
  have hc := hφ.continuous_fderiv one_ne_zero
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  exact hc.clm_apply continuous_const

theorem hasCompactSupport_grad {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (grad φ) := by
  refine (hφ.fderiv ℝ).mono fun x hx => ?_
  intro h0
  exact hx (grad_eq_zero_of_fderiv h0)

namespace IsTestFunΩ

variable {φ : EuclideanSpace ℝ (Fin d) → ℂ}

theorem continuous (h : IsTestFunΩ Ω φ) : Continuous φ := h.contDiff.continuous

theorem continuous_grad (h : IsTestFunΩ Ω φ) : Continuous (grad φ) :=
  LionsC12.continuous_grad h.contDiff

theorem hasCompactSupport_grad (h : IsTestFunΩ Ω φ) : HasCompactSupport (grad φ) :=
  LionsC12.hasCompactSupport_grad h.hasCompactSupport

theorem differentiable (h : IsTestFunΩ Ω φ) : Differentiable ℝ φ :=
  h.contDiff.differentiable one_ne_zero

theorem memLp (h : IsTestFunΩ Ω φ) : MemLp φ 2 (volume.restrict Ω) :=
  (h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport).restrict Ω

theorem memLp_grad (h : IsTestFunΩ Ω φ) : MemLp (grad φ) 2 (volume.restrict Ω) :=
  (h.continuous_grad.memLp_of_hasCompactSupport h.hasCompactSupport_grad).restrict Ω

theorem integrable (h : IsTestFunΩ Ω φ) : Integrable φ :=
  h.continuous.integrable_of_hasCompactSupport h.hasCompactSupport

theorem eq_zero_of_notMem (h : IsTestFunΩ Ω φ) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∉ Ω) :
    φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h' => hx (h.tsupport_subset h')

theorem fderiv_eq_zero_of_notMem (h : IsTestFunΩ Ω φ) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ Ω) : fderiv ℝ φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h' =>
    hx (h.tsupport_subset (tsupport_fderiv_subset ℝ h'))

theorem grad_eq_zero_of_notMem (h : IsTestFunΩ Ω φ) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ Ω) : grad φ x = 0 :=
  grad_eq_zero_of_fderiv (h.fderiv_eq_zero_of_notMem hx)

/-- The derivative of the complexification of a real function. -/
theorem fderiv_ofReal {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : Differentiable ℝ ψ)
    (x v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun y => (ψ y : ℂ)) x v = ((fderiv ℝ ψ x v : ℝ) : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt (x := ψ x)).comp x (hψ x).hasFDerivAt
  rw [show (fun y => (ψ y : ℂ)) = Complex.ofRealCLM ∘ ψ from rfl, h.fderiv]
  rfl

/-- A real `C^∞_c(Ω)` function, as a complex test function. -/
theorem ofReal {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ω) : IsTestFunΩ Ω (fun x => (ψ x : ℂ)) where
  contDiff := (Complex.ofRealCLM.contDiff.comp hψ).of_le (by exact_mod_cast le_top)
  hasCompactSupport := hc.comp_left Complex.ofReal_zero
  tsupport_subset := (tsupport_comp_subset Complex.ofReal_zero ψ).trans hs

end IsTestFunΩ

theorem mem_testGraphΩ {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : IsTestFunΩ Ω φ) :
    WithLp.toLp 2 (toL2Ω Ω φ hφ.memLp, toL2Ωvec Ω (grad φ) hφ.memLp_grad) ∈ testGraphΩ d Ω :=
  ⟨φ, hφ.contDiff, hφ.hasCompactSupport, hφ.tsupport_subset, coe_toL2Ω φ hφ.memLp,
    coe_toL2Ωvec (grad φ) hφ.memLp_grad⟩

theorem testGraphΩ_subset : testGraphΩ d Ω ⊆ H10ΩGraph d Ω :=
  (Submodule.subset_span).trans (Submodule.le_topologicalClosure _)

/-- The element `(φ, ∇φ)` of `H¹₀(Ω;ℂ)` defined by a test function `φ ∈ C¹_c(Ω;ℂ)`. -/
def ofTestΩ {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : IsTestFunΩ Ω φ) : H10Ω d Ω :=
  H10Ω.mk (WithLp.toLp 2 (toL2Ω Ω φ hφ.memLp, toL2Ωvec Ω (grad φ) hφ.memLp_grad))
    (testGraphΩ_subset (mem_testGraphΩ hφ))

theorem valΩ_ofTestΩ {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : IsTestFunΩ Ω φ) :
    valΩ d Ω (ofTestΩ hφ) = toL2Ω Ω φ hφ.memLp := rfl

theorem gradΩ_ofTestΩ {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : IsTestFunΩ Ω φ) :
    gradΩ d Ω (ofTestΩ hφ) = toL2Ωvec Ω (grad φ) hφ.memLp_grad := rfl

theorem coe_valΩ_ofTestΩ {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : IsTestFunΩ Ω φ) :
    ⇑(valΩ d Ω (ofTestΩ hφ)) =ᵐ[volume.restrict Ω] φ := coe_toL2Ω φ hφ.memLp

theorem coe_gradΩ_ofTestΩ {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : IsTestFunΩ Ω φ) :
    ⇑(gradΩ d Ω (ofTestΩ hφ)) =ᵐ[volume.restrict Ω] grad φ :=
  coe_toL2Ωvec (grad φ) hφ.memLp_grad

/-- A continuous semilinear map on `L²(Ω) × L²(Ω;ℂ^d)` that vanishes on the test graphs
vanishes on `H¹₀(Ω)`. -/
theorem eq_zero_of_testGraphΩ {σ : ℂ →+* ℂ} {F : Type*} [NormedAddCommGroup F] [Module ℂ F]
    (Λ : WithLp 2 (L2Ω d Ω × L2Ωvec d Ω) →SL[σ] F) (h : ∀ p ∈ testGraphΩ d Ω, Λ p = 0)
    (v : H10Ω d Ω) : Λ (H10Ω.pair v) = 0 := by
  have hle : H10ΩGraph d Ω ≤ LinearMap.ker (Λ : WithLp 2 (L2Ω d Ω × L2Ωvec d Ω) →ₛₗ[σ] F) :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 fun p hp => h p hp)
      (ContinuousLinearMap.isClosed_ker Λ)
  exact hle (H10Ω.pair_mem v)

/-! ### Inner products -/

theorem inner_L2Ω_eq (f g : L2Ω d Ω) : ⟪f, g⟫_ℂ = ∫ x in Ω, conj (f x) * g x := by
  rw [MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply, mul_comm]

theorem inner_L2Ωvec_eq (f g : L2Ωvec d Ω) : ⟪f, g⟫_ℂ = ∫ x in Ω, ⟪f x, g x⟫_ℂ :=
  MeasureTheory.L2.inner_def f g

/-- `⟨w, h⟩ = ∫_Ω conj(w) h` for a test function `w = φ`, as an integral over the whole space. -/
theorem inner_valΩ_ofTestΩ {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : IsTestFunΩ Ω φ)
    (h : L2Ω d Ω) :
    ⟪valΩ d Ω (ofTestΩ hφ), h⟫_ℂ = ∫ x in Ω, conj (φ x) * h x := by
  rw [inner_L2Ω_eq]
  refine integral_congr_ae ?_
  filter_upwards [coe_valΩ_ofTestΩ hφ] with x hx
  rw [hx]

/-! ### Integration by parts and the Gelfand triple -/

/-- Integration by parts for test functions in the direction `eᵢ`:
`∫ conj(∂ᵢφ) ψ = -∫ conj(φ) ∂ᵢψ`. -/
theorem integral_conj_fderiv_mul {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : IsTestFunΩ Ω φ)
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ : IsTestFunΩ Ω ψ) (v : EuclideanSpace ℝ (Fin d)) :
    ∫ x, conj (fderiv ℝ φ x v) * ψ x = -∫ x, conj (φ x) * fderiv ℝ ψ x v := by
  have hf'g : Integrable (fun x => fderiv ℝ φ x v * conj (ψ x)) := by
    have hc : Continuous fun x => fderiv ℝ φ x v * conj (ψ x) :=
      ((hφ.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
        (Complex.continuous_conj.comp hψ.continuous)
    refine hc.integrable_of_hasCompactSupport ?_
    exact (hψ.hasCompactSupport.comp_left (map_zero (starRingEnd ℂ))).mul_left
  have hfg' : Integrable (fun x => φ x * fderiv ℝ (fun y => conj (ψ y)) x v) := by
    have hc : Continuous fun x => φ x * fderiv ℝ (fun y => conj (ψ y)) x v := by
      refine hφ.continuous.mul ?_
      have : ContDiff ℝ 1 fun y => conj (ψ y) :=
        (Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp hψ.contDiff
      exact (this.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact hc.integrable_of_hasCompactSupport hφ.hasCompactSupport.mul_right
  have hfg : Integrable (fun x => φ x * conj (ψ x)) := by
    have hc : Continuous fun x => φ x * conj (ψ x) :=
      hφ.continuous.mul (Complex.continuous_conj.comp hψ.continuous)
    exact hc.integrable_of_hasCompactSupport hφ.hasCompactSupport.mul_right
  have hconjd : ∀ x, fderiv ℝ (fun y => conj (ψ y)) x v = conj (fderiv ℝ ψ x v) := by
    intro x
    have h := ((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt
      (x := ψ x)).comp x (hψ.differentiable x).hasFDerivAt
    rw [show (fun y => conj (ψ y)) = (Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ) ∘ ψ
      from rfl, h.fderiv]
    rfl
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) hf'g hfg' hfg
    (fun x _ => hφ.differentiable x) (fun x _ => by
      have : ContDiff ℝ 1 fun y => conj (ψ y) :=
        (Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp hψ.contDiff
      exact this.differentiable one_ne_zero x)
  simp only [hconjd] at key
  have h1 : ∫ x, conj (fderiv ℝ φ x v) * ψ x = conj (∫ x, fderiv ℝ φ x v * conj (ψ x)) := by
    rw [← integral_conj]
    congr 1; funext x; simp
  have h2 : ∫ x, conj (φ x) * fderiv ℝ ψ x v = conj (∫ x, φ x * conj (fderiv ℝ ψ x v)) := by
    rw [← integral_conj]
    congr 1; funext x; simp
  rw [h1, h2, key, map_neg, neg_neg]

/-- **Integration by parts in `H¹₀(Ω)`** against a real `C^∞_c(Ω)` function `ψ`:
`⟨∂ᵢw, ψ⟩ = -⟨w, ∂ᵢψ⟩`, in the form
`∫_Ω ψ conj(∂ᵢw) + ∫_Ω conj(w) ∂ᵢψ = 0`. -/
theorem inner_gradΩ_single {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω) (i : Fin d)
    (w : H10Ω d Ω) :
    (∫ x in Ω, (ψ x : ℂ) * conj (gradΩ d Ω w x i))
      + ∫ x in Ω, conj (valΩ d Ω w x) * ((fderiv ℝ ψ x (EuclideanSpace.single i 1) : ℝ) : ℂ)
      = 0 := by
  have hψ' := IsTestFunΩ.ofReal hψ hc hs
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  set G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℂ (Fin d) :=
    fun x => (ψ x : ℂ) • EuclideanSpace.single i (1 : ℂ) with hGdef
  have hGm : MemLp G 2 (volume.restrict Ω) := by
    have hcont : Continuous G :=
      Continuous.smul hψ'.continuous (continuous_const (y := EuclideanSpace.single i (1 : ℂ)))
    exact (hcont.memLp_of_hasCompactSupport hψ'.hasCompactSupport.smul_right).restrict Ω
  set g : EuclideanSpace ℝ (Fin d) → ℂ :=
    fun x => ((fderiv ℝ ψ x (EuclideanSpace.single i 1) : ℝ) : ℂ) with hgdef
  have hgm : MemLp g 2 (volume.restrict Ω) := by
    have hcont : Continuous g :=
      Complex.continuous_ofReal.comp
        ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
    refine (hcont.memLp_of_hasCompactSupport ?_).restrict Ω
    exact (hc.fderiv ℝ).comp_left (g := fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ =>
      ((L (EuclideanSpace.single i 1) : ℝ) : ℂ)) (by simp)
  set Λ : WithLp 2 (L2Ω d Ω × L2Ωvec d Ω) →L⋆[ℂ] ℂ :=
    (innerSLFlip ℂ (toL2Ωvec Ω G hGm)).comp (WithLp.sndL 2 ℂ (L2Ω d Ω) (L2Ωvec d Ω)) +
      (innerSLFlip ℂ (toL2Ω Ω g hgm)).comp (WithLp.fstL 2 ℂ (L2Ω d Ω) (L2Ωvec d Ω)) with hΛ
  have hval : ∀ p : WithLp 2 (L2Ω d Ω × L2Ωvec d Ω),
      Λ p = (∫ x in Ω, (ψ x : ℂ) * conj ((WithLp.ofLp p).2 x i))
        + ∫ x in Ω, conj ((WithLp.ofLp p).1 x) * g x := by
    intro p
    simp only [hΛ, add_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, innerSLFlip_apply_apply, WithLp.sndL_apply, WithLp.fstL_apply]
    rw [inner_L2Ωvec_eq, inner_L2Ω_eq]
    congr 1
    · refine integral_congr_ae ?_
      filter_upwards [coe_toL2Ωvec G hGm] with x hx
      rw [hx, hGdef, inner_smul_right, EuclideanSpace.inner_single_right, one_mul]
      rfl
    · refine integral_congr_ae ?_
      filter_upwards [coe_toL2Ω g hgm] with x hx
      rw [hx]
      rfl
  have h0 : ∀ p ∈ testGraphΩ d Ω, Λ p = 0 := by
    rintro p ⟨φ, hc1, hcs, hsub, h1, h2⟩
    have hφ : IsTestFunΩ Ω φ := ⟨hc1, hcs, hsub⟩
    rw [hval]
    have e1 : ∫ x in Ω, (ψ x : ℂ) * conj ((WithLp.ofLp p).2 x i)
        = ∫ x, conj (fderiv ℝ φ x (EuclideanSpace.single i 1)) * (ψ x : ℂ) := by
      calc ∫ x in Ω, (ψ x : ℂ) * conj ((WithLp.ofLp p).2 x i)
          = ∫ x in Ω, conj (fderiv ℝ φ x (EuclideanSpace.single i 1)) * (ψ x : ℂ) := by
            refine integral_congr_ae ?_
            filter_upwards [h2] with x hx
            rw [hx, mul_comm]
            rfl
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
            rw [hφ.fderiv_eq_zero_of_notMem hx]
            simp
    have e2 : ∫ x in Ω, conj ((WithLp.ofLp p).1 x) * g x
        = ∫ x, conj (φ x) * fderiv ℝ (fun y => (ψ y : ℂ)) x (EuclideanSpace.single i 1) := by
      calc ∫ x in Ω, conj ((WithLp.ofLp p).1 x) * g x
          = ∫ x in Ω, conj (φ x) * fderiv ℝ (fun y => (ψ y : ℂ)) x (EuclideanSpace.single i 1) := by
            refine integral_congr_ae ?_
            filter_upwards [h1] with x hx
            rw [hx, IsTestFunΩ.fderiv_ofReal hψd]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
            rw [hφ.eq_zero_of_notMem hx]
            simp
    rw [e1, e2, integral_conj_fderiv_mul hφ hψ', neg_add_cancel]
  have := eq_zero_of_testGraphΩ Λ h0 w
  rw [hval] at this
  exact this

/-- A function in `L²(Ω)`, `Ω` open, orthogonal to every real `C^∞_c(Ω)` function vanishes
almost everywhere on `Ω`. -/
theorem ae_eq_zero_of_forall_smoothΩ (hΩ : IsOpen Ω) {h : EuclideanSpace ℝ (Fin d) → ℂ}
    (hm : MemLp h 2 (volume.restrict Ω))
    (H : ∀ ψ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → ∫ x in Ω, (ψ x : ℂ) * h x = 0) : h =ᵐ[volume.restrict Ω] 0 := by
  have hloc : LocallyIntegrableOn h Ω volume := by
    rw [locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro K hKU hK
    have hfin : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hK.measure_ne_top
    have h2 : MemLp h 2 (volume.restrict K) := hm.mono_measure (Measure.restrict_mono hKU le_rfl)
    exact h2.integrable one_le_two
  have hae := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun ψ hψ hc hs => by
    have := H ψ hψ hc hs
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)]
    · simpa [Complex.real_smul] using this
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport fun h' => hx (hs h'), zero_smul])
  rw [EventuallyEq, ae_restrict_iff' hΩ.measurableSet]
  filter_upwards [hae] with x hx hxU
  simpa using hx hxU

/-- An element of `L²(Ω)`, `Ω` open, orthogonal to every real `C^∞_c(Ω)` function vanishes. -/
theorem eq_zero_of_forall_smoothΩ (hΩ : IsOpen Ω) (h : L2Ω d Ω)
    (H : ∀ ψ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → ∫ x in Ω, (ψ x : ℂ) * h x = 0) : h = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  exact ae_eq_zero_of_forall_smoothΩ hΩ (Lp.memLp h) H

/-- `L²(Ω) ↪ H⁻¹(Ω)` is injective, `Ω` open. -/
theorem ofL2Ω_injective (hΩ : IsOpen Ω) : Function.Injective (ofL2Ω d Ω) := by
  intro h h' heq
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_smoothΩ hΩ _ fun ψ hψ hc hs => ?_
  have hψ' := IsTestFunΩ.ofReal hψ hc hs
  have e : ofL2Ω d Ω h (ofTestΩ hψ') - ofL2Ω d Ω h' (ofTestΩ hψ') = 0 := by rw [heq, sub_self]
  simp only [ofL2Ω, ContinuousLinearMap.coe_comp, Function.comp_apply,
    innerSLFlip_apply_apply] at e
  rw [← inner_sub_right, inner_L2Ω_eq] at e
  rw [← e]
  refine integral_congr_ae ?_
  filter_upwards [coe_valΩ_ofTestΩ hψ'] with x hx
  rw [hx, Complex.conj_ofReal]

/-- `H¹₀(Ω) ↪ L²(Ω)` is injective, `Ω` open: the weak gradient is determined by the function. -/
theorem valΩ_injective (hΩ : IsOpen Ω) : Function.Injective (valΩ d Ω) := by
  intro w w' heq
  rw [← sub_eq_zero] at heq ⊢
  rw [← map_sub] at heq
  set v := w - w'
  have hcomp : ∀ i : Fin d, (fun x => gradΩ d Ω v x i) =ᵐ[volume.restrict Ω] 0 := by
    intro i
    have hm : MemLp (fun x => gradΩ d Ω v x i) 2 (volume.restrict Ω) :=
      ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ).comp_memLp (gradΩ d Ω v))
    refine ae_eq_zero_of_forall_smoothΩ hΩ hm fun ψ hψ hc hs => ?_
    have key := inner_gradΩ_single hψ hc hs i v
    have hv0 : ∫ x in Ω, conj (valΩ d Ω v x) * ((fderiv ℝ ψ x (EuclideanSpace.single i 1) : ℝ) : ℂ)
        = 0 := by
      have : ⇑(valΩ d Ω v) =ᵐ[volume.restrict Ω] 0 := by
        rw [heq]; exact Lp.coeFn_zero _ _ _
      rw [integral_congr_ae (g := fun _ => (0 : ℂ))]
      · simp
      · filter_upwards [this] with x hx
        rw [hx]; simp
    rw [hv0, add_zero] at key
    have : ∫ x in Ω, conj ((ψ x : ℂ) * gradΩ d Ω v x i) = 0 := by
      rw [← key]
      congr 1; funext x
      rw [map_mul, Complex.conj_ofReal]
    rw [integral_conj] at this
    simpa using this
  have hgrad : gradΩ d Ω v = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    have hall := (ae_all_iff (ι := Fin d)).2 hcomp
    filter_upwards [hall] with x hx
    ext i
    simpa using hx i
  apply H10Ω.ext
  have h1 : H10Ω.pair v = WithLp.toLp 2 (valΩ d Ω v, gradΩ d Ω v) := rfl
  rw [h1, heq, hgrad]
  rfl

/-- `H¹₀(Ω) ↪ L²(Ω)` has dense range, `Ω` open. -/
theorem denseRange_valΩ (hΩ : IsOpen Ω) : DenseRange (valΩ d Ω) := by
  have : (LinearMap.range (valΩ d Ω : H10Ω d Ω →ₗ[ℂ] L2Ω d Ω)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro h hh
    apply ofL2Ω_injective hΩ
    ext w
    rw [Submodule.mem_orthogonal'] at hh
    have := hh (valΩ d Ω w) ⟨w, rfl⟩
    simp only [ofL2Ω, ContinuousLinearMap.coe_comp, Function.comp_apply, innerSLFlip_apply_apply,
      map_zero, zero_apply]
    rw [← inner_conj_symm, this, map_zero]
  exact (Submodule.dense_iff_topologicalClosure_eq_top).2 this

/-! ### The forms and uniqueness -/

theorem isLionsSolutionΩ_iff (𝔟 : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (F : ℝ → L2Ω d Ω)
    (w : ℝ → H10Ω d Ω) :
    IsLionsSolutionΩ d Ω 𝔟 F w ↔ IsLionsSol (valΩ d Ω) (formΩ d Ω 𝔟) F w := Iff.rfl

theorem ofL2Ω_eq_ofHL (h : L2Ω d Ω) : ofL2Ω d Ω h = ofHL (valΩ d Ω) h := rfl

theorem ofH10Ω_eq (v : H10Ω d Ω) : ofH10Ω d Ω v = ofHL (valΩ d Ω) (valΩ d Ω v) := rfl

/-- A coefficient on `ℝ^d` that is bounded and measurable in `x` at the time `t`. -/
structure IsBoundedCoeffΩ (𝔟 : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (Λ : ℝ) : Prop where
  measurable : Measurable (𝔟 t)
  bound : ∀ x, |𝔟 t x| ≤ Λ

theorem integrable_formΩ_integrand {𝔟 : ℝ → EuclideanSpace ℝ (Fin d) → ℝ} {t Λ : ℝ}
    (h : IsBoundedCoeffΩ 𝔟 t Λ) (v w : H10Ω d Ω) :
    Integrable (fun x => (𝔟 t x : ℂ) * ⟪gradΩ d Ω w x, gradΩ d Ω v x⟫_ℂ) (volume.restrict Ω) := by
  have hi : Integrable (fun x => ⟪gradΩ d Ω w x, gradΩ d Ω v x⟫_ℂ) (volume.restrict Ω) :=
    L2.integrable_inner (gradΩ d Ω w) (gradΩ d Ω v)
  have hm : AEStronglyMeasurable (fun x => (𝔟 t x : ℂ)) (volume.restrict Ω) :=
    (Complex.measurable_ofReal.comp h.measurable).aestronglyMeasurable
  refine hi.bdd_mul (c := Λ) hm (Eventually.of_forall fun x => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs]; exact h.bound x

theorem formΩ_sub {𝔟 : ℝ → EuclideanSpace ℝ (Fin d) → ℝ} {t Λ : ℝ} (h : IsBoundedCoeffΩ 𝔟 t Λ)
    (v₁ v₂ z : H10Ω d Ω) :
    formΩ d Ω 𝔟 t (v₁ - v₂) z = formΩ d Ω 𝔟 t v₁ z - formΩ d Ω 𝔟 t v₂ z := by
  unfold formΩ
  rw [← integral_sub (integrable_formΩ_integrand h v₁ z) (integrable_formΩ_integrand h v₂ z)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (gradΩ d Ω v₁) (gradΩ d Ω v₂)] with x hx
  rw [map_sub, hx, Pi.sub_apply, inner_sub_right]
  ring

/-- For `𝔟 ≥ 0`: `Re 𝔟(t)[v,v] ≥ 0`. -/
theorem formΩ_self_re_nonneg {𝔟 : ℝ → EuclideanSpace ℝ (Fin d) → ℝ} {t Λ : ℝ}
    (h : IsBoundedCoeffΩ 𝔟 t Λ) (h0 : ∀ x, 0 ≤ 𝔟 t x) (v : H10Ω d Ω) :
    0 ≤ (formΩ d Ω 𝔟 t v v).re := by
  have hint := integrable_formΩ_integrand h v v
  unfold formΩ
  show 0 ≤ RCLike.re (∫ x in Ω, (𝔟 t x : ℂ) * ⟪gradΩ d Ω v x, gradΩ d Ω v x⟫_ℂ)
  rw [← integral_re hint]
  refine integral_nonneg fun x => ?_
  have e : RCLike.re ((𝔟 t x : ℂ) * ⟪gradΩ d Ω v x, gradΩ d Ω v x⟫_ℂ)
      = 𝔟 t x * ‖gradΩ d Ω v x‖ ^ 2 := by
    change ((𝔟 t x : ℂ) * ⟪gradΩ d Ω v x, gradΩ d Ω v x⟫_ℂ).re = _
    rw [Complex.re_ofReal_mul]
    congr 1
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [e]
  exact mul_nonneg (h0 x) (sq_nonneg _)

/-- **Uniqueness of the Lions variational solution** on an open set `Ω ⊆ ℝ^d`, for a scalar
coefficient which is measurable, bounded and nonnegative. -/
theorem isLionsSolutionΩ_unique (hΩ : IsOpen Ω) {𝔟 : ℝ → EuclideanSpace ℝ (Fin d) → ℝ} {Λ : ℝ}
    (h𝔟 : ∀ t, IsBoundedCoeffΩ 𝔟 t Λ) (h0 : ∀ t x, 0 ≤ 𝔟 t x) {F : ℝ → L2Ω d Ω}
    {w₁ w₂ : ℝ → H10Ω d Ω} (h₁ : IsLionsSolutionΩ d Ω 𝔟 F w₁)
    (h₂ : IsLionsSolutionΩ d Ω 𝔟 F w₂) : ∀ᵐ t ∂μ01, w₁ t = w₂ t :=
  IsLionsSol.ae_eq (valΩ_injective hΩ) (denseRange_valΩ hΩ)
    (fun t v₁ v₂ z => formΩ_sub (h𝔟 t) v₁ v₂ z)
    (fun t v => formΩ_self_re_nonneg (h𝔟 t) (h0 t) v)
    ((isLionsSolutionΩ_iff _ _ _).1 h₁) ((isLionsSolutionΩ_iff _ _ _).1 h₂)

end LionsC12
