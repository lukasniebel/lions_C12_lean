module

public import LionsC12.Spaces.Line
public import LionsC12.Spaces.TimeL2
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# `W^{1,2}(U)` and `H¹₀(U)` through weak derivatives, on an open set `U ⊆ ℝ`

The statement layer defines `H¹₀(U;ℂ)` as the closure of the graphs `(φ, φ')` of the
`C¹_c(U;ℂ)` functions in `L²(U) × L²(U)` (Brezis).  This file shows that this is the textbook
space: the closure of `C_c^∞(U)` in the Sobolev space `W^{1,2}(U)` defined by weak derivatives.

* `HasWeakDerivL2 U v g` — `g ∈ L²(U)` is the weak derivative of `v ∈ L²(U)` on `U`:
  `∫_U v φ' = -∫_U g φ` for every real `φ ∈ C_c^∞(U)`; `hasWeakDerivL2_iff_complex` — the same
  with complex test functions (`integral_fderiv_mul_of_real`, real and imaginary parts);
* `W12Graph U` — the subspace of `L²(U) × L²(U)` of the pairs `(v, v')`, that is `W^{1,2}(U)`
  with its norm `(‖v‖² + ‖v'‖²)^{1/2}`; it is closed (`isClosed_W12Graph`), and the weak
  derivative is unique (`hasWeakDerivL2_unique`), so that `W12Graph U` is the graph of a closed
  operator (`weakDerivOp`, `weakDerivOp_graph`, `weakDerivOp_isClosed`);
* `hasWeakDerivL2_dx`, `H10Graph_le_W12Graph` — `∂ₓv` is the weak derivative of `v ∈ H¹₀(U)`;
* `exists_smooth_approx` — mollification: a `C¹_c` function supported in an open set is the
  uniform limit, together with its derivative, of `C_c^∞` functions supported in a fixed compact
  subset of the open set;
* `H10Graph_eq_closure_smoothGraph` — `H¹₀(U)` is the closure of the graphs `smoothGraph U` of
  the `C_c^∞(U)` functions, `U` open; `range_H10toW12` — the isometric inclusion
  `H¹₀(U) ↪ W^{1,2}(U)` has for range the closure of `C_c^∞(U)` in `W^{1,2}(U)`, the textbook
  definition of `H¹₀(U)`;
* `hasWeakDerivL2_iff_forall_H10` — `g` is the weak derivative of `v` if and only if
  `⟨∂ₓw, v⟩ = -⟨w, g⟩` for every `w ∈ H¹₀(U)`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology Metric LionsC12Challenge
open scoped InnerProductSpace ComplexConjugate ContDiff ENNReal Convolution Pointwise

/-! ### Weak derivatives -/

variable {U : Set ℝ}

/-- `g ∈ L²(U)` is the weak derivative of `v ∈ L²(U)` on `U`: `∫_U v φ' = -∫_U g φ` for every
real `φ ∈ C_c^∞(U)` (smooth, compactly supported, `tsupport φ ⊆ U`). -/
def HasWeakDerivL2 (U : Set ℝ) (v g : L2 U) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ x in U, ((deriv φ x : ℝ) : ℂ) * v x = -∫ x in U, (φ x : ℂ) * g x

/-- The derivative of the complexification of a real function. -/
theorem deriv_ofReal {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) (x : ℝ) :
    deriv (fun y => (ψ y : ℂ)) x = ((deriv ψ x : ℝ) : ℂ) :=
  ((hψ x).hasDerivAt.ofReal_comp).deriv

section RealTest

variable {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U)

include hψ hc hs in
/-- `∫_U ψ f = ⟨ψ, f⟩` for a real test function `ψ`. -/
theorem integral_ofReal_mul_eq_inner (f : L2 U) :
    ∫ x in U, (ψ x : ℂ) * f x = ⟪val U (ofTest (IsTestFun.ofReal hψ hc hs)), f⟫_ℂ := by
  rw [inner_L2_eq]
  refine integral_congr_ae ?_
  filter_upwards [val_ofTest (IsTestFun.ofReal hψ hc hs)] with x hx
  rw [hx, Complex.conj_ofReal]

include hψ hc hs in
/-- `∫_U ψ' f = ⟨ψ', f⟩` for a real test function `ψ`. -/
theorem integral_deriv_ofReal_mul_eq_inner (f : L2 U) :
    ∫ x in U, ((deriv ψ x : ℝ) : ℂ) * f x = ⟪dx U (ofTest (IsTestFun.ofReal hψ hc hs)), f⟫_ℂ := by
  rw [inner_L2_eq]
  refine integral_congr_ae ?_
  filter_upwards [dx_ofTest (IsTestFun.ofReal hψ hc hs)] with x hx
  rw [hx, deriv_ofReal (hψ.differentiable (by simp)), Complex.conj_ofReal]

end RealTest

/-- The weak derivative in terms of inner products with the test elements `(ψ, ψ')`. -/
theorem hasWeakDerivL2_iff_inner {v g : L2 U} : HasWeakDerivL2 U v g ↔
    ∀ (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U),
      ⟪dx U (ofTest (IsTestFun.ofReal hψ hc hs)), v⟫_ℂ
        = -⟪val U (ofTest (IsTestFun.ofReal hψ hc hs)), g⟫_ℂ := by
  refine forall_congr' fun ψ => forall_congr' fun hψ => forall_congr' fun hc =>
    forall_congr' fun hs => ?_
  rw [integral_ofReal_mul_eq_inner hψ hc hs, integral_deriv_ofReal_mul_eq_inner hψ hc hs]

/-! ### The space `W^{1,2}(U)` -/

/-- `W^{1,2}(U)`, as the subspace of `L²(U) × L²(U)` of the pairs `(v, v')` of a function and
its weak derivative; its norm is `(‖v‖² + ‖v'‖²)^{1/2}`. -/
def W12Graph (U : Set ℝ) : Submodule ℂ (WithLp 2 (L2 U × L2 U)) where
  carrier := {p | HasWeakDerivL2 U (WithLp.ofLp p).1 (WithLp.ofLp p).2}
  zero_mem' := by
    simp only [mem_ofPred_eq, hasWeakDerivL2_iff_inner, WithLp.ofLp_zero, Prod.fst_zero,
      Prod.snd_zero, inner_zero_right, neg_zero, implies_true]
  add_mem' := by
    intro p q hp hq
    simp only [mem_ofPred_eq, hasWeakDerivL2_iff_inner, WithLp.ofLp_add, Prod.fst_add,
      Prod.snd_add, inner_add_right] at hp hq ⊢
    intro ψ hψ hc hs
    rw [hp ψ hψ hc hs, hq ψ hψ hc hs, neg_add]
  smul_mem' := by
    intro c p hp
    simp only [mem_ofPred_eq, hasWeakDerivL2_iff_inner, WithLp.ofLp_smul, Prod.smul_fst,
      Prod.smul_snd, inner_smul_right] at hp ⊢
    intro ψ hψ hc hs
    rw [hp ψ hψ hc hs, mul_neg]

theorem mem_W12Graph {p : WithLp 2 (L2 U × L2 U)} :
    p ∈ W12Graph U ↔ HasWeakDerivL2 U (WithLp.ofLp p).1 (WithLp.ofLp p).2 := Iff.rfl

theorem toLp_mem_W12Graph {v g : L2 U} :
    WithLp.toLp 2 (v, g) ∈ W12Graph U ↔ HasWeakDerivL2 U v g := Iff.rfl

/-- `W^{1,2}(U)` is closed in `L²(U) × L²(U)`. -/
theorem isClosed_W12Graph : IsClosed (W12Graph U : Set (WithLp 2 (L2 U × L2 U))) := by
  have e : (W12Graph U : Set (WithLp 2 (L2 U × L2 U))) =
      ⋂ (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U),
        {p | ⟪dx U (ofTest (IsTestFun.ofReal hψ hc hs)), (WithLp.ofLp p).1⟫_ℂ
          = -⟪val U (ofTest (IsTestFun.ofReal hψ hc hs)), (WithLp.ofLp p).2⟫_ℂ} := by
    ext p
    simp only [SetLike.mem_coe, mem_W12Graph, hasWeakDerivL2_iff_inner, mem_iInter,
      mem_ofPred_eq]
  rw [e]
  refine isClosed_iInter fun ψ => isClosed_iInter fun hψ => isClosed_iInter fun hc =>
    isClosed_iInter fun hs => isClosed_eq ?_ ?_
  · exact continuous_const.inner (WithLp.fstL 2 ℂ (L2 U) (L2 U)).continuous
  · exact (continuous_const.inner (WithLp.sndL 2 ℂ (L2 U) (L2 U)).continuous).neg

instance instCompleteSpaceW12Graph (U : Set ℝ) : CompleteSpace (W12Graph U) :=
  haveI : IsClosed (W12Graph U : Set (WithLp 2 (L2 U × L2 U))) := isClosed_W12Graph
  IsClosed.completeSpace_coe

/-- **Uniqueness of the weak derivative** on an open set: `(0, g) ∈ W^{1,2}(U)` forces `g = 0`. -/
theorem eq_zero_of_hasWeakDerivL2_zero (hU : IsOpen U) {g : L2 U} (h : HasWeakDerivL2 U 0 g) :
    g = 0 := by
  refine eq_zero_of_forall_smooth hU g fun ψ hψ hc hs => ?_
  have := h ψ hψ hc hs
  have e : ∫ x in U, ((deriv ψ x : ℝ) : ℂ) * (0 : L2 U) x = 0 := by
    rw [integral_deriv_ofReal_mul_eq_inner hψ hc hs, inner_zero_right]
  rw [e] at this
  exact neg_eq_zero.1 this.symm

/-- The weak derivative is unique on an open set. -/
theorem hasWeakDerivL2_unique (hU : IsOpen U) {v g₁ g₂ : L2 U} (h₁ : HasWeakDerivL2 U v g₁)
    (h₂ : HasWeakDerivL2 U v g₂) : g₁ = g₂ := by
  have h := (W12Graph U).sub_mem (toLp_mem_W12Graph.2 h₁) (toLp_mem_W12Graph.2 h₂)
  rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self] at h
  exact sub_eq_zero.1 (eq_zero_of_hasWeakDerivL2_zero hU h)

/-- The weak derivative as a closed operator in `L²(U)`: the partial linear map whose graph is
`W^{1,2}(U)` (`weakDerivOp_graph`). -/
def weakDerivOp (U : Set ℝ) : L2 U →ₗ.[ℂ] L2 U :=
  ((W12Graph U).map (WithLp.linearEquiv 2 ℂ (L2 U × L2 U)).toLinearMap).toLinearPMap

theorem weakDerivOp_graph (hU : IsOpen U) :
    (weakDerivOp U).graph
      = (W12Graph U).map (WithLp.linearEquiv 2 ℂ (L2 U × L2 U)).toLinearMap := by
  refine Submodule.toLinearPMap_graph_eq _ ?_
  rintro x ⟨p, hp, rfl⟩ hx
  have hp' : p = WithLp.toLp 2 (0, (WithLp.ofLp p).2) := by
    rw [← hx]; rfl
  rw [hp'] at hp
  exact eq_zero_of_hasWeakDerivL2_zero hU hp

/-- `(v, g)` lies on the graph of the weak derivative iff `g` is the weak derivative of `v`. -/
theorem mem_graph_weakDerivOp (hU : IsOpen U) {v g : L2 U} :
    (v, g) ∈ (weakDerivOp U).graph ↔ HasWeakDerivL2 U v g := by
  rw [weakDerivOp_graph hU]
  constructor
  · rintro ⟨p, hp, hpe⟩
    have : p = WithLp.toLp 2 (v, g) := by rw [← hpe]; rfl
    rw [this] at hp
    exact hp
  · intro h
    exact ⟨WithLp.toLp 2 (v, g), h, rfl⟩

/-- **The weak derivative is a closed operator** in `L²(U)`. -/
theorem weakDerivOp_isClosed (hU : IsOpen U) : (weakDerivOp U).IsClosed := by
  unfold LinearPMap.IsClosed
  rw [weakDerivOp_graph hU, Submodule.map_coe]
  have e : ⇑(WithLp.linearEquiv 2 ℂ (L2 U × L2 U)).toLinearMap
      = ⇑(WithLp.prodContinuousLinearEquiv 2 ℂ (L2 U) (L2 U)) := rfl
  rw [e, ContinuousLinearEquiv.image_eq_preimage_symm]
  exact isClosed_W12Graph.preimage
    (WithLp.prodContinuousLinearEquiv 2 ℂ (L2 U) (L2 U)).symm.continuous

/-! ### `H¹₀(U) ⊆ W^{1,2}(U)` -/

/-- **`∂ₓv` is the weak derivative of `v ∈ H¹₀(U)`.** -/
theorem hasWeakDerivL2_dx (v : H10 U) : HasWeakDerivL2 U (val U v) (dx U v) := by
  rw [hasWeakDerivL2_iff_inner]
  intro ψ hψ hc hs
  have hψ' := IsTestFun.ofReal hψ hc hs
  have hG : ∀ x, HasDerivAt (fun y => (ψ y : ℂ)) ((deriv ψ x : ℝ) : ℂ) x := fun x =>
    ((hψ.differentiable (by simp) x).hasDerivAt).ofReal_comp
  have hg : Continuous fun x => ((deriv ψ x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hψ.continuous_deriv (by simp))
  have hgm : MemLp (fun x => ((deriv ψ x : ℝ) : ℂ)) 2 (volume.restrict U) :=
    (hg.memLp_of_hasCompactSupport (hc.deriv.comp_left Complex.ofReal_zero)).restrict U
  have key := inner_dx_eq hG hg hψ'.memLp hgm v
  have e1 : toL2 U (fun y => (ψ y : ℂ)) hψ'.memLp = val U (ofTest hψ') := rfl
  have e2 : toL2 U (fun x => ((deriv ψ x : ℝ) : ℂ)) hgm = dx U (ofTest hψ') := by
    apply Lp.ext
    filter_upwards [coe_toL2 _ hgm, dx_ofTest hψ'] with x h1 h2
    rw [h1, h2, deriv_ofReal (hψ.differentiable (by simp))]
  rw [e1, e2] at key
  have key' := congrArg (starRingEnd ℂ) key
  rw [inner_conj_symm, map_neg, inner_conj_symm] at key'
  rw [key', neg_neg]

/-- **`H¹₀(U) ⊆ W^{1,2}(U)`**: the graph of `∂ₓ` on `H¹₀(U)` lies in `W^{1,2}(U)`. -/
theorem H10Graph_le_W12Graph : H10Graph U ≤ W12Graph U := fun p hp =>
  hasWeakDerivL2_dx (H10.mk p hp)

/-! ### Complex test functions -/

section ComplexTest

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G]
  [OpensMeasurableSpace G] {ν : Measure G} [IsFiniteMeasureOnCompacts ν] {S : Set G}

omit [NormedSpace ℝ G] in
/-- `c f` is integrable for `c` continuous with compact support and `f ∈ L²`. -/
theorem integrable_mul_of_memLp {c : G → ℂ} (hc : Continuous c) (hcc : HasCompactSupport c)
    {f : G → ℂ} (hf : MemLp f 2 ν) : Integrable (fun x => c x * f x) ν :=
  (hc.memLp_of_hasCompactSupport (p := 2) hcc).integrable_mul hf

/-- An identity `∫ v Dψ e = -∫ f ψ` for all real `ψ ∈ C_c^∞` supported in `S` holds for all
complex `ψ ∈ C_c^∞` supported in `S` (real and imaginary parts). -/
theorem integral_fderiv_mul_of_real {v f : G → ℂ}
    (hv : MemLp v 2 ν) (hf : MemLp f 2 ν)
    (e : G)
    (h : ∀ ψ : G → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ S → ∫ x, ((fderiv ℝ ψ x e : ℝ) : ℂ) * v x ∂ν = -∫ x, (ψ x : ℂ) * f x ∂ν)
    {φ : G → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ S) : ∫ x, fderiv ℝ φ x e * v x ∂ν = -∫ x, φ x * f x ∂ν := by
  have hre : ContDiff ℝ ∞ fun x => (φ x).re := Complex.reCLM.contDiff.comp hφ
  have him : ContDiff ℝ ∞ fun x => (φ x).im := Complex.imCLM.contDiff.comp hφ
  have hcre : HasCompactSupport fun x => (φ x).re := hc.comp_left Complex.zero_re
  have hcim : HasCompactSupport fun x => (φ x).im := hc.comp_left Complex.zero_im
  have h1 := h _ hre hcre ((tsupport_comp_subset Complex.zero_re φ).trans hs)
  have h2 := h _ him hcim ((tsupport_comp_subset Complex.zero_im φ).trans hs)
  have hd : ∀ x, HasFDerivAt φ (fderiv ℝ φ x) x := fun x =>
    (hφ.differentiable (by simp) x).hasFDerivAt
  have dre : ∀ x, fderiv ℝ (fun x => (φ x).re) x e = (fderiv ℝ φ x e).re := fun x => by
    rw [show (fun x => (φ x).re) = ⇑Complex.reCLM ∘ φ from rfl,
      (Complex.reCLM.hasFDerivAt.comp x (hd x)).fderiv]
    rfl
  have dim : ∀ x, fderiv ℝ (fun x => (φ x).im) x e = (fderiv ℝ φ x e).im := fun x => by
    rw [show (fun x => (φ x).im) = ⇑Complex.imCLM ∘ φ from rfl,
      (Complex.imCLM.hasFDerivAt.comp x (hd x)).fderiv]
    rfl
  simp only [dre, dim] at h1 h2
  have hφ' : Continuous fun x => fderiv ℝ φ x e :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ'c : HasCompactSupport fun x => fderiv ℝ φ x e :=
    (hc.fderiv ℝ).comp_left (g := fun L : G →L[ℝ] ℂ => L e) (by simp)
  have ci : ∀ {c : G → ℝ}, Continuous c → HasCompactSupport c →
      ∀ {f : G → ℂ}, MemLp f 2 ν →
        Integrable (fun x => (c x : ℂ) * f x) ν :=
    fun hc0 hcc _ hf => integrable_mul_of_memLp (Complex.continuous_ofReal.comp hc0)
      (hcc.comp_left Complex.ofReal_zero) hf
  have i1 := ci (c := fun x => (fderiv ℝ φ x e).re) (Complex.continuous_re.comp hφ')
    (hφ'c.comp_left Complex.zero_re) hv
  have i2 := ci (c := fun x => (fderiv ℝ φ x e).im) (Complex.continuous_im.comp hφ')
    (hφ'c.comp_left Complex.zero_im) hv
  have i3 := ci (c := fun x => (φ x).re) (Complex.continuous_re.comp hφ.continuous) hcre hf
  have i4 := ci (c := fun x => (φ x).im) (Complex.continuous_im.comp hφ.continuous) hcim hf
  calc ∫ x, fderiv ℝ φ x e * v x ∂ν
      = ∫ x, (((fderiv ℝ φ x e).re : ℂ) * v x
          + Complex.I * (((fderiv ℝ φ x e).im : ℂ) * v x)) ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        change fderiv ℝ φ x e * v x = _
        conv_lhs => rw [← Complex.re_add_im (fderiv ℝ φ x e)]
        ring
    _ = (∫ x, ((fderiv ℝ φ x e).re : ℂ) * v x ∂ν)
          + Complex.I * ∫ x, ((fderiv ℝ φ x e).im : ℂ) * v x ∂ν := by
        rw [integral_add i1 (i2.const_mul _), integral_const_mul]
    _ = -((∫ x, ((φ x).re : ℂ) * f x ∂ν) + Complex.I * ∫ x, ((φ x).im : ℂ) * f x ∂ν) := by
        rw [h1, h2]; ring
    _ = -∫ x, φ x * f x ∂ν := by
        rw [← integral_const_mul, ← integral_add i3 (i4.const_mul _)]
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        change _ = φ x * f x
        conv_rhs => rw [← Complex.re_add_im (φ x)]
        ring

end ComplexTest

/-- **The weak derivative with complex test functions**: `g` is the weak derivative of `v` iff
`∫_U v φ' = -∫_U g φ` for every complex `φ ∈ C_c^∞(U;ℂ)`. -/
theorem hasWeakDerivL2_iff_complex {v g : L2 U} : HasWeakDerivL2 U v g ↔
    ∀ φ : ℝ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x in U, deriv φ x * v x = -∫ x in U, φ x * g x := by
  constructor
  · intro h φ hφ hc hs
    exact integral_fderiv_mul_of_real (Lp.memLp v) (Lp.memLp g) 1 h hφ hc hs
  · intro h ψ hψ hc hs
    have := h (fun x => (ψ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hψ)
      (hc.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero ψ).trans hs)
    simpa only [deriv_ofReal (hψ.differentiable (by simp))] using this

/-! ### Mollification -/

section Mollify

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

/-- **Mollification.**  A `C¹` function `φ : G → ℂ` with compact support in an open set `U` of a
finite-dimensional real normed space is, together with its derivative, a uniform limit of
`C^∞` functions supported in a fixed compact set `K ⊆ U`: the convolutions `ρ ⋆ φ` with smooth
bumps `ρ` of small radius. -/
theorem exists_smooth_approx {U : Set G} (hU : IsOpen U) {φ : G → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    ∃ K : Set G, IsCompact K ∧ K ⊆ U ∧ tsupport φ ⊆ K ∧ ∀ ε > 0, ∃ ψ : G → ℂ,
      ContDiff ℝ ∞ ψ ∧ tsupport ψ ⊆ K ∧
        ∀ x, ‖ψ x - φ x‖ ≤ ε ∧ ‖fderiv ℝ ψ x - fderiv ℝ φ x‖ ≤ ε := by
  obtain ⟨δ, hδ, hδU⟩ := hc.isCompact.exists_cthickening_subset_open hU hs
  refine ⟨cthickening δ (tsupport φ), hc.isCompact.cthickening, hδU,
    self_subset_cthickening _, fun ε hε => ?_⟩
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.uniformContinuous_iff.1
    (hc.uniformContinuous_of_continuous hφ.continuous) ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.uniformContinuous_iff.1
    ((hc.fderiv ℝ).uniformContinuous_of_continuous (hφ.continuous_fderiv one_ne_zero)) ε hε
  set r := min δ (min δ₁ δ₂) with hr
  have hr0 : 0 < r := lt_min hδ (lt_min hδ₁ hδ₂)
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure G, μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  let ρ : ContDiffBump (0 : G) := ⟨r / 2, r, half_pos hr0, half_lt_self hr0⟩
  have hρl : LocallyIntegrable (ρ.normed μ) μ := ρ.integrable_normed.locallyIntegrable
  refine ⟨ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] φ, ?_, ?_, fun x => ⟨?_, ?_⟩⟩
  · exact ρ.hasCompactSupport_normed.contDiff_convolution_left _ ρ.contDiff_normed
      hφ.continuous.locallyIntegrable
  · refine closure_minimal ?_ isClosed_cthickening
    refine (support_convolution_subset _).trans ?_
    rw [ρ.support_normed_eq]
    refine (add_subset_add_left (subset_tsupport φ)).trans ?_
    rw [ball_add_zero]
    exact (thickening_subset_cthickening _ _).trans (cthickening_mono (min_le_left _ _) _)
  · rw [← dist_eq_norm]
    exact ρ.dist_normed_convolution_le hφ.continuous.aestronglyMeasurable fun y hy =>
      (h₁ (lt_of_lt_of_le (mem_ball.1 hy) ((min_le_right _ _).trans (min_le_left _ _)))).le
  · have hd := (hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hρl hφ x).fderiv
    have e : (ρ.normed μ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR G, μ] fderiv ℝ φ) x
        = (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] fderiv ℝ φ) x := by
      simp only [convolution]
      congr 1
    rw [hd, e, ← dist_eq_norm]
    exact ρ.dist_normed_convolution_le (hφ.continuous_fderiv one_ne_zero).aestronglyMeasurable
      fun y hy =>
        (h₂ (lt_of_lt_of_le (mem_ball.1 hy) ((min_le_right _ _).trans (min_le_right _ _)))).le

end Mollify

/-! ### `H¹₀(U)` is the closure of `C_c^∞(U)` -/

/-- The graphs `(φ, φ')` of the test functions `φ ∈ C_c^∞(U;ℂ)` (smooth, compactly supported,
`tsupport φ ⊆ U`), in `L²(U) × L²(U)`. -/
def smoothGraph (U : Set ℝ) : Set (WithLp 2 (L2 U × L2 U)) :=
  {p | ∃ φ : ℝ → ℂ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
    ⇑(WithLp.ofLp p).1 =ᵐ[volume.restrict U] φ ∧
    ⇑(WithLp.ofLp p).2 =ᵐ[volume.restrict U] deriv φ}

theorem smoothGraph_subset_testGraph : smoothGraph U ⊆ testGraph U := by
  rintro p ⟨φ, hφ, hc, hs, h1, h2⟩
  exact ⟨φ, hφ.of_le (by exact_mod_cast le_top), hc, hs, h1, h2⟩

theorem smoothGraph_subset_W12Graph : smoothGraph U ⊆ W12Graph U :=
  smoothGraph_subset_testGraph.trans (testGraph_subset_H10.trans H10Graph_le_W12Graph)

/-- A test graph is the pair of the classes of `φ` and `φ'`. -/
theorem eq_toLp_of_ae {p : WithLp 2 (L2 U × L2 U)} {φ : ℝ → ℂ} (hφ : IsTestFun U φ)
    (h1 : ⇑(WithLp.ofLp p).1 =ᵐ[volume.restrict U] φ)
    (h2 : ⇑(WithLp.ofLp p).2 =ᵐ[volume.restrict U] deriv φ) :
    p = WithLp.toLp 2 (toL2 U φ hφ.memLp, toL2 U (deriv φ) hφ.memLp_deriv) := by
  have e1 : (WithLp.ofLp p).1 = toL2 U φ hφ.memLp := by
    apply Lp.ext; filter_upwards [h1, coe_toL2 φ hφ.memLp] with x hx hx'; rw [hx, hx']
  have e2 : (WithLp.ofLp p).2 = toL2 U (deriv φ) hφ.memLp_deriv := by
    apply Lp.ext; filter_upwards [h2, coe_toL2 (deriv φ) hφ.memLp_deriv] with x hx hx'; rw [hx, hx']
  rw [← e1, ← e2]

theorem norm_toLp_prod_le {A B : Type*} [SeminormedAddCommGroup A] [SeminormedAddCommGroup B]
    (a : A) (b : B) : ‖WithLp.toLp 2 (a, b)‖ ≤ ‖a‖ + ‖b‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (a, b))
  have h' : ‖WithLp.toLp 2 (a, b)‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := h
  nlinarith [norm_nonneg (WithLp.toLp 2 (a, b)), norm_nonneg a, norm_nonneg b]

/-- `‖f - g‖_{L²} ≤ η μ(K)^{1/2}` for functions vanishing outside `K` with `‖f - g‖ ≤ η`. -/
theorem norm_toLp_sub_le {X F : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup F] {f g : X → F} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {K : Set X}
    (hK : MeasurableSet K) (hKμ : μ K < ⊤) (hf0 : ∀ x ∉ K, f x = 0) (hg0 : ∀ x ∉ K, g x = 0)
    {η : ℝ} (hη : 0 ≤ η) (hb : ∀ x, ‖f x - g x‖ ≤ η) :
    ‖hf.toLp f - hg.toLp g‖ ≤ η * sqrtMeas μ K := by
  rw [← MemLp.toLp_sub]
  exact norm_toLp_le_of_bound hK hKμ _ hη (fun x _ => hb x) fun x hx => by
    simp [hf0 x hx, hg0 x hx]

/-- Every `C¹_c(U)` graph is a limit of `C_c^∞(U)` graphs, `U` open. -/
theorem testGraph_subset_closure_smoothGraph (hU : IsOpen U) :
    testGraph U ⊆ closure (smoothGraph U) := by
  rintro p ⟨φ, hφ, hc, hs, h1, h2⟩
  have hφt : IsTestFun U φ := ⟨hφ, hc, hs⟩
  obtain ⟨K, hK, hKU, hφK, happrox⟩ := exists_smooth_approx hU hφ hc hs
  rw [eq_toLp_of_ae hφt h1 h2, Metric.mem_closure_iff]
  intro ε hε
  set C := sqrtMeas (volume.restrict U) K with hCdef
  have hC : 0 ≤ C := sqrtMeas_nonneg _ _
  have hKμ : (volume.restrict U) K < ⊤ :=
    (Measure.restrict_apply_le U K).trans_lt hK.measure_lt_top
  set η := ε / (2 * (C + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ψ, hψ, hψK, hb⟩ := happrox η hη0
  have hψt : IsTestFun U ψ :=
    ⟨hψ.of_le (by exact_mod_cast le_top), hK.of_isClosed_subset (isClosed_tsupport ψ) hψK,
      hψK.trans hKU⟩
  refine ⟨WithLp.toLp 2 (toL2 U ψ hψt.memLp, toL2 U (deriv ψ) hψt.memLp_deriv),
    ⟨ψ, hψ, hψt.hasCompactSupport, hψt.tsupport_subset, coe_toL2 ψ hψt.memLp,
      coe_toL2 (deriv ψ) hψt.memLp_deriv⟩, ?_⟩
  have hφ0 : ∀ x ∉ K, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hφK h)
  have hψ0 : ∀ x ∉ K, ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hψK h)
  have hφ0' : ∀ x ∉ K, deriv φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hφK (tsupport_deriv_subset h))
  have hψ0' : ∀ x ∉ K, deriv ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hψK (tsupport_deriv_subset h))
  have n1 := norm_toLp_sub_le hφt.memLp hψt.memLp hK.measurableSet hKμ hφ0 hψ0 hη0.le fun x => by
    rw [norm_sub_rev]; exact (hb x).1
  have n2 := norm_toLp_sub_le hφt.memLp_deriv hψt.memLp_deriv hK.measurableSet hKμ hφ0' hψ0'
    hη0.le fun x => by
    rw [← fderiv_apply_one_eq_deriv, ← fderiv_apply_one_eq_deriv,
      ← sub_apply]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [norm_one, mul_one, norm_sub_rev]
    exact (hb x).2
  rw [dist_eq_norm, ← WithLp.toLp_sub, Prod.mk_sub_mk]
  calc _ ≤ _ := norm_toLp_prod_le _ _
    _ ≤ η * C + η * C := add_le_add n1 n2
    _ = C / (C + 1) * ε := by rw [hη]; field_simp; ring
    _ < 1 * ε := by
        gcongr
        rw [div_lt_one (by positivity)]
        linarith
    _ = ε := one_mul ε

/-- **`H¹₀(U)` is the closure of `C_c^∞(U)`.**  For `U` open, the graph closure of the
`C¹_c(U)` functions, which defines `H10Graph U`, is also the closure of the graphs of the
`C_c^∞(U)` functions. -/
theorem H10Graph_eq_closure_smoothGraph (hU : IsOpen U) :
    H10Graph U = (Submodule.span ℂ (smoothGraph U)).topologicalClosure := by
  refine le_antisymm ?_
    (Submodule.topologicalClosure_mono (Submodule.span_mono smoothGraph_subset_testGraph))
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 fun p hp => ?_)
    (Submodule.isClosed_topologicalClosure _)
  rw [SetLike.mem_coe, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact closure_mono Submodule.subset_span (testGraph_subset_closure_smoothGraph hU hp)

/-- A continuous semilinear map on `L²(U) × L²(U)` vanishing on the graphs of the `C_c^∞(U)`
functions vanishes on `H¹₀(U)`, `U` open. -/
theorem eq_zero_of_smoothGraph (hU : IsOpen U) {σ : ℂ →+* ℂ} {F : Type*} [NormedAddCommGroup F]
    [Module ℂ F] (Λ : WithLp 2 (L2 U × L2 U) →SL[σ] F) (h : ∀ p ∈ smoothGraph U, Λ p = 0)
    (v : H10 U) : Λ (H10.pair v) = 0 := by
  have hle : H10Graph U ≤ LinearMap.ker (Λ : WithLp 2 (L2 U × L2 U) →ₛₗ[σ] F) := by
    rw [H10Graph_eq_closure_smoothGraph hU]
    exact Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 fun p hp => h p hp)
      (ContinuousLinearMap.isClosed_ker Λ)
  exact hle (H10.pair_mem v)

/-! ### `H¹₀(U)` inside `W^{1,2}(U)` -/

/-- The isometric inclusion `H¹₀(U) ↪ W^{1,2}(U)`. -/
def H10toW12 (U : Set ℝ) : H10 U →ₗᵢ[ℂ] W12Graph U where
  toLinearMap := Submodule.inclusion H10Graph_le_W12Graph
  norm_map' _ := rfl

theorem coe_H10toW12 (v : H10 U) : ((H10toW12 U v : W12Graph U) : WithLp 2 (L2 U × L2 U))
    = H10.pair v := rfl

/-- The graphs of the `C_c^∞(U)` functions, as elements of `W^{1,2}(U)`. -/
def smoothW12 (U : Set ℝ) : Set (W12Graph U) := Subtype.val ⁻¹' smoothGraph U

/-- **`H¹₀(U)` is the closure of `C_c^∞(U)` in `W^{1,2}(U)`**, the textbook definition: for `U`
open, the range of the isometric inclusion `H¹₀(U) ↪ W^{1,2}(U)` is the closure in `W^{1,2}(U)` of
(the span of) the `C_c^∞(U)` functions. -/
theorem range_H10toW12 (hU : IsOpen U) :
    LinearMap.range (H10toW12 U).toLinearMap
      = (Submodule.span ℂ (smoothW12 U)).topologicalClosure := by
  have himg : Subtype.val '' ((Submodule.span ℂ (smoothW12 U) : Submodule ℂ (W12Graph U)) :
      Set (W12Graph U)) = (Submodule.span ℂ (smoothGraph U) : Set (WithLp 2 (L2 U × L2 U))) := by
    have hS : (W12Graph U).subtype '' smoothW12 U = smoothGraph U := by
      ext q
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hq
        exact ⟨⟨q, smoothGraph_subset_W12Graph hq⟩, hq, rfl⟩
    have h := Submodule.map_span (W12Graph U).subtype (smoothW12 U)
    rw [hS] at h
    rw [← h, Submodule.map_coe, Submodule.coe_subtype]
  ext x
  have hL : x ∈ LinearMap.range (H10toW12 U).toLinearMap ↔
      (x : WithLp 2 (L2 U × L2 U)) ∈ H10Graph U := by
    change x ∈ LinearMap.range (Submodule.inclusion H10Graph_le_W12Graph) ↔ _
    rw [Submodule.range_inclusion]
    rfl
  rw [hL, H10Graph_eq_closure_smoothGraph hU, ← SetLike.mem_coe, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, mem_preimage, himg]

/-! ### The weak derivative tested against `H¹₀(U)` -/

/-- **`g` is the weak derivative of `v` iff `⟨∂ₓw, v⟩ = -⟨w, g⟩` for all `w ∈ H¹₀(U)`**, `U`
open.  (The test functions are dense in `H¹₀(U)`, and the identity is the definition of the
weak derivative for the real `C_c^∞(U)` functions.) -/
theorem hasWeakDerivL2_iff_forall_H10 (hU : IsOpen U) {v g : L2 U} :
    HasWeakDerivL2 U v g ↔ ∀ w : H10 U, ⟪dx U w, v⟫_ℂ = -⟪val U w, g⟫_ℂ := by
  constructor
  · intro h w
    rw [hasWeakDerivL2_iff_complex] at h
    set Λ : WithLp 2 (L2 U × L2 U) →L⋆[ℂ] ℂ :=
      (innerSLFlip ℂ v).comp (WithLp.sndL 2 ℂ (L2 U) (L2 U)) +
        (innerSLFlip ℂ g).comp (WithLp.fstL 2 ℂ (L2 U) (L2 U)) with hΛ
    have hΛp : ∀ p, Λ p = ⟪(WithLp.ofLp p).2, v⟫_ℂ + ⟪(WithLp.ofLp p).1, g⟫_ℂ := fun p => rfl
    have h0 : ∀ p ∈ smoothGraph U, Λ p = 0 := by
      rintro p ⟨φ, hφ, hc, hs, h1, h2⟩
      have hφd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x =>
        (hφ.differentiable (by simp) x).hasDerivAt
      have hχ : ContDiff ℝ ∞ fun x => conj (φ x) :=
        (Complex.conjCLE.toContinuousLinearMap.contDiff).comp hφ
      have hχd : ∀ x, deriv (fun x => conj (φ x)) x = conj (deriv φ x) := fun x =>
        (hφd x).star.deriv
      have key := h (fun x => conj (φ x)) hχ (hc.comp_left (map_zero _))
        ((tsupport_comp_subset (map_zero _) φ).trans hs)
      simp only [hχd] at key
      have e1 : ∫ x in U, conj ((WithLp.ofLp p).2 x) * v x = ∫ x in U, conj (deriv φ x) * v x :=
        integral_congr_ae (by filter_upwards [h2] with x hx; rw [hx])
      have e2 : ∫ x in U, conj ((WithLp.ofLp p).1 x) * g x = ∫ x in U, conj (φ x) * g x :=
        integral_congr_ae (by filter_upwards [h1] with x hx; rw [hx])
      rw [hΛp, inner_L2_eq, inner_L2_eq, e1, e2, key, neg_add_cancel]
    have := eq_zero_of_smoothGraph hU Λ h0 w
    rw [hΛp] at this
    exact eq_neg_of_add_eq_zero_left this
  · intro h
    rw [hasWeakDerivL2_iff_inner]
    intro ψ hψ hc hs
    exact h _

end LionsC12
