module

public import LionsC12.Domains.Spaces
public import LionsC12.Spaces.Sobolev

/-!
# `W^{1,2}(Ω)` and `H¹₀(Ω)` through weak gradients, on an open set `Ω ⊆ ℝ^d`

The `d`-dimensional analogue of `LionsC12.Spaces.Sobolev`: the statement-level `H¹₀(Ω;ℂ)`, the
closure of the graphs `(φ, ∇φ)` of the `C¹_c(Ω;ℂ)` functions in `L²(Ω) × L²(Ω;ℂ^d)`, is the
closure of `C_c^∞(Ω)` in the Sobolev space `W^{1,2}(Ω)` defined by weak gradients.

* `HasWeakGradL2 Ω v G` — `G ∈ L²(Ω;ℂ^d)` is the weak gradient of `v ∈ L²(Ω)` on `Ω`:
  `∫_Ω v ∂ᵢφ = -∫_Ω Gᵢ φ` for every real `φ ∈ C_c^∞(Ω)` and every `i`;
  `hasWeakGradL2_iff_complex` — the same with complex test functions;
* `W12ΩGraph d Ω` — `W^{1,2}(Ω)` with its norm `(‖v‖² + ‖G‖²)^{1/2}`, a closed subspace of
  `L²(Ω) × L²(Ω;ℂ^d)` (`isClosed_W12ΩGraph`); the weak gradient is unique on an open set
  (`hasWeakGradL2_unique`);
* `hasWeakGradL2_gradΩ`, `H10ΩGraph_le_W12ΩGraph` — `∇v` is the weak gradient of `v ∈ H¹₀(Ω)`;
* `H10ΩGraph_eq_closure_smoothGraphΩ` — `H¹₀(Ω)` is the closure of the graphs of the
  `C_c^∞(Ω)` functions, `Ω` open (by the mollification `exists_smooth_approx`);
  `range_H10ΩtoW12Ω` — the isometric inclusion `H¹₀(Ω) ↪ W^{1,2}(Ω)` has for range the closure
  of `C_c^∞(Ω)` in `W^{1,2}(Ω)`, the textbook definition of `H¹₀(Ω)`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology Metric LionsC12Challenge
open scoped InnerProductSpace ComplexConjugate ContDiff

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Weak gradients -/

/-- `G ∈ L²(Ω;ℂ^d)` is the weak gradient of `v ∈ L²(Ω)` on `Ω`: `∫_Ω v ∂ᵢφ = -∫_Ω Gᵢ φ` for
every real `φ ∈ C_c^∞(Ω)` (smooth, compactly supported, `tsupport φ ⊆ Ω`) and every `i`, where
`∂ᵢφ(x) = Dφ(x) eᵢ`. -/
def HasWeakGradL2 (Ω : Set (EuclideanSpace ℝ (Fin d))) (v : L2Ω d Ω) (G : L2Ωvec d Ω) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∀ i : Fin d, ∫ x in Ω, ((fderiv ℝ φ x (EuclideanSpace.single i 1) : ℝ) : ℂ) * v x
      = -∫ x in Ω, (φ x : ℂ) * G x i

section RealTest

variable {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)

include hψ hc in
theorem memLp_partial (i : Fin d) :
    MemLp (fun x => ((fderiv ℝ ψ x (EuclideanSpace.single i 1) : ℝ) : ℂ)) 2
      (volume.restrict Ω) := by
  have hcont : Continuous fun x => ((fderiv ℝ ψ x (EuclideanSpace.single i 1) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
  refine (hcont.memLp_of_hasCompactSupport ?_).restrict Ω
  exact (hc.fderiv ℝ).comp_left (g := fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ =>
    ((L (EuclideanSpace.single i 1) : ℝ) : ℂ)) (by simp)

include hψ hc in
theorem memLp_smul_single (i : Fin d) :
    MemLp (fun x => (ψ x : ℂ) • EuclideanSpace.single i (1 : ℂ)) 2 (volume.restrict Ω) := by
  have hcont : Continuous fun x => (ψ x : ℂ) • EuclideanSpace.single i (1 : ℂ) :=
    (Complex.continuous_ofReal.comp hψ.continuous).smul continuous_const
  exact (hcont.memLp_of_hasCompactSupport
    (hc.comp_left Complex.ofReal_zero).smul_right).restrict Ω

/-- `∫_Ω ∂ᵢψ f = ⟨∂ᵢψ, f⟩` for a real test function `ψ`. -/
theorem integral_partial_mul_eq_inner (i : Fin d) (f : L2Ω d Ω) :
    ∫ x in Ω, ((fderiv ℝ ψ x (EuclideanSpace.single i 1) : ℝ) : ℂ) * f x
      = ⟪toL2Ω Ω _ (memLp_partial hψ hc i), f⟫_ℂ := by
  rw [inner_L2Ω_eq]
  refine integral_congr_ae ?_
  filter_upwards [coe_toL2Ω _ (memLp_partial (Ω := Ω) hψ hc i)] with x hx
  rw [hx, Complex.conj_ofReal]

/-- `∫_Ω ψ Gᵢ = ⟨ψ eᵢ, G⟩` for a real test function `ψ`. -/
theorem integral_mul_apply_eq_inner (i : Fin d) (G : L2Ωvec d Ω) :
    ∫ x in Ω, (ψ x : ℂ) * G x i = ⟪toL2Ωvec Ω _ (memLp_smul_single hψ hc i), G⟫_ℂ := by
  rw [inner_L2Ωvec_eq]
  refine integral_congr_ae ?_
  filter_upwards [coe_toL2Ωvec _ (memLp_smul_single (Ω := Ω) hψ hc i)] with x hx
  rw [hx, inner_smul_left, EuclideanSpace.inner_single_left, map_one, one_mul,
    Complex.conj_ofReal]

end RealTest

/-- The weak gradient in terms of inner products with `∂ᵢψ` and `ψ eᵢ`. -/
theorem hasWeakGradL2_iff_inner {v : L2Ω d Ω} {G : L2Ωvec d Ω} : HasWeakGradL2 Ω v G ↔
    ∀ (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ),
      tsupport ψ ⊆ Ω → ∀ i : Fin d, ⟪toL2Ω Ω _ (memLp_partial hψ hc i), v⟫_ℂ
        = -⟪toL2Ωvec Ω _ (memLp_smul_single hψ hc i), G⟫_ℂ := by
  refine forall_congr' fun ψ => forall_congr' fun hψ => forall_congr' fun hc =>
    forall_congr' fun hs => forall_congr' fun i => ?_
  rw [integral_partial_mul_eq_inner hψ hc i, integral_mul_apply_eq_inner hψ hc i]

/-- **The weak gradient with complex test functions**: `G` is the weak gradient of `v` iff
`∫_Ω v ∂ᵢφ = -∫_Ω Gᵢ φ` for every complex `φ ∈ C_c^∞(Ω;ℂ)` and every `i`. -/
theorem hasWeakGradL2_iff_complex {v : L2Ω d Ω} {G : L2Ωvec d Ω} : HasWeakGradL2 Ω v G ↔
    ∀ φ : EuclideanSpace ℝ (Fin d) → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∀ i : Fin d, ∫ x in Ω, fderiv ℝ φ x (EuclideanSpace.single i 1) * v x
        = -∫ x in Ω, φ x * G x i := by
  constructor
  · intro h φ hφ hc hs i
    exact integral_fderiv_mul_of_real (Lp.memLp v)
      ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ).comp_memLp G) _
      (fun ψ hψ hcψ hsψ => h ψ hψ hcψ hsψ i) hφ hc hs
  · intro h ψ hψ hc hs i
    have := h (fun x => (ψ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hψ)
      (hc.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero ψ).trans hs) i
    simpa only [IsTestFunΩ.fderiv_ofReal (hψ.differentiable (by simp))] using this

/-! ### The space `W^{1,2}(Ω)` -/

/-- `W^{1,2}(Ω)`, as the subspace of `L²(Ω) × L²(Ω;ℂ^d)` of the pairs `(v, G)` of a function
and its weak gradient; its norm is `(‖v‖² + ‖G‖²)^{1/2}`. -/
def W12ΩGraph (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    Submodule ℂ (WithLp 2 (L2Ω d Ω × L2Ωvec d Ω)) where
  carrier := {p | HasWeakGradL2 Ω (WithLp.ofLp p).1 (WithLp.ofLp p).2}
  zero_mem' := by
    simp only [mem_ofPred_eq, hasWeakGradL2_iff_inner, WithLp.ofLp_zero, Prod.fst_zero,
      Prod.snd_zero, inner_zero_right, neg_zero, implies_true]
  add_mem' := by
    intro p q hp hq
    simp only [mem_ofPred_eq, hasWeakGradL2_iff_inner, WithLp.ofLp_add, Prod.fst_add,
      Prod.snd_add, inner_add_right] at hp hq ⊢
    intro ψ hψ hc hs i
    rw [hp ψ hψ hc hs i, hq ψ hψ hc hs i, neg_add]
  smul_mem' := by
    intro c p hp
    simp only [mem_ofPred_eq, hasWeakGradL2_iff_inner, WithLp.ofLp_smul, Prod.smul_fst,
      Prod.smul_snd, inner_smul_right] at hp ⊢
    intro ψ hψ hc hs i
    rw [hp ψ hψ hc hs i, mul_neg]

theorem mem_W12ΩGraph {p : WithLp 2 (L2Ω d Ω × L2Ωvec d Ω)} :
    p ∈ W12ΩGraph d Ω ↔ HasWeakGradL2 Ω (WithLp.ofLp p).1 (WithLp.ofLp p).2 := Iff.rfl

theorem toLp_mem_W12ΩGraph {v : L2Ω d Ω} {G : L2Ωvec d Ω} :
    WithLp.toLp 2 (v, G) ∈ W12ΩGraph d Ω ↔ HasWeakGradL2 Ω v G := Iff.rfl

/-- `W^{1,2}(Ω)` is closed in `L²(Ω) × L²(Ω;ℂ^d)`. -/
theorem isClosed_W12ΩGraph :
    IsClosed (W12ΩGraph d Ω : Set (WithLp 2 (L2Ω d Ω × L2Ωvec d Ω))) := by
  have e : (W12ΩGraph d Ω : Set (WithLp 2 (L2Ω d Ω × L2Ωvec d Ω))) =
      ⋂ (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
        (_ : tsupport ψ ⊆ Ω) (i : Fin d),
        {p | ⟪toL2Ω Ω _ (memLp_partial hψ hc i), (WithLp.ofLp p).1⟫_ℂ
          = -⟪toL2Ωvec Ω _ (memLp_smul_single hψ hc i), (WithLp.ofLp p).2⟫_ℂ} := by
    ext p
    simp only [SetLike.mem_coe, mem_W12ΩGraph, hasWeakGradL2_iff_inner, mem_iInter,
      mem_ofPred_eq]
  rw [e]
  refine isClosed_iInter fun ψ => isClosed_iInter fun hψ => isClosed_iInter fun hc =>
    isClosed_iInter fun _ => isClosed_iInter fun i => isClosed_eq ?_ ?_
  · exact continuous_const.inner (WithLp.fstL 2 ℂ (L2Ω d Ω) (L2Ωvec d Ω)).continuous
  · exact (continuous_const.inner (WithLp.sndL 2 ℂ (L2Ω d Ω) (L2Ωvec d Ω)).continuous).neg

instance instCompleteSpaceW12ΩGraph (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    CompleteSpace (W12ΩGraph d Ω) :=
  haveI : IsClosed (W12ΩGraph d Ω : Set (WithLp 2 (L2Ω d Ω × L2Ωvec d Ω))) := isClosed_W12ΩGraph
  IsClosed.completeSpace_coe

/-- **Uniqueness of the weak gradient** on an open set: `(0, G) ∈ W^{1,2}(Ω)` forces `G = 0`. -/
theorem eq_zero_of_hasWeakGradL2_zero (hΩ : IsOpen Ω) {G : L2Ωvec d Ω}
    (h : HasWeakGradL2 Ω 0 G) : G = 0 := by
  have hcomp : ∀ i : Fin d, (fun x => G x i) =ᵐ[volume.restrict Ω] 0 := by
    intro i
    have hm : MemLp (fun x => G x i) 2 (volume.restrict Ω) :=
      (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ).comp_memLp G
    refine ae_eq_zero_of_forall_smoothΩ hΩ hm fun ψ hψ hc hs => ?_
    have key := h ψ hψ hc hs i
    rw [integral_partial_mul_eq_inner hψ hc i, inner_zero_right] at key
    exact neg_eq_zero.1 key.symm
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [(ae_all_iff (ι := Fin d)).2 hcomp] with x hx
  ext i
  simpa using hx i

/-- The weak gradient is unique on an open set. -/
theorem hasWeakGradL2_unique (hΩ : IsOpen Ω) {v : L2Ω d Ω} {G₁ G₂ : L2Ωvec d Ω}
    (h₁ : HasWeakGradL2 Ω v G₁) (h₂ : HasWeakGradL2 Ω v G₂) : G₁ = G₂ := by
  have h := (W12ΩGraph d Ω).sub_mem (toLp_mem_W12ΩGraph.2 h₁) (toLp_mem_W12ΩGraph.2 h₂)
  rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self] at h
  exact sub_eq_zero.1 (eq_zero_of_hasWeakGradL2_zero hΩ h)

/-! ### `H¹₀(Ω) ⊆ W^{1,2}(Ω)` -/

/-- **`∇v` is the weak gradient of `v ∈ H¹₀(Ω)`.** -/
theorem hasWeakGradL2_gradΩ (w : H10Ω d Ω) : HasWeakGradL2 Ω (valΩ d Ω w) (gradΩ d Ω w) := by
  intro ψ hψ hc hs i
  have key := congrArg (starRingEnd ℂ) (inner_gradΩ_single hψ hc hs i w)
  rw [map_add, ← integral_conj, ← integral_conj, map_zero] at key
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at key
  rw [eq_neg_iff_add_eq_zero, add_comm, ← key]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-- **`H¹₀(Ω) ⊆ W^{1,2}(Ω)`**: the graph of `∇` on `H¹₀(Ω)` lies in `W^{1,2}(Ω)`. -/
theorem H10ΩGraph_le_W12ΩGraph : H10ΩGraph d Ω ≤ W12ΩGraph d Ω := fun p hp =>
  hasWeakGradL2_gradΩ (H10Ω.mk p hp)

/-! ### `H¹₀(Ω)` is the closure of `C_c^∞(Ω)` -/

/-- The graphs `(φ, ∇φ)` of the test functions `φ ∈ C_c^∞(Ω;ℂ)` (smooth, compactly supported,
`tsupport φ ⊆ Ω`), in `L²(Ω) × L²(Ω;ℂ^d)`. -/
def smoothGraphΩ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    Set (WithLp 2 (L2Ω d Ω × L2Ωvec d Ω)) :=
  {p | ∃ φ : EuclideanSpace ℝ (Fin d) → ℂ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ Ω ∧ ⇑(WithLp.ofLp p).1 =ᵐ[volume.restrict Ω] φ ∧
    ⇑(WithLp.ofLp p).2 =ᵐ[volume.restrict Ω] grad φ}

theorem smoothGraphΩ_subset_testGraphΩ : smoothGraphΩ d Ω ⊆ testGraphΩ d Ω := by
  rintro p ⟨φ, hφ, hc, hs, h1, h2⟩
  exact ⟨φ, hφ.of_le (by exact_mod_cast le_top), hc, hs, h1, h2⟩

theorem smoothGraphΩ_subset_W12ΩGraph : smoothGraphΩ d Ω ⊆ W12ΩGraph d Ω :=
  smoothGraphΩ_subset_testGraphΩ.trans (testGraphΩ_subset.trans H10ΩGraph_le_W12ΩGraph)

/-- The gradient `∇φ(x)` as a continuous linear function of the derivative `Dφ(x)`. -/
def gradCLM (d : ℕ) : (EuclideanSpace ℝ (Fin d) →L[ℝ] ℂ) →L[ℝ] EuclideanSpace ℂ (Fin d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun L => WithLp.toLp 2 fun i => L (EuclideanSpace.single i 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem grad_eq_gradCLM (φ : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d)) :
    grad φ x = gradCLM d (fderiv ℝ φ x) := rfl

/-- A test graph is the pair of the classes of `φ` and `∇φ`. -/
theorem eq_toLp_of_aeΩ {p : WithLp 2 (L2Ω d Ω × L2Ωvec d Ω)}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : IsTestFunΩ Ω φ)
    (h1 : ⇑(WithLp.ofLp p).1 =ᵐ[volume.restrict Ω] φ)
    (h2 : ⇑(WithLp.ofLp p).2 =ᵐ[volume.restrict Ω] grad φ) :
    p = WithLp.toLp 2 (toL2Ω Ω φ hφ.memLp, toL2Ωvec Ω (grad φ) hφ.memLp_grad) := by
  have e1 : (WithLp.ofLp p).1 = toL2Ω Ω φ hφ.memLp := by
    apply Lp.ext; filter_upwards [h1, coe_toL2Ω φ hφ.memLp] with x hx hx'; rw [hx, hx']
  have e2 : (WithLp.ofLp p).2 = toL2Ωvec Ω (grad φ) hφ.memLp_grad := by
    apply Lp.ext
    filter_upwards [h2, coe_toL2Ωvec (grad φ) hφ.memLp_grad] with x hx hx'; rw [hx, hx']
  rw [← e1, ← e2]

/-- Every `C¹_c(Ω)` graph is a limit of `C_c^∞(Ω)` graphs, `Ω` open. -/
theorem testGraphΩ_subset_closure_smoothGraphΩ (hΩ : IsOpen Ω) :
    testGraphΩ d Ω ⊆ closure (smoothGraphΩ d Ω) := by
  rintro p ⟨φ, hφ, hc, hs, h1, h2⟩
  have hφt : IsTestFunΩ Ω φ := ⟨hφ, hc, hs⟩
  obtain ⟨K, hK, hKΩ, hφK, happrox⟩ := exists_smooth_approx hΩ hφ hc hs
  rw [eq_toLp_of_aeΩ hφt h1 h2, Metric.mem_closure_iff]
  intro ε hε
  set C := sqrtMeas (volume.restrict Ω) K with hCdef
  have hC : 0 ≤ C := sqrtMeas_nonneg _ _
  have hKμ : (volume.restrict Ω) K < ⊤ :=
    (Measure.restrict_apply_le Ω K).trans_lt hK.measure_lt_top
  set B := ‖gradCLM d‖ + 1 with hB
  have hB1 : 1 ≤ B := by simp only [hB]; linarith [norm_nonneg (gradCLM d)]
  set η := ε / (2 * (C + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ψ, hψ, hψK, hb⟩ := happrox (η / B) (by positivity)
  have hψt : IsTestFunΩ Ω ψ :=
    ⟨hψ.of_le (by exact_mod_cast le_top), hK.of_isClosed_subset (isClosed_tsupport ψ) hψK,
      hψK.trans hKΩ⟩
  refine ⟨WithLp.toLp 2 (toL2Ω Ω ψ hψt.memLp, toL2Ωvec Ω (grad ψ) hψt.memLp_grad),
    ⟨ψ, hψ, hψt.hasCompactSupport, hψt.tsupport_subset, coe_toL2Ω ψ hψt.memLp,
      coe_toL2Ωvec (grad ψ) hψt.memLp_grad⟩, ?_⟩
  have hφ0 : ∀ x ∉ K, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hφK h)
  have hψ0 : ∀ x ∉ K, ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hψK h)
  have hφ0' : ∀ x ∉ K, grad φ x = 0 := fun x hx => grad_eq_zero_of_fderiv
    (image_eq_zero_of_notMem_tsupport fun h => hx (hφK (tsupport_fderiv_subset ℝ h)))
  have hψ0' : ∀ x ∉ K, grad ψ x = 0 := fun x hx => grad_eq_zero_of_fderiv
    (image_eq_zero_of_notMem_tsupport fun h => hx (hψK (tsupport_fderiv_subset ℝ h)))
  have hηB : η / B ≤ η := div_le_self hη0.le hB1
  have n1 := norm_toLp_sub_le hφt.memLp hψt.memLp hK.measurableSet hKμ hφ0 hψ0 hη0.le
    fun x => by rw [norm_sub_rev]; exact (hb x).1.trans hηB
  have n2 := norm_toLp_sub_le hφt.memLp_grad hψt.memLp_grad hK.measurableSet hKμ hφ0' hψ0'
    hη0.le fun x => by
      rw [grad_eq_gradCLM, grad_eq_gradCLM, ← map_sub]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [norm_sub_rev]
      calc ‖gradCLM d‖ * ‖fderiv ℝ ψ x - fderiv ℝ φ x‖ ≤ B * (η / B) := by
            gcongr
            · linarith
            · exact (hb x).2
        _ = η := by field_simp
  rw [dist_eq_norm, ← WithLp.toLp_sub, Prod.mk_sub_mk]
  calc _ ≤ _ := norm_toLp_prod_le _ _
    _ ≤ η * C + η * C := add_le_add n1 n2
    _ = C / (C + 1) * ε := by rw [hη]; field_simp; ring
    _ < 1 * ε := by
        gcongr
        rw [div_lt_one (by positivity)]
        linarith
    _ = ε := one_mul ε

/-- **`H¹₀(Ω)` is the closure of `C_c^∞(Ω)`.**  For `Ω` open, the graph closure of the
`C¹_c(Ω)` functions, which defines `H10ΩGraph d Ω`, is also the closure of the graphs of the
`C_c^∞(Ω)` functions. -/
theorem H10ΩGraph_eq_closure_smoothGraphΩ (hΩ : IsOpen Ω) :
    H10ΩGraph d Ω = (Submodule.span ℂ (smoothGraphΩ d Ω)).topologicalClosure := by
  refine le_antisymm ?_
    (Submodule.topologicalClosure_mono (Submodule.span_mono smoothGraphΩ_subset_testGraphΩ))
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 fun p hp => ?_)
    (Submodule.isClosed_topologicalClosure _)
  rw [SetLike.mem_coe, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact closure_mono Submodule.subset_span (testGraphΩ_subset_closure_smoothGraphΩ hΩ hp)

/-- A continuous semilinear map on `L²(Ω) × L²(Ω;ℂ^d)` vanishing on the graphs of the
`C_c^∞(Ω)` functions vanishes on `H¹₀(Ω)`, `Ω` open. -/
theorem eq_zero_of_smoothGraphΩ (hΩ : IsOpen Ω) {σ : ℂ →+* ℂ} {F : Type*}
    [NormedAddCommGroup F] [Module ℂ F] (Λ : WithLp 2 (L2Ω d Ω × L2Ωvec d Ω) →SL[σ] F)
    (h : ∀ p ∈ smoothGraphΩ d Ω, Λ p = 0) (v : H10Ω d Ω) : Λ (H10Ω.pair v) = 0 := by
  have hle : H10ΩGraph d Ω ≤ LinearMap.ker (Λ : WithLp 2 (L2Ω d Ω × L2Ωvec d Ω) →ₛₗ[σ] F) := by
    rw [H10ΩGraph_eq_closure_smoothGraphΩ hΩ]
    exact Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 fun p hp => h p hp)
      (ContinuousLinearMap.isClosed_ker Λ)
  exact hle (H10Ω.pair_mem v)

/-! ### `H¹₀(Ω)` inside `W^{1,2}(Ω)` -/

/-- The isometric inclusion `H¹₀(Ω) ↪ W^{1,2}(Ω)`. -/
def H10ΩtoW12Ω (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    H10Ω d Ω →ₗᵢ[ℂ] W12ΩGraph d Ω where
  toLinearMap := Submodule.inclusion H10ΩGraph_le_W12ΩGraph
  norm_map' _ := rfl

theorem coe_H10ΩtoW12Ω (v : H10Ω d Ω) :
    ((H10ΩtoW12Ω d Ω v : W12ΩGraph d Ω) : WithLp 2 (L2Ω d Ω × L2Ωvec d Ω)) = H10Ω.pair v := rfl

/-- The graphs of the `C_c^∞(Ω)` functions, as elements of `W^{1,2}(Ω)`. -/
def smoothW12Ω (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) : Set (W12ΩGraph d Ω) :=
  Subtype.val ⁻¹' smoothGraphΩ d Ω

/-- **`H¹₀(Ω)` is the closure of `C_c^∞(Ω)` in `W^{1,2}(Ω)`**, the textbook definition: for `Ω`
open, the range of the isometric inclusion `H¹₀(Ω) ↪ W^{1,2}(Ω)` is the closure in `W^{1,2}(Ω)`
of (the span of) the `C_c^∞(Ω)` functions. -/
theorem range_H10ΩtoW12Ω (hΩ : IsOpen Ω) :
    LinearMap.range (H10ΩtoW12Ω d Ω).toLinearMap
      = (Submodule.span ℂ (smoothW12Ω d Ω)).topologicalClosure := by
  have himg : Subtype.val '' ((Submodule.span ℂ (smoothW12Ω d Ω) : Submodule ℂ (W12ΩGraph d Ω)) :
      Set (W12ΩGraph d Ω))
      = (Submodule.span ℂ (smoothGraphΩ d Ω) : Set (WithLp 2 (L2Ω d Ω × L2Ωvec d Ω))) := by
    have hS : (W12ΩGraph d Ω).subtype '' smoothW12Ω d Ω = smoothGraphΩ d Ω := by
      ext q
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hq
        exact ⟨⟨q, smoothGraphΩ_subset_W12ΩGraph hq⟩, hq, rfl⟩
    have h := Submodule.map_span (W12ΩGraph d Ω).subtype (smoothW12Ω d Ω)
    rw [hS] at h
    rw [← h, Submodule.map_coe, Submodule.coe_subtype]
  ext x
  have hL : x ∈ LinearMap.range (H10ΩtoW12Ω d Ω).toLinearMap ↔
      (x : WithLp 2 (L2Ω d Ω × L2Ωvec d Ω)) ∈ H10ΩGraph d Ω := by
    change x ∈ LinearMap.range (Submodule.inclusion H10ΩGraph_le_W12ΩGraph) ↔ _
    rw [Submodule.range_inclusion]
    rfl
  rw [hL, H10ΩGraph_eq_closure_smoothGraphΩ hΩ, ← SetLike.mem_coe, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, mem_preimage, himg]

end LionsC12
