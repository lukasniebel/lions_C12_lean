module

public import LionsC12.Domains.Coordinates

/-!
# Tensor products `P(x₁) Q(x')` and their spatial weak formulation

For `P, P', A, b : ℝ → ℝ` (bounded, measurable) and `Q ∈ C^∞_c(ℝ^n)`, the function
`W(x) = P(x₁) Q(x')` on `ℝ^{n+1}` has the gradient `(P'(x₁) Q(x'), P(x₁) ∇Q(x'))`
(`grad_tens`), and if the one-dimensional identity `∫ b P' conj(ψ') = ∫ A conj(ψ)` holds for every
`ψ ∈ C¹_c(ℝ;ℂ)` (the weak form of `-(b P')' = A`, without boundary conditions), then for every
`φ ∈ C¹_c(ℝ^{n+1};ℂ)` (`tensorΩ_weak`)
`∫ b(x₁) ∇W · conj(∇φ) = ∫ (A(x₁) Q(x') - b(x₁) P(x₁) ΔQ(x')) conj(φ)`,
i.e. `-div(b ∇W) = A ⊗ Q - b P ⊗ ΔQ` weakly.  The `x₁`-part is Fubini in the coordinates
`ℝ × ℝ^n` and the one-dimensional identity on each line; the `x'`-parts are integrations by
parts along the directions `e₂, …, e_{n+1}`, along which `b(x₁) P(x₁)` is constant.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge
open scoped InnerProductSpace ComplexConjugate ContDiff

variable {n : ℕ}

/-! ### Derivatives of `Q` -/

/-- `∂ⱼQ`. -/
def dQ (Q : EuclideanSpace ℝ (Fin n) → ℝ) (j : Fin n) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ Q y (EuclideanSpace.single j 1)

/-- `∂ⱼ∂ⱼQ`. -/
def d2Q (Q : EuclideanSpace ℝ (Fin n) → ℝ) (j : Fin n) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ (dQ Q j) y (EuclideanSpace.single j 1)

/-- `ΔQ = Σⱼ ∂ⱼ∂ⱼQ`. -/
def lapQ (Q : EuclideanSpace ℝ (Fin n) → ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j, d2Q Q j y

/-- A smooth compactly supported function on `ℝ^n`. -/
structure IsBumpFn (Q : EuclideanSpace ℝ (Fin n) → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ Q
  hasCompactSupport : HasCompactSupport Q

namespace IsBumpFn

variable {Q : EuclideanSpace ℝ (Fin n) → ℝ} (hQ : IsBumpFn Q)
include hQ

theorem continuous : Continuous Q := hQ.contDiff.continuous

theorem differentiable : Differentiable ℝ Q := hQ.contDiff.differentiable (by simp)

theorem contDiff_dQ (j : Fin n) : ContDiff ℝ ∞ (dQ Q j) :=
  (hQ.contDiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem continuous_dQ (j : Fin n) : Continuous (dQ Q j) := (hQ.contDiff_dQ j).continuous

theorem differentiable_dQ (j : Fin n) : Differentiable ℝ (dQ Q j) :=
  (hQ.contDiff_dQ j).differentiable (by simp)

theorem continuous_d2Q (j : Fin n) : Continuous (d2Q Q j) :=
  ((hQ.contDiff_dQ j).continuous_fderiv (by simp)).clm_apply continuous_const

theorem continuous_lapQ : Continuous (lapQ Q) :=
  continuous_finsetSum _ fun j _ => hQ.continuous_d2Q j

theorem hasCompactSupport_dQ (j : Fin n) : HasCompactSupport (dQ Q j) :=
  (hQ.hasCompactSupport.fderiv ℝ).mono fun y hy h0 => hy (by simp [dQ, h0])

theorem hasCompactSupport_d2Q (j : Fin n) : HasCompactSupport (d2Q Q j) :=
  ((hQ.hasCompactSupport_dQ j).fderiv ℝ).mono fun y hy h0 => hy (by simp [d2Q, h0])

theorem hasCompactSupport_lapQ : HasCompactSupport (lapQ Q) := by
  refine HasCompactSupport.intro' (K := ⋃ j, tsupport (d2Q Q j))
    (isCompact_iUnion fun j => hQ.hasCompactSupport_d2Q j)
    (isClosed_iUnion_of_finite fun j => isClosed_tsupport _) fun y hy => ?_
  refine Finset.sum_eq_zero fun j _ => ?_
  exact image_eq_zero_of_notMem_tsupport fun h => hy (mem_iUnion.2 ⟨j, h⟩)

theorem bdd : ∃ C, ∀ y, |Q y| ≤ C :=
  hQ.continuous.bounded_above_of_compact_support hQ.hasCompactSupport

theorem bdd_dQ (j : Fin n) : ∃ C, ∀ y, |dQ Q j y| ≤ C :=
  (hQ.continuous_dQ j).bounded_above_of_compact_support (hQ.hasCompactSupport_dQ j)

theorem bdd_d2Q (j : Fin n) : ∃ C, ∀ y, |d2Q Q j y| ≤ C :=
  (hQ.continuous_d2Q j).bounded_above_of_compact_support (hQ.hasCompactSupport_d2Q j)

theorem bdd_lapQ : ∃ C, ∀ y, |lapQ Q y| ≤ C :=
  hQ.continuous_lapQ.bounded_above_of_compact_support hQ.hasCompactSupport_lapQ

end IsBumpFn

/-! ### The tensor product and its gradient -/

/-- The tensor product `P(x₁) Q(x')` on `ℝ^{n+1}`. -/
def tens (P : ℝ → ℝ) (Q : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ℝ :=
  P (x 0) * Q (tailL n x)

/-- The gradient `(P'(x₁) Q(x'), P(x₁) ∇Q(x'))` of the tensor product, as a complex vector. -/
def gradTens (P Px : ℝ → ℝ) (Q : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.cons ((Px (x 0) * Q (tailL n x) : ℝ) : ℂ)
    (fun j => ((P (x 0) * dQ Q j (tailL n x) : ℝ) : ℂ)) : Fin (n + 1) → ℂ)

@[simp] theorem gradTens_zero (P Px : ℝ → ℝ) (Q : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    gradTens P Px Q x 0 = ((Px (x 0) * Q (tailL n x) : ℝ) : ℂ) := rfl

@[simp] theorem gradTens_succ (P Px : ℝ → ℝ) (Q : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (j : Fin n) :
    gradTens P Px Q x j.succ = ((P (x 0) * dQ Q j (tailL n x) : ℝ) : ℂ) := rfl

theorem measurable_head : Measurable (fun x : EuclideanSpace ℝ (Fin (n + 1)) => x 0) :=
  (EuclideanSpace.proj (0 : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).continuous.measurable

theorem continuous_head : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) => x 0) :=
  (EuclideanSpace.proj (0 : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).continuous

theorem hasFDerivAt_tens {P Px : ℝ → ℝ} (hP : ∀ s, HasDerivAt P (Px s) s)
    {Q : EuclideanSpace ℝ (Fin n) → ℝ} (hQ : Differentiable ℝ Q)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    HasFDerivAt (tens P Q) (P (x 0) • (fderiv ℝ Q (tailL n x)).comp (tailL n)
      + Q (tailL n x) • (Px (x 0) • (EuclideanSpace.proj 0 :
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))) x := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin (n + 1)) => P (y 0))
      (Px (x 0) • (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)) x :=
    (hP (x 0)).comp_hasFDerivAt x
      (EuclideanSpace.proj (0 : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun y => Q (tailL n y)) ((fderiv ℝ Q (tailL n x)).comp (tailL n)) x :=
    (hQ (tailL n x)).hasFDerivAt.comp x (tailL n).hasFDerivAt
  exact h1.mul h2

theorem fderiv_tens_apply {P Px : ℝ → ℝ} (hP : ∀ s, HasDerivAt P (Px s) s)
    {Q : EuclideanSpace ℝ (Fin n) → ℝ} (hQ : Differentiable ℝ Q)
    (x v : EuclideanSpace ℝ (Fin (n + 1))) :
    fderiv ℝ (tens P Q) x v = P (x 0) * fderiv ℝ Q (tailL n x) (tailL n v)
      + Q (tailL n x) * (Px (x 0) * v 0) := by
  rw [(hasFDerivAt_tens hP hQ x).fderiv]
  rfl

theorem differentiable_tens {P Px : ℝ → ℝ} (hP : ∀ s, HasDerivAt P (Px s) s)
    {Q : EuclideanSpace ℝ (Fin n) → ℝ} (hQ : Differentiable ℝ Q) : Differentiable ℝ (tens P Q) :=
  fun x => (hasFDerivAt_tens hP hQ x).differentiableAt

/-- The gradient of the (complexified) tensor product. -/
theorem grad_tens {P Px : ℝ → ℝ} (hP : ∀ s, HasDerivAt P (Px s) s)
    {Q : EuclideanSpace ℝ (Fin n) → ℝ} (hQ : Differentiable ℝ Q)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    grad (fun y => (tens P Q y : ℂ)) x = gradTens P Px Q x := by
  ext i
  simp only [grad, PiLp.toLp_apply]
  rw [IsTestFunΩ.fderiv_ofReal (differentiable_tens hP hQ), fderiv_tens_apply hP hQ]
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [tailL_single_zero, single_zero_apply_zero, map_zero, gradTens_zero]
    push_cast; ring
  · rw [tailL_single_succ, single_succ_apply_zero, gradTens_succ]
    simp [dQ]

theorem contDiff_tens {P : ℝ → ℝ} (hP : ContDiff ℝ 1 P) {Q : EuclideanSpace ℝ (Fin n) → ℝ}
    (hQ : ContDiff ℝ 1 Q) : ContDiff ℝ 1 (tens P Q) :=
  (hP.comp (EuclideanSpace.proj (0 : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).contDiff).mul (hQ.comp (tailL n).contDiff)

/-- The inner product with the gradient of the tensor product, coordinatewise. -/
theorem inner_grad_gradTens (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℂ) (P Px : ℝ → ℝ)
    (Q : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ⟪grad φ x, gradTens P Px Q x⟫_ℂ
      = ((Px (x 0) * Q (tailL n x) : ℝ) : ℂ) * conj (fderiv ℝ φ x (EuclideanSpace.single 0 1))
        + ∑ j : Fin n, ((P (x 0) * dQ Q j (tailL n x) : ℝ) : ℂ)
            * conj (fderiv ℝ φ x (EuclideanSpace.single j.succ 1)) := by
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [RCLike.inner_apply, grad, PiLp.toLp_apply, gradTens_zero, gradTens_succ]

/-! ### Integrability -/

theorem integrable_bdd_mul_cpt {f g : EuclideanSpace ℝ (Fin (n + 1)) → ℂ}
    (hf : AEStronglyMeasurable f) (hb : ∃ C, ∀ x, ‖f x‖ ≤ C) (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun x => f x * g x) := by
  obtain ⟨C, hC⟩ := hb
  exact (hg.integrable_of_hasCompactSupport hgc).bdd_mul hf (Eventually.of_forall hC)

theorem hasCompactSupport_conj_fderiv {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℂ}
    (hφc : HasCompactSupport φ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    HasCompactSupport (fun x => conj (fderiv ℝ φ x v)) :=
  (hφc.fderiv ℝ).mono fun x hx h0 => hx (by simp [h0])

theorem continuous_conj_fderiv {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℂ} (hφ : ContDiff ℝ 1 φ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) : Continuous (fun x => conj (fderiv ℝ φ x v)) :=
  Complex.continuous_conj.comp ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)

/-- Measurability and boundedness of `(f(x₁) g(x') : ℂ)`. -/
theorem aestronglyMeasurable_head_tail {f : ℝ → ℝ} (hf : Measurable f)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) :
    AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin (n + 1)) => ((f (x 0) * g (tailL n x) : ℝ) : ℂ)) :=
  (Complex.measurable_ofReal.comp ((hf.comp measurable_head).mul
    (hg.comp (tailL n).continuous).measurable)).aestronglyMeasurable

theorem bdd_head_tail {f : ℝ → ℝ} (hf : ∃ C, ∀ s, |f s| ≤ C)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ∃ C, ∀ y, |g y| ≤ C) :
    ∃ C, ∀ x : EuclideanSpace ℝ (Fin (n + 1)), ‖((f (x 0) * g (tailL n x) : ℝ) : ℂ)‖ ≤ C := by
  obtain ⟨C₁, h₁⟩ := hf
  obtain ⟨C₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, fun x => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (h₁ _) (h₂ _) (abs_nonneg _) ((abs_nonneg _).trans (h₁ 0))

theorem bdd_mul {f g : ℝ → ℝ} (hf : ∃ C, ∀ s, |f s| ≤ C) (hg : ∃ C, ∀ s, |g s| ≤ C) :
    ∃ C, ∀ s, |f s * g s| ≤ C := by
  obtain ⟨C₁, h₁⟩ := hf
  obtain ⟨C₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, fun s => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (h₁ _) (h₂ _) (abs_nonneg _) ((abs_nonneg _).trans (h₁ 0))

/-! ### The `x₁`-direction: Fubini and the one-dimensional identity -/

/-- A test function restricted to the line `s ↦ (s, y)`. -/
theorem line_test {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (y : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 1 (fun s => φ (insE n (s, y))) ∧ HasCompactSupport (fun s => φ (insE n (s, y))) ∧
      ∀ s, HasDerivAt (fun s => φ (insE n (s, y)))
        (fderiv ℝ φ (insE n (s, y)) (EuclideanSpace.single 0 1)) s := by
  refine ⟨hφ.comp ((insE n).contDiff.comp (contDiff_id.prodMk contDiff_const)), ?_, fun s => ?_⟩
  · obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
    refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun s hs => ?_
    refine image_eq_zero_of_notMem_tsupport fun h => hs ?_
    have h1 := hR h
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 := abs_head_le_norm (insE n (s, y))
    rw [insE_apply_zero] at h2
    exact abs_le.1 (h2.trans h1)
  · have hc : HasDerivAt (fun s : ℝ => insE n (0, y) + s • EuclideanSpace.single 0 1)
        (EuclideanSpace.single 0 1) s := by
      simpa using ((hasDerivAt_id s).smul_const
        (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))).const_add (insE n (0, y))
    have hfun : (fun s => φ (insE n (s, y)))
        = φ ∘ fun s : ℝ => insE n (0, y) + s • EuclideanSpace.single 0 1 := by
      funext s; simp only [Function.comp_apply]; rw [insE_eq]
    rw [hfun]
    have := (hφ.differentiable one_ne_zero
      (insE n (0, y) + s • EuclideanSpace.single 0 1)).hasFDerivAt.comp_hasDerivAt s hc
    rwa [← insE_eq] at this

/-- **The `x₁`-part.**  Fubini and the one-dimensional identity on each line `{x' = y}`. -/
theorem tensorΩ_weak_head {Px A b : ℝ → ℝ} (hPxm : Measurable Px) (hAm : Measurable A)
    (hbm : Measurable b) (hPxb : ∃ C, ∀ s, |Px s| ≤ C) (hAb : ∃ C, ∀ s, |A s| ≤ C)
    (hbb : ∃ C, ∀ s, |b s| ≤ C) {Q : EuclideanSpace ℝ (Fin n) → ℝ} (hQ : IsBumpFn Q)
    (h1 : ∀ ψ : ℝ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      ∫ s, ((b s * Px s : ℝ) : ℂ) * conj (deriv ψ s) = ∫ s, (A s : ℂ) * conj (ψ s))
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℂ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∫ x, ((b (x 0) * Px (x 0) * Q (tailL n x) : ℝ) : ℂ)
        * conj (fderiv ℝ φ x (EuclideanSpace.single 0 1))
      = ∫ x, ((A (x 0) * Q (tailL n x) : ℝ) : ℂ) * conj (φ x) := by
  set f1 : EuclideanSpace ℝ (Fin (n + 1)) → ℂ :=
    fun x => ((b (x 0) * Px (x 0) * Q (tailL n x) : ℝ) : ℂ)
      * conj (fderiv ℝ φ x (EuclideanSpace.single 0 1)) with hf1
  set f2 : EuclideanSpace ℝ (Fin (n + 1)) → ℂ :=
    fun x => ((A (x 0) * Q (tailL n x) : ℝ) : ℂ) * conj (φ x) with hf2
  have hi1 : Integrable f1 := by
    refine integrable_bdd_mul_cpt (f := fun x => ((b (x 0) * Px (x 0) * Q (tailL n x) : ℝ) : ℂ))
      (aestronglyMeasurable_head_tail (hbm.mul hPxm) hQ.continuous)
      (bdd_head_tail (bdd_mul hbb hPxb) hQ.bdd) (continuous_conj_fderiv hφ _)
      (hasCompactSupport_conj_fderiv hφc _)
  have hi2 : Integrable f2 := by
    refine integrable_bdd_mul_cpt (f := fun x => ((A (x 0) * Q (tailL n x) : ℝ) : ℂ))
      (aestronglyMeasurable_head_tail hAm hQ.continuous) (bdd_head_tail hAb hQ.bdd)
      (Complex.continuous_conj.comp hφ.continuous) (hφc.comp_left (map_zero _))
  have hi1' : Integrable (f1 ∘ insE n) (volume.prod volume) := integrable_comp_insE_iff.2 hi1
  have hi2' : Integrable (f2 ∘ insE n) (volume.prod volume) := integrable_comp_insE_iff.2 hi2
  rw [← integral_comp_insE f1, ← integral_comp_insE f2]
  change ∫ p, (f1 ∘ insE n) p ∂(volume.prod volume) = ∫ p, (f2 ∘ insE n) p ∂(volume.prod volume)
  rw [integral_prod_symm _ hi1', integral_prod_symm _ hi2']
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  obtain ⟨hψ1, hψc, hψd⟩ := line_test hφ hφc y
  have hderiv : deriv (fun s => φ (insE n (s, y)))
      = fun s => fderiv ℝ φ (insE n (s, y)) (EuclideanSpace.single 0 1) :=
    funext fun s => (hψd s).deriv
  have key := h1 _ hψ1 hψc
  rw [hderiv] at key
  simp only [Function.comp_apply, hf1, hf2, insE_apply_zero, tailL_insE]
  calc ∫ s, ((b s * Px s * Q y : ℝ) : ℂ)
          * conj (fderiv ℝ φ (insE n (s, y)) (EuclideanSpace.single 0 1))
      = (Q y : ℂ) * ∫ s, ((b s * Px s : ℝ) : ℂ)
          * conj (fderiv ℝ φ (insE n (s, y)) (EuclideanSpace.single 0 1)) := by
        rw [← integral_const_mul]
        congr 1; funext s; push_cast; ring
    _ = (Q y : ℂ) * ∫ s, (A s : ℂ) * conj (φ (insE n (s, y))) := by rw [key]
    _ = ∫ s, ((A s * Q y : ℝ) : ℂ) * conj (φ (insE n (s, y))) := by
        rw [← integral_const_mul]
        congr 1; funext s; push_cast; ring

/-! ### The `x'`-directions: integration by parts along `e_{j+1}` -/

theorem tensorΩ_weak_tail {P b : ℝ → ℝ} (hPm : Measurable P) (hbm : Measurable b)
    (hPb : ∃ C, ∀ s, |P s| ≤ C) (hbb : ∃ C, ∀ s, |b s| ≤ C)
    {Q : EuclideanSpace ℝ (Fin n) → ℝ} (hQ : IsBumpFn Q) (j : Fin n)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℂ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∫ x, ((b (x 0) * P (x 0) * dQ Q j (tailL n x) : ℝ) : ℂ)
        * conj (fderiv ℝ φ x (EuclideanSpace.single j.succ 1))
      = -∫ x, ((b (x 0) * P (x 0) * d2Q Q j (tailL n x) : ℝ) : ℂ) * conj (φ x) := by
  set v : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single j.succ 1 with hv
  set f : EuclideanSpace ℝ (Fin (n + 1)) → ℂ :=
    fun x => ((b (x 0) * P (x 0) * dQ Q j (tailL n x) : ℝ) : ℂ) with hf
  set f' : EuclideanSpace ℝ (Fin (n + 1)) → ℂ :=
    fun x => ((b (x 0) * P (x 0) * d2Q Q j (tailL n x) : ℝ) : ℂ) with hf'
  set g : EuclideanSpace ℝ (Fin (n + 1)) → ℂ := fun x => conj (φ x) with hg
  set g' : EuclideanSpace ℝ (Fin (n + 1)) → ℂ := fun x => conj (fderiv ℝ φ x v) with hg'
  have hbP : ∃ C, ∀ s, |b s * P s| ≤ C := bdd_mul hbb hPb
  have hf'g : Integrable (fun x => f' x * g x) :=
    integrable_bdd_mul_cpt (aestronglyMeasurable_head_tail (hbm.mul hPm) (hQ.continuous_d2Q j))
      (bdd_head_tail hbP (hQ.bdd_d2Q j)) (Complex.continuous_conj.comp hφ.continuous)
      (hφc.comp_left (map_zero _))
  have hfg' : Integrable (fun x => f x * g' x) :=
    integrable_bdd_mul_cpt (aestronglyMeasurable_head_tail (hbm.mul hPm) (hQ.continuous_dQ j))
      (bdd_head_tail hbP (hQ.bdd_dQ j)) (continuous_conj_fderiv hφ _)
      (hasCompactSupport_conj_fderiv hφc _)
  have hfg : Integrable (fun x => f x * g x) :=
    integrable_bdd_mul_cpt (aestronglyMeasurable_head_tail (hbm.mul hPm) (hQ.continuous_dQ j))
      (bdd_head_tail hbP (hQ.bdd_dQ j)) (Complex.continuous_conj.comp hφ.continuous)
      (hφc.comp_left (map_zero _))
  have hfd : ∀ x, HasLineDerivAt ℝ f (f' x) x v := by
    intro x
    have hline : (fun t : ℝ => f (x + t • v))
        = fun t => ((b (x 0) * P (x 0) : ℝ) : ℂ)
          * (dQ Q j (tailL n x + t • EuclideanSpace.single j 1) : ℂ) := by
      funext t
      simp only [hf, map_add, map_smul, hv, tailL_single_succ]
      have h0 : (x + t • EuclideanSpace.single j.succ (1 : ℝ)) 0 = x 0 := by
        simp
      rw [h0]
      push_cast; ring
    have hc : HasDerivAt (fun t : ℝ => tailL n x + t • EuclideanSpace.single j 1)
        (EuclideanSpace.single j 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
        (EuclideanSpace.single j (1 : ℝ))).const_add (tailL n x)
    have hd := ((hQ.differentiable_dQ j) (tailL n x + (0 : ℝ) • EuclideanSpace.single j 1)
      ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
    simp only [zero_smul, add_zero] at hd
    have hd' := (hd.ofReal_comp).const_mul ((b (x 0) * P (x 0) : ℝ) : ℂ)
    show HasDerivAt (fun t : ℝ => f (x + t • v)) (f' x) 0
    rw [hline]
    have e1 : f' x = ((b (x 0) * P (x 0) : ℝ) : ℂ)
        * ((fderiv ℝ (dQ Q j) (tailL n x) (EuclideanSpace.single j 1) : ℝ) : ℂ) := by
      simp only [hf', d2Q]; push_cast; ring
    rw [e1]
    exact hd'
  have hgd : ∀ x, HasLineDerivAt ℝ g (g' x) x v := by
    intro x
    have h := ((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt
      (x := φ x)).comp x ((hφ.differentiable one_ne_zero x).hasFDerivAt)
    exact h.hasLineDerivAt v
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.mul ℝ ℂ) hf'g hfg' hfg (fun x _ => hfd x)
    (fun x _ => hgd x)
  simpa [hf, hf', hg, hg'] using key

/-- **The spatial weak formulation of `-div(b ∇(P ⊗ Q)) = A ⊗ Q - b P ⊗ ΔQ`.** -/
theorem tensorΩ_weak {P Px A b : ℝ → ℝ} (hPm : Measurable P) (hPxm : Measurable Px)
    (hAm : Measurable A) (hbm : Measurable b) (hPb : ∃ C, ∀ s, |P s| ≤ C)
    (hPxb : ∃ C, ∀ s, |Px s| ≤ C) (hAb : ∃ C, ∀ s, |A s| ≤ C) (hbb : ∃ C, ∀ s, |b s| ≤ C)
    {Q : EuclideanSpace ℝ (Fin n) → ℝ} (hQ : IsBumpFn Q)
    (h1 : ∀ ψ : ℝ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      ∫ s, ((b s * Px s : ℝ) : ℂ) * conj (deriv ψ s) = ∫ s, (A s : ℂ) * conj (ψ s))
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℂ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∫ x, (b (x 0) : ℂ) * ⟪grad φ x, gradTens P Px Q x⟫_ℂ
      = ∫ x, conj (φ x) * ((A (x 0) * Q (tailL n x)
          - b (x 0) * P (x 0) * lapQ Q (tailL n x) : ℝ) : ℂ) := by
  have hbP : ∃ C, ∀ s, |b s * P s| ≤ C := bdd_mul hbb hPb
  have hint0 : Integrable (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
      ((b (x 0) * Px (x 0) * Q (tailL n x) : ℝ) : ℂ)
        * conj (fderiv ℝ φ x (EuclideanSpace.single 0 1))) :=
    integrable_bdd_mul_cpt (aestronglyMeasurable_head_tail (hbm.mul hPxm) hQ.continuous)
      (bdd_head_tail (bdd_mul hbb hPxb) hQ.bdd) (continuous_conj_fderiv hφ _)
      (hasCompactSupport_conj_fderiv hφc _)
  have hintj : ∀ j : Fin n, Integrable (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
      ((b (x 0) * P (x 0) * dQ Q j (tailL n x) : ℝ) : ℂ)
        * conj (fderiv ℝ φ x (EuclideanSpace.single j.succ 1))) := fun j =>
    integrable_bdd_mul_cpt (aestronglyMeasurable_head_tail (hbm.mul hPm) (hQ.continuous_dQ j))
      (bdd_head_tail hbP (hQ.bdd_dQ j)) (continuous_conj_fderiv hφ _)
      (hasCompactSupport_conj_fderiv hφc _)
  have hintA : Integrable (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
      ((A (x 0) * Q (tailL n x) : ℝ) : ℂ) * conj (φ x)) :=
    integrable_bdd_mul_cpt (aestronglyMeasurable_head_tail hAm hQ.continuous)
      (bdd_head_tail hAb hQ.bdd) (Complex.continuous_conj.comp hφ.continuous)
      (hφc.comp_left (map_zero _))
  have hint2 : ∀ j : Fin n, Integrable (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
      ((b (x 0) * P (x 0) * d2Q Q j (tailL n x) : ℝ) : ℂ) * conj (φ x)) := fun j =>
    integrable_bdd_mul_cpt (aestronglyMeasurable_head_tail (hbm.mul hPm) (hQ.continuous_d2Q j))
      (bdd_head_tail hbP (hQ.bdd_d2Q j)) (Complex.continuous_conj.comp hφ.continuous)
      (hφc.comp_left (map_zero _))
  have eL : (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
        (b (x 0) : ℂ) * ⟪grad φ x, gradTens P Px Q x⟫_ℂ)
      = fun x => ((b (x 0) * Px (x 0) * Q (tailL n x) : ℝ) : ℂ)
          * conj (fderiv ℝ φ x (EuclideanSpace.single 0 1))
        + ∑ j : Fin n, ((b (x 0) * P (x 0) * dQ Q j (tailL n x) : ℝ) : ℂ)
          * conj (fderiv ℝ φ x (EuclideanSpace.single j.succ 1)) := by
    funext x
    rw [inner_grad_gradTens, mul_add, Finset.mul_sum]
    congr 1
    · push_cast; ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      push_cast; ring
  have eR : (fun x : EuclideanSpace ℝ (Fin (n + 1)) => conj (φ x) * ((A (x 0) * Q (tailL n x)
          - b (x 0) * P (x 0) * lapQ Q (tailL n x) : ℝ) : ℂ))
      = fun x => ((A (x 0) * Q (tailL n x) : ℝ) : ℂ) * conj (φ x)
        - ∑ j : Fin n, ((b (x 0) * P (x 0) * d2Q Q j (tailL n x) : ℝ) : ℂ) * conj (φ x) := by
    funext x
    simp only [lapQ, Finset.mul_sum]
    push_cast
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  rw [eL, eR, integral_add hint0 (integrable_finsetSum _ fun j _ => hintj j),
    integral_sub hintA (integrable_finsetSum _ fun j _ => hint2 j),
    integral_finsetSum _ fun j _ => hintj j, integral_finsetSum _ fun j _ => hint2 j,
    tensorΩ_weak_head hPxm hAm hbm hPxb hAb hbb hQ h1 hφ hφc]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact tensorΩ_weak_tail hPm hbm hPb hbb hQ j hφ hφc

end LionsC12
