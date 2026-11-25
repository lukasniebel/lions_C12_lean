module

public import LionsC12.Lions.Projection
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Gelfand triples and Lions' existence theorem

This file sets up the abstract parabolic framework `V ↪ H ↪ V'` and proves J.-L. Lions'
existence theorem for the variational (weak) formulation of the Cauchy problem
`u' + 𝒜(t) u = f`, `u(0) = u₀`, using `LionsC12.lions_projection`.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory
open scoped InnerProductSpace ENNReal

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A Gelfand triple `V ↪ H ↪ V'`: a continuous injective linear embedding `j : V → H`
with dense range. -/
structure GelfandTriple (V H : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  /-- The continuous linear embedding `j : V → H`. -/
  j : V →L[ℝ] H
  injective : Function.Injective j
  denseRange : DenseRange j

/-- The embedding `H → V'`, `h ↦ (v ↦ ⟪h, j v⟫)`. -/
def GelfandTriple.flat (G : GelfandTriple V H) : H →L[ℝ] StrongDual ℝ V :=
  LinearMap.mkContinuous
    { toFun := fun h => (innerSL ℝ h).comp G.j
      map_add' := by
        intro x y; ext v; simp
      map_smul' := by
        intro c x; ext v; simp }
    ‖G.j‖ (by
      intro h
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      rw [innerSL_apply_norm, mul_comm])

@[simp]
theorem GelfandTriple.flat_apply (G : GelfandTriple V H) (h : H) (v : V) :
    G.flat h v = ⟪h, G.j v⟫_ℝ := rfl

theorem GelfandTriple.flat_injective (G : GelfandTriple V H) : Function.Injective G.flat := by
  intro h₁ h₂ hh
  have key : ∀ v : V, ⟪h₁ - h₂, G.j v⟫_ℝ = 0 := by
    intro v
    have h1 : G.flat h₁ v = G.flat h₂ v := by rw [hh]
    rw [inner_sub_left]
    simpa using sub_eq_zero.mpr h1
  have hz : (fun y : H => ⟪h₁ - h₂, y⟫_ℝ) = fun _ => 0 := by
    refine Continuous.ext_on G.denseRange ?_ continuous_const ?_
    · exact (innerSL ℝ (h₁ - h₂)).continuous
    · rintro _ ⟨v, rfl⟩
      exact key v
  have h0 : ⟪h₁ - h₂, h₁ - h₂⟫_ℝ = 0 := congrFun hz _
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)

/-- The measure of the time interval `(0, T]`. -/
def μT (T : ℝ) : Measure ℝ := volume.restrict (Set.Ioc 0 T)

instance instIsFiniteMeasureμT (T : ℝ) : IsFiniteMeasure (μT T) :=
  ⟨by simp only [μT, Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩

/-- Test functions: `C¹` functions `ℝ → V` vanishing on `[T, ∞)`. -/
def IsTestV (T : ℝ) (φ : ℝ → V) : Prop := ContDiff ℝ 1 φ ∧ ∀ t, T ≤ t → φ t = 0

/-- A measurable family of uniformly bounded, coercive forms on `V`, `t ∈ (0,T]`. -/
structure IsFormFamily (T : ℝ) (A : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (M α : ℝ) : Prop where
  meas : AEStronglyMeasurable A (μT T)
  bound : ∀ t, ‖A t‖ ≤ M
  coercive : ∀ t v, α * ‖v‖ ^ 2 ≤ A t v v
  α_pos : 0 < α

/-- Lions' variational solution. -/
def IsVariationalSolution (G : GelfandTriple V H) (T : ℝ) (A : ℝ → V →L[ℝ] V →L[ℝ] ℝ)
    (f : ℝ → StrongDual ℝ V) (u₀ : H) (u : ℝ → V) : Prop :=
  MemLp u 2 (μT T) ∧ ∀ φ : ℝ → V, IsTestV T φ →
    ∫ t in (0 : ℝ)..T, (-(⟪G.j (u t), G.j (deriv φ t)⟫_ℝ) + A t (u t) (φ t))
      = (∫ t in (0 : ℝ)..T, f t (φ t)) + ⟪u₀, G.j (φ 0)⟫_ℝ


/-! ### Auxiliary material for the existence proof -/

section Aux

/-- Riesz representative of a continuous linear functional on `V`. -/
def rieszV (L : StrongDual ℝ V) : V := (InnerProductSpace.toDual ℝ V).symm L

@[simp] theorem inner_rieszV (L : StrongDual ℝ V) (v : V) : ⟪rieszV L, v⟫_ℝ = L v :=
  InnerProductSpace.toDual_symm_apply

@[simp] theorem norm_rieszV (L : StrongDual ℝ V) : ‖rieszV L‖ = ‖L‖ :=
  (InnerProductSpace.toDual ℝ V).symm.norm_map L

theorem continuous_rieszV : Continuous (rieszV : StrongDual ℝ V → V) :=
  (InnerProductSpace.toDual ℝ V).symm.continuous

theorem rieszV_add (L L' : StrongDual ℝ V) : rieszV (L + L') = rieszV L + rieszV L' := by
  refine ext_inner_right ℝ fun v => ?_
  simp [inner_add_left]

theorem rieszV_smul (c : ℝ) (L : StrongDual ℝ V) : rieszV (c • L) = c • rieszV L := by
  refine ext_inner_right ℝ fun v => ?_
  simp [real_inner_smul_left]

theorem rieszV_neg (L : StrongDual ℝ V) : rieszV (-L) = -rieszV L := by
  refine ext_inner_right ℝ fun v => ?_
  simp [inner_neg_left]

/-- Every continuous function is in every `Lᵖ((0,T])`. -/
theorem memLp_of_continuous {E : Type*} [NormedAddCommGroup E] {T : ℝ} {g : ℝ → E}
    (hg : Continuous g) (p : ℝ≥0∞) : MemLp g p (μT T) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hC x (Set.Ioc_subset_Icc_self hx))

/-- `MemLp.add` with the codomain given explicitly (elaboration of the generic `ε`-version is
very slow for `StrongDual`-valued functions). -/
theorem memLp_add' {E : Type*} [NormedAddCommGroup E] {μ : Measure ℝ} {p : ℝ≥0∞} {f g : ℝ → E}
    (hf : MemLp f p μ) (hg : MemLp g p μ) : MemLp (fun t => f t + g t) p μ :=
  MemLp.add (ε := E) hf hg

theorem memLp_rieszV {T : ℝ} {b : ℝ → StrongDual ℝ V} (hb : MemLp b 2 (μT T)) :
    MemLp (fun t => rieszV (b t)) 2 (μT T) :=
  hb.of_le (continuous_rieszV.comp_aestronglyMeasurable hb.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => le_of_eq (norm_rieszV _))

/-- The `L²`-pairing of a `V'`-valued `L²` function with an element of `L²(0,T;V)`. -/
theorem inner_toLp_rieszV {T : ℝ} {b : ℝ → StrongDual ℝ V} (hb : MemLp b 2 (μT T))
    (u : Lp V 2 (μT T)) :
    ⟪(memLp_rieszV hb).toLp (fun t => rieszV (b t)), u⟫_ℝ = ∫ t, b t (u t) ∂(μT T) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_rieszV hb).coeFn_toLp] with t ht
  rw [ht, inner_rieszV]

theorem norm_toLp_rieszV {T : ℝ} {b : ℝ → StrongDual ℝ V} (hb : MemLp b 2 (μT T)) :
    ‖(memLp_rieszV hb).toLp (fun t => rieszV (b t))‖ = (eLpNorm b 2 (μT T)).toReal := by
  rw [Lp.norm_toLp]
  congr 1
  exact eLpNorm_congr_norm_ae (continuous_rieszV.comp_aestronglyMeasurable hb.aestronglyMeasurable)
    hb.aestronglyMeasurable (Filter.Eventually.of_forall fun _ => norm_rieszV _)

end Aux


section Test

variable {T : ℝ}

omit [CompleteSpace V] in
theorem IsTestV.continuous {φ : ℝ → V} (hφ : IsTestV T φ) : Continuous φ := hφ.1.continuous

omit [CompleteSpace V] in
theorem IsTestV.continuous_deriv {φ : ℝ → V} (hφ : IsTestV T φ) : Continuous (deriv φ) :=
  hφ.1.continuous_deriv_one

omit [CompleteSpace V] in
theorem IsTestV.differentiable {φ : ℝ → V} (hφ : IsTestV T φ) : Differentiable ℝ φ :=
  hφ.1.differentiable one_ne_zero

omit [CompleteSpace V] in
theorem IsTestV.memLp {φ : ℝ → V} (hφ : IsTestV T φ) (p : ℝ≥0∞) : MemLp φ p (μT T) :=
  memLp_of_continuous hφ.continuous p

/-- Test functions form a submodule of `ℝ → V`. -/
def testSubmodule (T : ℝ) : Submodule ℝ (ℝ → V) where
  carrier := {φ | IsTestV T φ}
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun t ht => by
    simp only [Pi.add_apply, ha.2 t ht, hb.2 t ht, add_zero]⟩
  zero_mem' := ⟨contDiff_const, fun _ _ => rfl⟩
  smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun t ht => by
    simp only [Pi.smul_apply, ha.2 t ht, smul_zero]⟩

omit [CompleteSpace V] in
theorem mem_testSubmodule {φ : ℝ → V} : φ ∈ testSubmodule T ↔ IsTestV T φ := Iff.rfl

/-- The `V'`-valued density defining the form `E φ`. -/
def bfun (G : GelfandTriple V H) (A : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (φ : ℝ → V) (t : ℝ) :
    StrongDual ℝ V :=
  -(G.flat (G.j (deriv φ t))) + (A t).flip (φ t)

theorem bfun_apply (G : GelfandTriple V H) (A : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (φ : ℝ → V) (t : ℝ)
    (v : V) : bfun G A φ t v = -(⟪G.j v, G.j (deriv φ t)⟫_ℝ) + A t v (φ t) := by
  simp only [bfun, add_apply, neg_apply,
    GelfandTriple.flat_apply, ContinuousLinearMap.flip_apply]
  rw [real_inner_comm]

theorem bfun_add (G : GelfandTriple V H) (A : ℝ → V →L[ℝ] V →L[ℝ] ℝ) {φ ψ : ℝ → V}
    (hφ : IsTestV T φ) (hψ : IsTestV T ψ) :
    bfun G A (φ + ψ) = bfun G A φ + bfun G A ψ := by
  funext t
  have hd : deriv (φ + ψ) t = deriv φ t + deriv ψ t :=
    deriv_add (hφ.differentiable t) (hψ.differentiable t)
  simp only [bfun, hd, Pi.add_apply, map_add]
  abel

theorem bfun_smul (G : GelfandTriple V H) (A : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (c : ℝ) {φ : ℝ → V}
    (hφ : IsTestV T φ) : bfun G A (c • φ) = c • bfun G A φ := by
  funext t
  have hd : deriv (c • φ) t = c • deriv φ t := by
    simpa using deriv_const_smul c (hφ.differentiable t)
  simp only [bfun, hd, Pi.smul_apply, map_smul]
  simp [smul_add, smul_neg]

end Test


section Existence

variable {T : ℝ}

/-- `AEStronglyMeasurable` version of applying a measurable family of operators. -/
theorem aestronglyMeasurable_clm_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure ℝ} {B : ℝ → E →L[ℝ] F} {g : ℝ → E}
    (hB : AEStronglyMeasurable B μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun t => B t (g t)) μ :=
  (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := F)).continuous.comp_aestronglyMeasurable
    (hB.prodMk hg)

theorem memLp_of_bound' {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hm : AEStronglyMeasurable g (μT T)) (C : ℝ) (hC : ∀ t ∈ Set.Ioc (0 : ℝ) T, ‖g t‖ ≤ C)
    (p : ℝ≥0∞) : MemLp g p (μT T) :=
  MemLp.of_bound hm C (ae_restrict_of_forall_mem measurableSet_Ioc hC)

omit [CompleteSpace V] in
/-- Uniform bound of a test function on the time interval. -/
theorem IsTestV.exists_bound {φ : ℝ → V} (hφ : IsTestV T φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc (0 : ℝ) T, ‖φ t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hφ.continuous.continuousOn
  refine ⟨|C|, abs_nonneg _, fun t ht => (hC t (Set.Ioc_subset_Icc_self ht)).trans (le_abs_self C)⟩

omit [CompleteSpace V] in
theorem memLp_Aflip (A : ℝ → V →L[ℝ] V →L[ℝ] ℝ) {M α : ℝ} (hA : IsFormFamily T A M α)
    {φ : ℝ → V} (hφ : IsTestV T φ) : MemLp (fun t => (A t).flip (φ t)) 2 (μT T) := by
  have hflip : AEStronglyMeasurable (fun t => (A t).flip) (μT T) :=
    (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).continuous.comp_aestronglyMeasurable hA.meas
  have h2m : AEStronglyMeasurable (fun t => (A t).flip (φ t)) (μT T) :=
    aestronglyMeasurable_clm_apply hflip hφ.continuous.aestronglyMeasurable
  obtain ⟨C, hC0, hC⟩ := hφ.exists_bound
  have hM : 0 ≤ M := (norm_nonneg (A 0)).trans (hA.bound 0)
  refine memLp_of_bound' h2m (M * C) (fun x hx => ?_) 2
  calc ‖(A x).flip (φ x)‖ ≤ ‖(A x).flip‖ * ‖φ x‖ := (A x).flip.le_opNorm _
    _ = ‖A x‖ * ‖φ x‖ := by rw [ContinuousLinearMap.opNorm_flip]
    _ ≤ M * C := mul_le_mul (hA.bound x) (hC x hx) (norm_nonneg _) hM

theorem memLp_bfun (G : GelfandTriple V H) {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α : ℝ}
    (hA : IsFormFamily T A M α) {φ : ℝ → V} (hφ : IsTestV T φ) :
    MemLp (bfun G A φ) 2 (μT T) :=
  memLp_add' (memLp_of_continuous
      ((G.flat.continuous.comp (G.j.continuous.comp hφ.continuous_deriv)).neg) 2)
    (memLp_Aflip A hA hφ)

omit [CompleteSpace V] in
theorem integrable_A_self (A : ℝ → V →L[ℝ] V →L[ℝ] ℝ) {M α : ℝ} (hA : IsFormFamily T A M α)
    {φ : ℝ → V} (hφ : IsTestV T φ) : Integrable (fun t => A t (φ t) (φ t)) (μT T) := by
  obtain ⟨C, hC0, hC⟩ := hφ.exists_bound
  have hM : 0 ≤ M := (norm_nonneg (A 0)).trans (hA.bound 0)
  have hm : AEStronglyMeasurable (fun t => A t (φ t) (φ t)) (μT T) := by
    have := aestronglyMeasurable_clm_apply (memLp_Aflip A hA hφ).aestronglyMeasurable
      hφ.continuous.aestronglyMeasurable
    simpa only [ContinuousLinearMap.flip_apply] using this
  refine memLp_one_iff_integrable.mp (memLp_of_bound' hm (M * C * C) (fun x hx => ?_) 1)
  calc ‖A x (φ x) (φ x)‖ ≤ ‖A x (φ x)‖ * ‖φ x‖ := (A x (φ x)).le_opNorm _
    _ ≤ (‖A x‖ * ‖φ x‖) * ‖φ x‖ :=
        mul_le_mul_of_nonneg_right ((A x).le_opNorm _) (norm_nonneg _)
    _ ≤ (M * C) * C := mul_le_mul (mul_le_mul (hA.bound x) (hC x hx) (norm_nonneg _) hM)
        (hC x hx) (norm_nonneg _) (mul_nonneg hM hC0)


/-- The inclusion of test functions into `L²(0,T;V)`. -/
def testι (T : ℝ) : testSubmodule (V := V) T →ₗ[ℝ] Lp V 2 (μT T) where
  toFun := fun φ => (IsTestV.memLp (mem_testSubmodule.mp φ.2) 2).toLp (φ : ℝ → V)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

omit [CompleteSpace V] in
theorem coeFn_testι (φ : testSubmodule (V := V) T) :
    (testι T φ : ℝ → V) =ᵐ[μT T] (φ : ℝ → V) :=
  MemLp.coeFn_toLp (IsTestV.memLp (mem_testSubmodule.mp φ.2) 2)

/-- The "size" of a test function used in the coercivity estimate. -/
def testN (G : GelfandTriple V H) (T : ℝ) (φ : testSubmodule (V := V) T) : ℝ :=
  Real.sqrt ((∫ t, ‖(φ : ℝ → V) t‖ ^ 2 ∂(μT T)) + ‖G.j ((φ : ℝ → V) 0)‖ ^ 2)

omit [CompleteSpace V] in
theorem integral_norm_sq_nonneg (φ : testSubmodule (V := V) T) :
    0 ≤ ∫ t, ‖(φ : ℝ → V) t‖ ^ 2 ∂(μT T) :=
  integral_nonneg fun t => by positivity

theorem testN_nonneg (G : GelfandTriple V H) (φ : testSubmodule (V := V) T) :
    0 ≤ testN G T φ := Real.sqrt_nonneg _

theorem testN_sq (G : GelfandTriple V H) (φ : testSubmodule (V := V) T) :
    testN G T φ ^ 2 = (∫ t, ‖(φ : ℝ → V) t‖ ^ 2 ∂(μT T)) + ‖G.j ((φ : ℝ → V) 0)‖ ^ 2 :=
  Real.sq_sqrt (add_nonneg (integral_norm_sq_nonneg φ) (sq_nonneg _))

omit [CompleteSpace V] in
theorem norm_testι_sq (φ : testSubmodule (V := V) T) :
    ‖testι T φ‖ ^ 2 = ∫ t, ‖(φ : ℝ → V) t‖ ^ 2 ∂(μT T) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_testι φ] with t ht
  rw [ht, real_inner_self_eq_norm_sq]

theorem norm_testι_le (G : GelfandTriple V H) (φ : testSubmodule (V := V) T) :
    ‖testι T φ‖ ≤ testN G T φ := by
  rw [testN, Real.le_sqrt (norm_nonneg _) (add_nonneg (integral_norm_sq_nonneg φ) (sq_nonneg _)),
    norm_testι_sq]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem norm_j_le_testN (G : GelfandTriple V H) (φ : testSubmodule (V := V) T) :
    ‖G.j ((φ : ℝ → V) 0)‖ ≤ testN G T φ := by
  rw [testN, Real.le_sqrt (norm_nonneg _) (add_nonneg (integral_norm_sq_nonneg φ) (sq_nonneg _))]
  exact le_add_of_nonneg_left (integral_norm_sq_nonneg φ)


variable {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α : ℝ}

/-- The Riesz vector in `L²(0,T;V)` representing the form `E φ`. -/
def testW (G : GelfandTriple V H) (hA : IsFormFamily T A M α) (φ : testSubmodule (V := V) T) :
    Lp V 2 (μT T) :=
  (memLp_rieszV (memLp_bfun G hA (mem_testSubmodule.mp φ.2))).toLp
    (fun t => rieszV (bfun G A (φ : ℝ → V) t))

/-- The continuous linear form `u ↦ ∫₀ᵀ (−⟪j u, j φ'⟫ + 𝔞(t)[u, φ])`. -/
def testE (G : GelfandTriple V H) (hA : IsFormFamily T A M α) (φ : testSubmodule (V := V) T) :
    Lp V 2 (μT T) →L[ℝ] ℝ :=
  innerSL ℝ (testW G hA φ)

theorem testE_apply (G : GelfandTriple V H) (hA : IsFormFamily T A M α)
    (φ : testSubmodule (V := V) T) (u : Lp V 2 (μT T)) :
    testE G hA φ u = ∫ t, bfun G A (φ : ℝ → V) t (u t) ∂(μT T) := by
  simpa only [testE, innerSL_apply_apply, testW] using
    inner_toLp_rieszV (memLp_bfun G hA (mem_testSubmodule.mp φ.2)) u

theorem testW_add (G : GelfandTriple V H) (hA : IsFormFamily T A M α)
    (φ ψ : testSubmodule (V := V) T) :
    testW G hA (φ + ψ) = testW G hA φ + testW G hA ψ := by
  simp only [testW]
  rw [← MemLp.toLp_add]
  refine (MemLp.toLp_eq_toLp_iff _ _).mpr (Filter.Eventually.of_forall fun t => ?_)
  have h : bfun G A ((φ + ψ : testSubmodule (V := V) T) : ℝ → V) t
      = bfun G A (φ : ℝ → V) t + bfun G A (ψ : ℝ → V) t := by
    have h' := bfun_add G A (mem_testSubmodule.mp φ.2) (mem_testSubmodule.mp ψ.2)
    exact congrFun h' t
  simp only [Pi.add_apply, h]
  exact rieszV_add _ _

theorem testW_smul (G : GelfandTriple V H) (hA : IsFormFamily T A M α) (c : ℝ)
    (φ : testSubmodule (V := V) T) : testW G hA (c • φ) = c • testW G hA φ := by
  simp only [testW]
  rw [← MemLp.toLp_const_smul]
  refine (MemLp.toLp_eq_toLp_iff _ _).mpr (Filter.Eventually.of_forall fun t => ?_)
  have h : bfun G A ((c • φ : testSubmodule (V := V) T) : ℝ → V) t
      = c • bfun G A (φ : ℝ → V) t := by
    have h' := bfun_smul G A c (mem_testSubmodule.mp φ.2)
    exact congrFun h' t
  simp only [Pi.smul_apply, h]
  exact rieszV_smul _ _

theorem testE_isLinear (G : GelfandTriple V H) (hA : IsFormFamily T A M α)
    (u : Lp V 2 (μT T)) : IsLinearMap ℝ (fun φ => testE G hA φ u) := by
  constructor
  · intro φ ψ
    simp only [testE, innerSL_apply_apply, testW_add, inner_add_left]
  · intro c φ
    simp only [testE, innerSL_apply_apply, testW_smul, real_inner_smul_left, smul_eq_mul]


/-- The boundary term: `∫₀ᵀ ⟪jφ, jφ'⟫ = −½ ‖jφ(0)‖²` for a test function `φ` (which vanishes
at `T`). -/
theorem integral_inner_j_deriv (G : GelfandTriple V H) (hT : 0 < T) {ψ : ℝ → V}
    (hψ : IsTestV T ψ) :
    ∫ t, ⟪G.j (ψ t), G.j (deriv ψ t)⟫_ℝ ∂(μT T) = -(1 / 2 * ‖G.j (ψ 0)‖ ^ 2) := by
  have hcont : Continuous fun t => ⟪G.j (ψ t), G.j (deriv ψ t)⟫_ℝ :=
    Continuous.inner (G.j.continuous.comp hψ.continuous)
      (G.j.continuous.comp hψ.continuous_deriv)
  have hj : ∀ t, HasDerivAt (fun s => G.j (ψ s)) (G.j (deriv ψ t)) t := fun t =>
    G.j.hasFDerivAt.comp_hasDerivAt t ((hψ.differentiable t).hasDerivAt)
  have hF : ∀ t, HasDerivAt (fun s => ⟪G.j (ψ s), G.j (ψ s)⟫_ℝ)
      (2 * ⟪G.j (ψ t), G.j (deriv ψ t)⟫_ℝ) t := by
    intro t
    have h := HasDerivAt.inner ℝ (hj t) (hj t)
    have heq : ⟪G.j (ψ t), G.j (deriv ψ t)⟫_ℝ + ⟪G.j (deriv ψ t), G.j (ψ t)⟫_ℝ
        = 2 * ⟪G.j (ψ t), G.j (deriv ψ t)⟫_ℝ := by
      rw [real_inner_comm (G.j (deriv ψ t)) (G.j (ψ t))]; ring
    rwa [heq] at h
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := T)
    (fun x _ => hF x) ((hcont.const_mul 2).intervalIntegrable 0 T)
  rw [intervalIntegral.integral_const_mul] at hFTC
  have hzero : ψ T = 0 := hψ.2 T le_rfl
  rw [hzero] at hFTC
  simp only [map_zero, inner_zero_left, zero_sub] at hFTC
  rw [real_inner_self_eq_norm_sq] at hFTC
  rw [μT, ← intervalIntegral.integral_of_le hT.le]
  linarith

/-- Coercivity of the form `E`. -/
theorem coercive_bfun (G : GelfandTriple V H) (hA : IsFormFamily T A M α) (hT : 0 < T)
    {ψ : ℝ → V} (hψ : IsTestV T ψ) :
    min (1 / 2 : ℝ) α * ((∫ t, ‖ψ t‖ ^ 2 ∂(μT T)) + ‖G.j (ψ 0)‖ ^ 2)
      ≤ ∫ t, bfun G A ψ t (ψ t) ∂(μT T) := by
  have hcont : Continuous fun t => ⟪G.j (ψ t), G.j (deriv ψ t)⟫_ℝ :=
    Continuous.inner (G.j.continuous.comp hψ.continuous)
      (G.j.continuous.comp hψ.continuous_deriv)
  have hint1 : Integrable (fun t => ⟪G.j (ψ t), G.j (deriv ψ t)⟫_ℝ) (μT T) :=
    memLp_one_iff_integrable.mp (memLp_of_continuous hcont 1)
  have hint2 : Integrable (fun t => A t (ψ t) (ψ t)) (μT T) := integrable_A_self A hA hψ
  have hsplit : ∫ t, bfun G A ψ t (ψ t) ∂(μT T)
      = -(∫ t, ⟪G.j (ψ t), G.j (deriv ψ t)⟫_ℝ ∂(μT T)) + ∫ t, A t (ψ t) (ψ t) ∂(μT T) := by
    have hc : ∫ t, bfun G A ψ t (ψ t) ∂(μT T)
        = ∫ t, (-(⟪G.j (ψ t), G.j (deriv ψ t)⟫_ℝ) + A t (ψ t) (ψ t)) ∂(μT T) :=
      integral_congr_ae (Filter.Eventually.of_forall fun t => bfun_apply G A ψ t (ψ t))
    have hneg : Integrable (fun t => -(⟪G.j (ψ t), G.j (deriv ψ t)⟫_ℝ)) (μT T) := hint1.neg
    rw [hc, integral_add hneg hint2, integral_neg]
  have hnormsq : Integrable (fun t => α * ‖ψ t‖ ^ 2) (μT T) :=
    memLp_one_iff_integrable.mp
      (memLp_of_continuous (continuous_const.mul (hψ.continuous.norm.pow 2)) 1)
  have h4 : α * (∫ t, ‖ψ t‖ ^ 2 ∂(μT T)) ≤ ∫ t, A t (ψ t) (ψ t) ∂(μT T) := by
    rw [← integral_const_mul]
    exact integral_mono hnormsq hint2 fun t => hA.coercive t (ψ t)
  have hI : (0 : ℝ) ≤ ∫ t, ‖ψ t‖ ^ 2 ∂(μT T) := integral_nonneg fun t => by positivity
  have e1 : min (1 / 2 : ℝ) α * (∫ t, ‖ψ t‖ ^ 2 ∂(μT T)) ≤ α * (∫ t, ‖ψ t‖ ^ 2 ∂(μT T)) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hI
  have e2 : min (1 / 2 : ℝ) α * ‖G.j (ψ 0)‖ ^ 2 ≤ 1 / 2 * ‖G.j (ψ 0)‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  rw [hsplit, integral_inner_j_deriv G hT hψ, mul_add]
  linarith

theorem testE_coercive (G : GelfandTriple V H) (hA : IsFormFamily T A M α) (hT : 0 < T)
    (φ : testSubmodule (V := V) T) :
    min (1 / 2 : ℝ) α * testN G T φ ^ 2 ≤ testE G hA φ (testι T φ) := by
  have hψ : IsTestV T ((φ : ℝ → V)) := mem_testSubmodule.mp φ.2
  have h1 : testE G hA φ (testι T φ) = ∫ t, bfun G A (φ : ℝ → V) t ((φ : ℝ → V) t) ∂(μT T) := by
    rw [testE_apply]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_testι φ] with t ht
    rw [ht]
  rw [h1, testN_sq]
  exact coercive_bfun G hA hT hψ


theorem intervalIntegral_eq_integral_μT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hT : (0 : ℝ) ≤ T) (g : ℝ → E) : ∫ t in (0 : ℝ)..T, g t = ∫ t, g t ∂(μT T) := by
  rw [intervalIntegral.integral_of_le hT]; rfl

/-- The right-hand side functional of Lions' theorem. -/
def testL (G : GelfandTriple V H) (T : ℝ) {f : ℝ → StrongDual ℝ V} (hf : MemLp f 2 (μT T))
    (u₀ : H) : testSubmodule (V := V) T →ₗ[ℝ] ℝ where
  toFun := fun φ => ⟪(memLp_rieszV hf).toLp (fun t => rieszV (f t)), testι T φ⟫_ℝ
    + ⟪u₀, G.j ((φ : ℝ → V) 0)⟫_ℝ
  map_add' := by
    intro φ ψ
    simp only [map_add, inner_add_right, Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' := by
    intro c φ
    simp only [map_smul, real_inner_smul_right, SetLike.val_smul, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul]
    ring

theorem testL_apply (G : GelfandTriple V H) (T : ℝ) {f : ℝ → StrongDual ℝ V}
    (hf : MemLp f 2 (μT T)) (u₀ : H) (φ : testSubmodule (V := V) T) :
    testL G T hf u₀ φ
      = (∫ t, f t ((φ : ℝ → V) t) ∂(μT T)) + ⟪u₀, G.j ((φ : ℝ → V) 0)⟫_ℝ := by
  show ⟪(memLp_rieszV hf).toLp (fun t => rieszV (f t)), testι T φ⟫_ℝ
      + ⟪u₀, G.j ((φ : ℝ → V) 0)⟫_ℝ = _
  congr 1
  rw [inner_toLp_rieszV hf (testι T φ)]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_testι φ] with t ht
  rw [ht]

theorem testL_bound (G : GelfandTriple V H) {T : ℝ} {f : ℝ → StrongDual ℝ V}
    (hf : MemLp f 2 (μT T)) (u₀ : H) (φ : testSubmodule (V := V) T) :
    |testL G T hf u₀ φ| ≤ ((eLpNorm f 2 (μT T)).toReal + ‖u₀‖) * testN G T φ := by
  have hW : ‖(memLp_rieszV hf).toLp (fun t => rieszV (f t))‖ = (eLpNorm f 2 (μT T)).toReal :=
    norm_toLp_rieszV hf
  have h1 : |⟪(memLp_rieszV hf).toLp (fun t => rieszV (f t)), testι T φ⟫_ℝ|
      ≤ (eLpNorm f 2 (μT T)).toReal * testN G T φ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hW]
    exact mul_le_mul_of_nonneg_left (norm_testι_le G φ) ENNReal.toReal_nonneg
  have h2 : |⟪u₀, G.j ((φ : ℝ → V) 0)⟫_ℝ| ≤ ‖u₀‖ * testN G T φ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_j_le_testN G φ) (norm_nonneg _))
  have : testL G T hf u₀ φ = ⟪(memLp_rieszV hf).toLp (fun t => rieszV (f t)), testι T φ⟫_ℝ
      + ⟪u₀, G.j ((φ : ℝ → V) 0)⟫_ℝ := rfl
  rw [this, add_mul]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

end Existence

/-- **Lions' theorem, existence part**, with the energy bound for the constructed solution. -/
theorem lions_existence_bound (G : GelfandTriple V H) {T : ℝ} (hT : 0 < T)
    {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α : ℝ} (hA : IsFormFamily T A M α)
    {f : ℝ → StrongDual ℝ V} (hf : MemLp f 2 (μT T)) (u₀ : H) :
    ∃ u : ℝ → V, IsVariationalSolution G T A f u₀ u ∧
      (eLpNorm u 2 (μT T)).toReal
        ≤ ((eLpNorm f 2 (μT T)).toReal + ‖u₀‖) / min (1 / 2) α := by
  obtain ⟨uLp, hsol, hnorm⟩ := lions_projection (testι T) (testN G T) (testN_nonneg G)
    (norm_testι_le G) (testE G hA) (testE_isLinear G hA)
    (α := min (1 / 2) α) (lt_min (by norm_num) hA.α_pos)
    (testE_coercive G hA hT) (testL G T hf u₀)
    (C := (eLpNorm f 2 (μT T)).toReal + ‖u₀‖)
    (by positivity) (testL_bound G hf u₀)
  refine ⟨(uLp : ℝ → V), ⟨Lp.memLp uLp, ?_⟩, ?_⟩
  · intro φ hφ
    have hco : ((⟨φ, hφ⟩ : testSubmodule (V := V) T) : ℝ → V) = φ := rfl
    have h := hsol ⟨φ, hφ⟩
    rw [testE_apply, testL_apply, hco] at h
    rw [intervalIntegral_eq_integral_μT hT.le, intervalIntegral_eq_integral_μT hT.le, ← h]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun t => (bfun_apply G A φ t ((uLp : ℝ → V) t)).symm)
  · rw [← Lp.norm_def]
    exact hnorm

/-- **Lions' theorem, existence part.** -/
theorem lions_existence (G : GelfandTriple V H) {T : ℝ} (hT : 0 < T)
    {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α : ℝ} (hA : IsFormFamily T A M α)
    {f : ℝ → StrongDual ℝ V} (hf : MemLp f 2 (μT T)) (u₀ : H) :
    ∃ u : ℝ → V, IsVariationalSolution G T A f u₀ u :=
  let ⟨u, hu, _⟩ := lions_existence_bound G hT hA hf u₀; ⟨u, hu⟩



end LionsC12

end
