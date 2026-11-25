module

public import LionsC12.Domains.Spaces
public import LionsC12.Spaces.TimeL2
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Coordinates `x = (x₁, x')` on `ℝ^{n+1}`

The splitting `ℝ^{n+1} = ℝ × ℝ^n` of `EuclideanSpace ℝ (Fin (n+1))` into the first coordinate
and the tail, used to tensorise the one-dimensional construction:

* `tailL n : ℝ^{n+1} →L ℝ^n`, `x ↦ x' = (x₂, …, x_{n+1})`;
* `insE n : ℝ × ℝ^n ≃L ℝ^{n+1}`, `(s, y) ↦ (s, y)`, with inverse `x ↦ (x₁, x')`;
* `measurePreserving_insE` — `insE n` preserves Lebesgue measure (Fubini in these coordinates);
* `norm_sq_eq_head_tail` — `‖x‖² = x₁² + ‖x'‖²`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology

variable {n : ℕ}

/-- The tail `x' = (x₂, …, x_{n+1})` of a point of `ℝ^{n+1}`. -/
def tailL (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => EuclideanSpace.proj j.succ)

@[simp] theorem tailL_apply (x : EuclideanSpace ℝ (Fin (n + 1))) (j : Fin n) :
    tailL n x j = x j.succ := rfl

/-- The linear map `(s, y) ↦ (s, y₁, …, yₙ)`. -/
def insLin (n : ℕ) : (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun p := WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (n + 1) → ℝ)
  map_add' p q := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c p := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The coordinates `ℝ × ℝ^n ≃ ℝ^{n+1}`. -/
def insE (n : ℕ) : (ℝ × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  ContinuousLinearEquiv.equivOfInverse (LinearMap.toContinuousLinearMap (insLin n))
    ((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).prod (tailL n))
    (fun p => by
      ext
      · simp [insLin]
      · simp [insLin])
    (fun x => by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [insLin])

@[simp] theorem insE_apply_zero (p : ℝ × EuclideanSpace ℝ (Fin n)) : insE n p 0 = p.1 := rfl

@[simp] theorem insE_apply_succ (p : ℝ × EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    insE n p j.succ = p.2 j := rfl

@[simp] theorem tailL_insE (p : ℝ × EuclideanSpace ℝ (Fin n)) : tailL n (insE n p) = p.2 := by
  ext j
  simp

theorem insE_symm_apply (x : EuclideanSpace ℝ (Fin (n + 1))) :
    (insE n).symm x = (x 0, tailL n x) := rfl

theorem insE_eq (s : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    insE n (s, y) = insE n (0, y) + s • EuclideanSpace.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem tailL_single_zero : tailL n (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) = 0 := by
  ext j
  simp [Fin.succ_ne_zero]

theorem tailL_single_succ (j : Fin n) :
    tailL n (EuclideanSpace.single j.succ (1 : ℝ)) = EuclideanSpace.single j 1 := by
  ext k
  by_cases h : k = j
  · subst h; simp
  · simp [h]

theorem single_succ_apply_zero (j : Fin n) :
    (EuclideanSpace.single j.succ (1 : ℝ) : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 := by
  simp [(Fin.succ_ne_zero j).symm]

theorem single_zero_apply_zero :
    (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin (n + 1))) 0 = 1 := by
  simp

/-- `insE n` preserves Lebesgue measure. -/
theorem measurePreserving_insE (n : ℕ) : MeasurePreserving (insE n) := by
  have h1 : MeasurePreserving (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, WithLp.ofLp p.2))
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod (PiLp.volume_preserving_ofLp (Fin n))
  have h2 := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have h3 := PiLp.volume_preserving_toLp (Fin (n + 1))
  have h := h3.comp (h2.comp h1)
  convert h using 1
  funext p
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [MeasurableEquiv.piFinSuccAbove]
  · simp [MeasurableEquiv.piFinSuccAbove]

theorem measurableEmbedding_insE (n : ℕ) : MeasurableEmbedding (insE n) :=
  (insE n).toHomeomorph.measurableEmbedding

/-- Integrals over `ℝ^{n+1}` in the coordinates `(x₁, x')`. -/
theorem integral_comp_insE {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : EuclideanSpace ℝ (Fin (n + 1)) → G) :
    ∫ p, f (insE n p) = ∫ x, f x :=
  (measurePreserving_insE n).integral_comp (measurableEmbedding_insE n) f

theorem integrable_comp_insE_iff {G : Type*} [NormedAddCommGroup G]
    {f : EuclideanSpace ℝ (Fin (n + 1)) → G} :
    Integrable (f ∘ insE n) ↔ Integrable f :=
  (measurePreserving_insE n).integrable_comp_emb (measurableEmbedding_insE n)

/-- `‖x‖² = x₁² + ‖x'‖²`. -/
theorem norm_sq_eq_head_tail (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖x‖ ^ 2 = x 0 ^ 2 + ‖tailL n x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), Fin.sum_univ_succ]
  simp [Real.norm_eq_abs, sq_abs]

theorem norm_le_head_add_tail (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖x‖ ≤ |x 0| + ‖tailL n x‖ := by
  have h := norm_sq_eq_head_tail x
  nlinarith [norm_nonneg x, abs_nonneg (x 0), norm_nonneg (tailL n x), sq_abs (x 0)]

theorem abs_head_le_norm (x : EuclideanSpace ℝ (Fin (n + 1))) : |x 0| ≤ ‖x‖ := by
  have h := norm_sq_eq_head_tail x
  nlinarith [norm_nonneg x, abs_nonneg (x 0), norm_nonneg (tailL n x), sq_abs (x 0)]

end LionsC12
