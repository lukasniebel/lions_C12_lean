module

public import LionsC12.Construction.Defs
public import LionsC12.Coefficient.Blocks
public import LionsC12.Coefficient.Support
public import LionsC12.Modes.Trig
public import LionsC12.Solution.Basic
public import LionsC12.Solution.Divergence
public import LionsC12.Forcing.Cancellation
public import LionsC12.Coefficient.Holder
public import LionsC12.Coefficient.Sharpness
public import LionsC12.Forcing.Continuity
public import LionsC12.Forcing.Elliptic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Zero extension and parabolic rescaling of the interval construction

The one-dimensional objects of Section 6 of the paper, as explicit functions:

* the zero extension `Z g` of a function on `(0,π)` to `ℝ` (`E₀` in the paper), and the zero
  extensions `uZ`, `utZ`, `uxZ`, `fZ` of the solution, its derivatives and the forcing; `uZ(t,·)`
  is continuous because `u(t,·)` vanishes at `0` and `π`, and `‖∂ₜuZ(t)‖_{L²(ℝ)} = ‖∂ₜu(t)‖_H`;
* the parabolic rescaling `(t,x) ↦ (t/r², (x - x₀)/r)` of the coefficient, the solution and
  the forcing (`bR`, `UR`, `URx`, `FR`), with the ½-Hölder bound `C/r`, the failure of
  `α`-Hölder continuity (`bR_not_holder`), and `∂ₜUR ∉ L²` (`not_integrableOn_URt`).

The Hilbert-space statements built on these functions are in `LionsC12/Domains/`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ## The zero extension -/

/-- The zero extension of a function on `(0,π)` to the whole line. -/
def Z (g : ℝ → ℝ) (x : ℝ) : ℝ := if x ∈ Set.Ioo (0 : ℝ) π then g x else 0

theorem Z_of_mem {g : ℝ → ℝ} {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) π) : Z g x = g x := ite_eq_left hx

theorem Z_of_notMem {g : ℝ → ℝ} {x : ℝ} (hx : x ∉ Set.Ioo (0 : ℝ) π) : Z g x = 0 := ite_eq_right hx

theorem abs_Z_le (g : ℝ → ℝ) (x : ℝ) : |Z g x| ≤ |g x| := by
  unfold Z
  split_ifs with h
  · exact le_refl _
  · simp

theorem Z_eventuallyEq_of_mem {g : ℝ → ℝ} {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) π) :
    Z g =ᶠ[nhds x] g := by
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact Z_of_mem hy

private theorem lt_zero_or_pi_lt {x : ℝ} (hx : x ∉ Set.Ioo (0 : ℝ) π) (hx0 : x ≠ 0) (hxπ : x ≠ π) :
    x < 0 ∨ π < x := by
  rcases lt_or_ge x 0 with h | h
  · exact Or.inl h
  · have hx0' : 0 < x := lt_of_le_of_ne h (Ne.symm hx0)
    have hnot : ¬ x < π := fun hlt => hx ⟨hx0', hlt⟩
    exact Or.inr (lt_of_le_of_ne (not_lt.1 hnot) (Ne.symm hxπ))

theorem Z_eventuallyEq_zero {g : ℝ → ℝ} {x : ℝ} (hx : x ∉ Set.Ioo (0 : ℝ) π) (hx0 : x ≠ 0)
    (hxπ : x ≠ π) : Z g =ᶠ[nhds x] fun _ => (0 : ℝ) := by
  rcases lt_zero_or_pi_lt hx hx0 hxπ with h | h
  · filter_upwards [Iio_mem_nhds h] with y hy
    exact Z_of_notMem (fun hy' => absurd hy'.1 (not_lt.2 (le_of_lt hy)))
  · filter_upwards [Ioi_mem_nhds h] with y hy
    exact Z_of_notMem (fun hy' => absurd hy'.2 (not_lt.2 (le_of_lt hy)))

/-- The zero extension of a continuous function vanishing at `0` and `π` is continuous. -/
theorem continuous_Z {g : ℝ → ℝ} (hg : Continuous g) (h0 : g 0 = 0) (hπ : g π = 0) :
    Continuous (Z g) := by
  have key : ∀ x₀ : ℝ, g x₀ = 0 → ContinuousAt (Z g) x₀ := by
    intro x₀ hx₀
    have hz : Z g x₀ = 0 := by
      unfold Z; split_ifs with h
      · exact hx₀
      · rfl
    rw [ContinuousAt, hz]
    refine squeeze_zero_norm (a := fun y => ‖g y‖) (fun y => ?_) ?_
    · simpa [Real.norm_eq_abs] using abs_Z_le g y
    · have h := (hg.norm).tendsto x₀
      simpa [hx₀] using h
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hmem : x ∈ Set.Ioo (0 : ℝ) π
  · exact hg.continuousAt.congr (Z_eventuallyEq_of_mem hmem).symm
  · rcases eq_or_ne x 0 with rfl | hx0
    · exact key 0 h0
    · rcases eq_or_ne x π with rfl | hxπ
      · exact key π hπ
      · exact continuousAt_const.congr (Z_eventuallyEq_zero hmem hx0 hxπ).symm

/-- The zero-extended solution. -/
def uZ (ε : ℝ) (t x : ℝ) : ℝ := Z (u D ε t) x

/-- The zero extension of `∂_t u`. -/
def utZ (ε : ℝ) (t x : ℝ) : ℝ := Z (ut D ε t) x

/-- The zero extension of `∂_x u`. -/
def uxZ (ε : ℝ) (t x : ℝ) : ℝ := Z (ux D ε t) x

/-- The zero extension of the forcing. -/
def fZ (ε : ℝ) (t x : ℝ) : ℝ := Z (f D ε t) x

theorem continuous_u_x (ε t : ℝ) : Continuous (u D ε t) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_u_x D ε t x).continuousAt

theorem uZ_continuous_x (ε t : ℝ) : Continuous (uZ D ε t) :=
  continuous_Z (continuous_u_x D ε t) (u_zero_left D ε t) (u_zero_right D ε t)

theorem hasDerivAt_uZ_t (ε : ℝ) (t x : ℝ) :
    HasDerivAt (fun t => uZ D ε t x) (utZ D ε t x) t := by
  by_cases hmem : x ∈ Set.Ioo (0 : ℝ) π
  · have h1 : (fun t => uZ D ε t x) = fun t => u D ε t x := by
      funext s; exact Z_of_mem hmem
    have h2 : utZ D ε t x = ut D ε t x := Z_of_mem hmem
    rw [h1, h2]
    exact hasDerivAt_u_t D ε t x
  · have h1 : (fun t => uZ D ε t x) = fun _ => (0 : ℝ) := by
      funext s; exact Z_of_notMem hmem
    have h2 : utZ D ε t x = 0 := Z_of_notMem hmem
    rw [h1, h2]
    exact hasDerivAt_const _ _

/-- The `L²(ℝ)`-norm of the zero extension equals the `L²(0,π)`-norm. -/
theorem integral_Z_sq (g : ℝ → ℝ) : ∫ x, (Z g x) ^ 2 = normSq g := by
  have h1 : (fun x => (Z g x) ^ 2) = Set.indicator (Set.Ioo (0 : ℝ) π) (fun x => g x ^ 2) := by
    funext x
    by_cases hx : x ∈ Set.Ioo (0 : ℝ) π
    · rw [Z_of_mem hx, Set.indicator_of_mem hx]
    · rw [Z_of_notMem hx, Set.indicator_of_notMem hx]
      norm_num
  rw [h1, MeasureTheory.integral_indicator measurableSet_Ioo, normSq,
    intervalIntegral.integral_of_le Real.pi_pos.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem integral_sq_utZ (ε t : ℝ) : ∫ x, (utZ D ε t x) ^ 2 = utNormSq D ε t :=
  integral_Z_sq (ut D ε t)

/-! ## Parabolic rescaling to a bounded interval -/

/-- The rescaled coefficient. -/
def bR (ε r x₀ : ℝ) (t x : ℝ) : ℝ := a D ε (t / r ^ 2) ((x - x₀) / r)

/-- The rescaled solution. -/
def UR (ε r x₀ : ℝ) (t x : ℝ) : ℝ := uZ D ε (t / r ^ 2) ((x - x₀) / r)

/-- The spatial derivative of the rescaled solution `UR`. -/
def URx (ε r x₀ : ℝ) (t x : ℝ) : ℝ := r⁻¹ * uxZ D ε (t / r ^ 2) ((x - x₀) / r)

/-- The rescaled forcing. -/
def FR (ε r x₀ : ℝ) (t x : ℝ) : ℝ := r⁻¹ ^ 2 * fZ D ε (t / r ^ 2) ((x - x₀) / r)

theorem abs_bR_sub_one_le {ε : ℝ} (hε0 : 0 ≤ ε) (r x₀ t x : ℝ) :
    |bR D ε r x₀ t x - 1| ≤ ε / 480 := abs_a_sub_one_le D hε0 _ _

theorem abs_bR_sub_le (ε : ℝ) {r : ℝ} (hr : 0 < r) (x₀ s t x : ℝ) :
    |bR D ε r x₀ t x - bR D ε r x₀ s x| ≤ 2 * |ε| * Cβ D / r * Real.sqrt |t - s| := by
  have h := abs_a_sub_le D ε (s / r ^ 2) (t / r ^ 2) ((x - x₀) / r)
  have hdiff : t / r ^ 2 - s / r ^ 2 = (t - s) / r ^ 2 := by ring
  have habs : |t / r ^ 2 - s / r ^ 2| = |t - s| / r ^ 2 := by
    rw [hdiff, abs_div, abs_of_pos (by positivity : (0:ℝ) < r ^ 2)]
  have hsqrt : Real.sqrt (|t / r ^ 2 - s / r ^ 2|) = Real.sqrt |t - s| / r := by
    rw [habs, Real.sqrt_div (abs_nonneg _), Real.sqrt_sq hr.le]
  rw [bR, bR]
  rw [hsqrt] at h
  calc |a D ε (t / r ^ 2) ((x - x₀) / r) - a D ε (s / r ^ 2) ((x - x₀) / r)|
      ≤ 2 * |ε| * Cβ D * (Real.sqrt |t - s| / r) := h
    _ = 2 * |ε| * Cβ D / r * Real.sqrt |t - s| := by ring

theorem bR_not_holder {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (x₀ : ℝ) {α : ℝ}
    (hα : 1 / 2 < α) (hα1 : α < 1) (C : ℝ) :
    ∃ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧ t ∈ Set.Icc (0 : ℝ) 1 ∧ s ≠ t ∧
      C * |t - s| ^ α < |bR D ε r x₀ t x₀ - bR D ε r x₀ s x₀| := by
  obtain ⟨σ, τ, hσ, hτ, hne, hlt⟩ := not_holder D hε hα hα1 (max C 0)
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hr2' : r ^ 2 ≤ 1 := by nlinarith
  have hval : ∀ w : ℝ, bR D ε r x₀ (r ^ 2 * w) x₀ = a D ε w 0 := by
    intro w
    rw [bR, mul_div_cancel_left₀ _ hr2.ne', sub_self, zero_div]
  obtain ⟨hσ0, hσ1⟩ := hσ
  obtain ⟨hτ0, hτ1⟩ := hτ
  refine ⟨r ^ 2 * σ, r ^ 2 * τ, ⟨by positivity, by nlinarith⟩, ⟨by positivity, by nlinarith⟩,
    ?_, ?_⟩
  · exact fun hc => hne (by
      have := mul_left_cancel₀ hr2.ne' hc
      exact this)
  · have hts : |r ^ 2 * τ - r ^ 2 * σ| = r ^ 2 * |τ - σ| := by
      rw [← mul_sub, abs_mul, abs_of_pos hr2]
    have hrp : ((r ^ 2 : ℝ)) ^ α ≤ 1 := Real.rpow_le_one hr2.le hr2' (by linarith)
    have hrpow : |r ^ 2 * τ - r ^ 2 * σ| ^ α ≤ |τ - σ| ^ α := by
      rw [hts, Real.mul_rpow hr2.le (abs_nonneg _)]
      nlinarith [Real.rpow_nonneg (abs_nonneg (τ - σ)) α, Real.rpow_nonneg hr2.le α]
    rw [hval, hval]
    calc C * |r ^ 2 * τ - r ^ 2 * σ| ^ α
        ≤ max C 0 * |r ^ 2 * τ - r ^ 2 * σ| ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) α)
      _ ≤ max C 0 * |τ - σ| ^ α := mul_le_mul_of_nonneg_left hrpow (le_max_right _ _)
      _ < |a D ε τ 0 - a D ε σ 0| := hlt

theorem hasDerivAt_UR_t (ε r x₀ t x : ℝ) :
    HasDerivAt (fun t => UR D ε r x₀ t x) (r⁻¹ ^ 2 * utZ D ε (t / r ^ 2) ((x - x₀) / r)) t := by
  have h1 : HasDerivAt (fun s : ℝ => s / r ^ 2) (1 / r ^ 2) t := by
    simpa using (hasDerivAt_id t).div_const (r ^ 2)
  have h2 := (hasDerivAt_uZ_t D ε (t / r ^ 2) ((x - x₀) / r)).comp t h1
  have h3 : (fun s : ℝ => UR D ε r x₀ s x)
      = (fun T => uZ D ε T ((x - x₀) / r)) ∘ fun s : ℝ => s / r ^ 2 := rfl
  have hval : r⁻¹ ^ 2 * utZ D ε (t / r ^ 2) ((x - x₀) / r)
      = utZ D ε (t / r ^ 2) ((x - x₀) / r) * (1 / r ^ 2) := by ring
  rw [h3, hval]
  exact h2

theorem UR_initial (ε r x₀ x : ℝ) : UR D ε r x₀ 0 x = 0 := by
  rw [UR, zero_div]
  unfold uZ Z
  split_ifs with h
  · exact u_initial D ε _
  · rfl

theorem integral_sq_URt (ε : ℝ) {r : ℝ} (hr : 0 < r) (x₀ t : ℝ) :
    ∫ x, (r⁻¹ ^ 2 * utZ D ε (t / r ^ 2) ((x - x₀) / r)) ^ 2
      = r⁻¹ ^ 3 * utNormSq D ε (t / r ^ 2) := by
  have hstep : ∫ x, (utZ D ε (t / r ^ 2) ((x - x₀) / r)) ^ 2
      = r * utNormSq D ε (t / r ^ 2) := by
    have h1 : ∫ x, (utZ D ε (t / r ^ 2) ((x - x₀) / r)) ^ 2
        = ∫ x, (fun w : ℝ => (utZ D ε (t / r ^ 2) (w / r)) ^ 2) (x - x₀) := rfl
    rw [h1, MeasureTheory.integral_sub_right_eq_self
      (fun w : ℝ => (utZ D ε (t / r ^ 2) (w / r)) ^ 2) x₀]
    have h2 : ∫ w, (utZ D ε (t / r ^ 2) (w / r)) ^ 2
        = ∫ w, (fun y : ℝ => (utZ D ε (t / r ^ 2) y) ^ 2) (w / r) := rfl
    rw [h2, MeasureTheory.Measure.integral_comp_div (fun y : ℝ => (utZ D ε (t / r ^ 2) y) ^ 2) r,
      integral_sq_utZ, smul_eq_mul, abs_of_pos hr]
  have h3 : ∫ x, (r⁻¹ ^ 2 * utZ D ε (t / r ^ 2) ((x - x₀) / r)) ^ 2
      = ∫ x, (r⁻¹ ^ 2) ^ 2 * (utZ D ε (t / r ^ 2) ((x - x₀) / r)) ^ 2 := by
    simp only [mul_pow]
  rw [h3, MeasureTheory.integral_const_mul, hstep]
  field_simp

theorem not_integrableOn_URt {ε : ℝ} (hε : ε ≠ 0) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (x₀ : ℝ) :
    ¬ MeasureTheory.IntegrableOn
      (fun t => ∫ x, (r⁻¹ ^ 2 * utZ D ε (t / r ^ 2) ((x - x₀) / r)) ^ 2) (Set.Icc (0 : ℝ) 1) := by
  intro h
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hr2' : r ^ 2 ≤ 1 := by nlinarith
  have heq : (fun t => ∫ x, (r⁻¹ ^ 2 * utZ D ε (t / r ^ 2) ((x - x₀) / r)) ^ 2)
      = fun t => r⁻¹ ^ 3 * utNormSq D ε (t / r ^ 2) :=
    funext fun t => integral_sq_URt D ε hr x₀ t
  rw [heq] at h
  have h2 : MeasureTheory.IntegrableOn (fun t => utNormSq D ε (t / r ^ 2)) (Set.Icc (0 : ℝ) 1) := by
    have h3 : MeasureTheory.IntegrableOn
        (fun t => r ^ 3 * (r⁻¹ ^ 3 * utNormSq D ε (t / r ^ 2))) (Set.Icc (0 : ℝ) 1) :=
      h.const_mul _
    refine MeasureTheory.IntegrableOn.congr_fun h3 ?_ measurableSet_Icc
    intro t _
    field_simp
  refine not_integrableOn_utNormSq D hε ?_
  have hG : MeasureTheory.Integrable
      (Set.indicator (Set.Icc (0 : ℝ) 1) fun t => utNormSq D ε (t / r ^ 2)) :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).2 h2
  have hG2 := (MeasureTheory.integrable_comp_mul_left_iff
    (Set.indicator (Set.Icc (0 : ℝ) 1) fun t => utNormSq D ε (t / r ^ 2)) hr2.ne').2 hG
  have hG3 : MeasureTheory.IntegrableOn
      (fun s => (Set.indicator (Set.Icc (0 : ℝ) 1) fun t => utNormSq D ε (t / r ^ 2)) (r ^ 2 * s))
      (Set.Icc (0 : ℝ) 1) := hG2.integrableOn
  refine MeasureTheory.IntegrableOn.congr_fun hG3 ?_ measurableSet_Icc
  intro s hs
  obtain ⟨hs0, hs1⟩ := hs
  have hmem : r ^ 2 * s ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, by nlinarith⟩
  show (Set.Icc (0 : ℝ) 1).indicator (fun t => utNormSq D ε (t / r ^ 2)) (r ^ 2 * s)
      = utNormSq D ε s
  rw [Set.indicator_of_mem hmem]
  rw [mul_div_cancel_left₀ _ hr2.ne']

end LionsC12

end
