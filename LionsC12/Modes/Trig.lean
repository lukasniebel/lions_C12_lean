module

public import LionsC12.Construction.Defs
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The spatial oscillatory modes (Section 2 of the paper)

This file contains the elementary calculus and the `L²(0,π)`-orthogonality relations for the
profile `φ(x) = sin² x` and the modes

* `p_K(x) = sin (K x) sin (2 x)`,
* `c_K(x) = cos (K x) cos (2 x)`.

The main results are

* the derivative formulas `hasDerivAt_φ`, `hasDerivAt_p`, `hasDerivAt_p'`, `hasDerivAt_c`;
* the pointwise bounds `abs_φ_le_one`, `abs_φ'_le_one`, `abs_φ''_le`, `abs_p_le_one`,
  `abs_c_le_one`, `abs_p'_le`, `abs_p''_le`;
* the continuity of `φ`, `φ'`, `φ''` and of the modes and their derivatives;
* the product-to-sum formulas `p_eq`, `c_eq`;
* identity (2.4) in the form `hasDerivAt_coeff_profile`;
* the basic integral `integral_cos_mul_cos` and the orthogonality relations
  `normSq_p`, `normSq_c`, `inner_p_c`, `inner_p_p`, `inner_p_c'`, `inner_c_p`, `inner_c_c`;
* the Pythagoras lemma `normSq_sum_p` for a lacunary finite combination of the modes `p_K`.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ## Elementary derivatives of `x ↦ sin (k x)` and `x ↦ cos (k x)` -/

theorem hasDerivAt_linear (k x : ℝ) : HasDerivAt (fun y : ℝ => k * y) k x := by
  simpa using (hasDerivAt_id x).const_mul k

theorem hasDerivAt_sin_mul (k x : ℝ) :
    HasDerivAt (fun y : ℝ => sin (k * y)) (cos (k * x) * k) x := by
  have h := (Real.hasDerivAt_sin (k * x)).comp x (hasDerivAt_linear k x)
  simpa [Function.comp_def] using h

theorem hasDerivAt_cos_mul (k x : ℝ) :
    HasDerivAt (fun y : ℝ => cos (k * y)) (-sin (k * x) * k) x := by
  have h := (Real.hasDerivAt_cos (k * x)).comp x (hasDerivAt_linear k x)
  simpa [Function.comp_def] using h

theorem continuous_cos_mul (k : ℝ) : Continuous fun x : ℝ => cos (k * x) := by fun_prop

theorem continuous_sin_mul (k : ℝ) : Continuous fun x : ℝ => sin (k * x) := by fun_prop

/-! ## Endpoint values -/

theorem φ_zero : φ 0 = 0 := by simp [φ]

theorem φ_pi : φ π = 0 := by simp [φ]

theorem φ'_zero : φ' 0 = 0 := by simp [φ']

theorem φ'_pi : φ' π = 0 := by simp [φ', Real.sin_two_pi]

theorem p_zero (K : ℕ) : p K 0 = 0 := by simp [p]

theorem p_pi (K : ℕ) : p K π = 0 := by simp [p, Real.sin_two_pi]

theorem p'_zero (K : ℕ) : p' K 0 = 0 := by simp [p']

theorem p'_pi (K : ℕ) : p' K π = 0 := by
  simp [p', Real.sin_two_pi, Real.sin_nat_mul_pi]

/-! ## Derivatives of the profile and of the modes -/

theorem hasDerivAt_φ (x : ℝ) : HasDerivAt φ (φ' x) x := by
  have h := (Real.hasDerivAt_sin x).fun_mul (Real.hasDerivAt_sin x)
  have e : φ' x = cos x * sin x + sin x * cos x := by
    simp only [φ', Real.sin_two_mul]; ring
  have hφ : φ = fun y : ℝ => sin y * sin y := by
    funext y; simp only [φ, pow_two]
  rw [e, hφ]
  exact h

theorem hasDerivAt_φ' (x : ℝ) : HasDerivAt φ' (φ'' x) x := by
  have e : φ'' x = cos (2 * x) * 2 := by simp only [φ'']; ring
  rw [e]
  exact hasDerivAt_sin_mul 2 x

theorem hasDerivAt_p (K : ℕ) (x : ℝ) : HasDerivAt (p K) (p' K x) x := by
  have h := (hasDerivAt_sin_mul (K : ℝ) x).fun_mul (hasDerivAt_sin_mul 2 x)
  have e : p' K x =
      cos ((K : ℝ) * x) * (K : ℝ) * sin (2 * x) + sin ((K : ℝ) * x) * (cos (2 * x) * 2) := by
    simp only [p']; ring
  rw [e]
  exact h

theorem hasDerivAt_p' (K : ℕ) (x : ℝ) : HasDerivAt (p' K) (p'' K x) x := by
  have h1 := ((hasDerivAt_cos_mul (K : ℝ) x).const_mul (K : ℝ)).fun_mul (hasDerivAt_sin_mul 2 x)
  have h2 := ((hasDerivAt_sin_mul (K : ℝ) x).const_mul (2 : ℝ)).fun_mul (hasDerivAt_cos_mul 2 x)
  have h := h1.fun_add h2
  have e : p'' K x =
      ((K : ℝ) * (-sin ((K : ℝ) * x) * (K : ℝ)) * sin (2 * x) +
          (K : ℝ) * cos ((K : ℝ) * x) * (cos (2 * x) * 2)) +
        ((2 : ℝ) * (cos ((K : ℝ) * x) * (K : ℝ)) * cos (2 * x) +
          (2 : ℝ) * sin ((K : ℝ) * x) * (-sin (2 * x) * 2)) := by
    simp only [p'', p, c]; ring
  rw [e]
  exact h

theorem hasDerivAt_c (K : ℕ) (x : ℝ) :
    HasDerivAt (c K) (-(K : ℝ) * sin (K * x) * cos (2 * x) - 2 * cos (K * x) * sin (2 * x)) x := by
  have h := (hasDerivAt_cos_mul (K : ℝ) x).fun_mul (hasDerivAt_cos_mul 2 x)
  have e : -(K : ℝ) * sin ((K : ℝ) * x) * cos (2 * x) - 2 * cos ((K : ℝ) * x) * sin (2 * x) =
      -sin ((K : ℝ) * x) * (K : ℝ) * cos (2 * x) +
        cos ((K : ℝ) * x) * (-sin (2 * x) * 2) := by ring
  rw [e]
  exact h

/-! ## Pointwise bounds -/

theorem abs_φ_le_one (x : ℝ) : |φ x| ≤ 1 := by
  rw [φ, abs_of_nonneg (sq_nonneg _)]
  exact Real.sin_sq_le_one x

theorem abs_φ'_le_one (x : ℝ) : |φ' x| ≤ 1 := Real.abs_sin_le_one _

theorem abs_φ''_le (x : ℝ) : |φ'' x| ≤ 2 := by
  rw [φ'', abs_mul, abs_two]
  linarith [Real.abs_cos_le_one (2 * x)]

private lemma abs_mul_mul_le (r : ℝ) (hr : 0 ≤ r) (u v : ℝ) (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    |r * u * v| ≤ r := by
  have h1 : |r * u * v| = r * (|u| * |v|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hr]; ring
  have h2 : |u| * |v| ≤ 1 := (mul_le_of_le_one_left (abs_nonneg _) hu).trans hv
  calc |r * u * v| = r * (|u| * |v|) := h1
    _ ≤ r * 1 := mul_le_mul_of_nonneg_left h2 hr
    _ = r := mul_one r

theorem abs_p_le_one (K : ℕ) (x : ℝ) : |p K x| ≤ 1 := by
  simp only [p, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)).trans (Real.abs_sin_le_one _)

theorem abs_c_le_one (K : ℕ) (x : ℝ) : |c K x| ≤ 1 := by
  simp only [c, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans (Real.abs_cos_le_one _)

theorem abs_p'_le (K : ℕ) (x : ℝ) : |p' K x| ≤ K + 2 := by
  have h : |p' K x| ≤ |(K : ℝ) * cos ((K : ℝ) * x) * sin (2 * x)| +
      |(2 : ℝ) * sin ((K : ℝ) * x) * cos (2 * x)| := by
    simp only [p']
    exact abs_add_le _ _
  refine h.trans (add_le_add ?_ ?_)
  · exact abs_mul_mul_le _ (Nat.cast_nonneg K) _ _ (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)
  · exact abs_mul_mul_le 2 (by norm_num) _ _ (Real.abs_sin_le_one _) (Real.abs_cos_le_one _)

theorem abs_p''_le (K : ℕ) (x : ℝ) : |p'' K x| ≤ (K : ℝ) ^ 2 + 4 * K + 4 := by
  have h : |p'' K x| ≤ |(-((K : ℝ) ^ 2 + 4)) * p K x| + |4 * (K : ℝ) * c K x| := by
    simp only [p'']
    exact abs_add_le _ _
  refine h.trans ?_
  have h1 : |(-((K : ℝ) ^ 2 + 4)) * p K x| ≤ (K : ℝ) ^ 2 + 4 := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (K : ℝ) ^ 2 + 4)]
    calc ((K : ℝ) ^ 2 + 4) * |p K x| ≤ ((K : ℝ) ^ 2 + 4) * 1 :=
          mul_le_mul_of_nonneg_left (abs_p_le_one K x) (by positivity)
      _ = (K : ℝ) ^ 2 + 4 := mul_one _
  have h2 : |4 * (K : ℝ) * c K x| ≤ 4 * (K : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * (K : ℝ))]
    calc 4 * (K : ℝ) * |c K x| ≤ 4 * (K : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (abs_c_le_one K x) (by positivity)
      _ = 4 * (K : ℝ) := mul_one _
  linarith

/-! ## Continuity -/

theorem continuous_p (K : ℕ) : Continuous (p K) := by
  show Continuous fun x : ℝ => sin ((K : ℝ) * x) * sin (2 * x)
  fun_prop

theorem continuous_c (K : ℕ) : Continuous (c K) := by
  show Continuous fun x : ℝ => cos ((K : ℝ) * x) * cos (2 * x)
  fun_prop

theorem continuous_φ : Continuous φ := by
  show Continuous fun x : ℝ => sin x ^ 2
  fun_prop

theorem continuous_φ' : Continuous φ' := by
  show Continuous fun x : ℝ => sin (2 * x)
  fun_prop

theorem continuous_φ'' : Continuous φ'' := by
  show Continuous fun x : ℝ => 2 * cos (2 * x)
  fun_prop

theorem continuous_p' (K : ℕ) : Continuous (p' K) := by
  show Continuous fun x : ℝ => (K : ℝ) * cos (K * x) * sin (2 * x) + 2 * sin (K * x) * cos (2 * x)
  fun_prop

theorem continuous_p'' (K : ℕ) : Continuous (p'' K) := by
  have h1 : Continuous (p K) := continuous_p K
  have h2 : Continuous (c K) := continuous_c K
  show Continuous fun x : ℝ => -((K : ℝ) ^ 2 + 4) * p K x + 4 * (K : ℝ) * c K x
  fun_prop

/-! ## Product-to-sum formulas -/

/-- Product-to-sum: `p_K = (cos((K-2)x) - cos((K+2)x))/2`. -/
theorem p_eq (K : ℕ) (x : ℝ) :
    p K x = (cos (((K : ℝ) - 2) * x) - cos (((K : ℝ) + 2) * x)) / 2 := by
  have h1 : ((K : ℝ) - 2) * x = (K : ℝ) * x - 2 * x := by ring
  have h2 : ((K : ℝ) + 2) * x = (K : ℝ) * x + 2 * x := by ring
  rw [h1, h2, Real.cos_sub, Real.cos_add]
  simp only [p]
  ring

/-- Product-to-sum: `c_K = (cos((K-2)x) + cos((K+2)x))/2`. -/
theorem c_eq (K : ℕ) (x : ℝ) :
    c K x = (cos (((K : ℝ) - 2) * x) + cos (((K : ℝ) + 2) * x)) / 2 := by
  have h1 : ((K : ℝ) - 2) * x = (K : ℝ) * x - 2 * x := by ring
  have h2 : ((K : ℝ) + 2) * x = (K : ℝ) * x + 2 * x := by ring
  rw [h1, h2, Real.cos_sub, Real.cos_add]
  simp only [c]
  ring

/-- Identity (2.4): `-∂_x( K⁻¹ cos(Kx) φ'(x) ) = p_K(x) - 2 K⁻¹ c_K(x)`. -/
theorem hasDerivAt_coeff_profile (K : ℕ) (hK : 0 < K) (x : ℝ) :
    HasDerivAt (fun x => ((K : ℝ))⁻¹ * cos (K * x) * φ' x)
      (-(p K x - 2 * ((K : ℝ))⁻¹ * c K x)) x := by
  have hK' : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  have h := ((hasDerivAt_cos_mul (K : ℝ) x).const_mul ((K : ℝ))⁻¹).fun_mul (hasDerivAt_sin_mul 2 x)
  have e : -(p K x - 2 * ((K : ℝ))⁻¹ * c K x) =
      ((K : ℝ))⁻¹ * (-sin ((K : ℝ) * x) * (K : ℝ)) * sin (2 * x) +
        ((K : ℝ))⁻¹ * cos ((K : ℝ) * x) * (cos (2 * x) * 2) := by
    have hKK : ((K : ℝ))⁻¹ * (K : ℝ) = 1 := inv_mul_cancel₀ hK'
    simp only [p, c]
    linear_combination (sin ((K : ℝ) * x) * sin (2 * x)) * hKK
  rw [e]
  exact h

/-! ## The basic cosine integrals on `(0,π)` -/

/-- `∫₀^π cos (k x) dx` for an integer `k`. -/
private lemma integral_cos_int_mul (k : ℤ) :
    (∫ x in (0 : ℝ)..π, cos ((k : ℝ) * x)) = if k = 0 then π else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) π,
        HasDerivAt (fun x : ℝ => sin ((k : ℝ) * x) / (k : ℝ)) (cos ((k : ℝ) * y)) y := by
      intro y _
      have h := (hasDerivAt_sin_mul ((k : ℝ)) y).div_const ((k : ℝ))
      simpa [mul_div_assoc, div_self hk'] using h
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((continuous_cos_mul ((k : ℝ))).intervalIntegrable 0 π), ite_eq_right hk]
    simp [Real.sin_int_mul_pi]

/-- `∫₀^π cos(n x) cos(m x) dx` for natural `n, m`. -/
theorem integral_cos_mul_cos (n m : ℕ) :
    ∫ x in (0 : ℝ)..π, cos (n * x) * cos (m * x) =
      if n = m then (if n = 0 then π else π / 2) else 0 := by
  have key : ∀ x : ℝ, cos ((n : ℝ) * x) * cos ((m : ℝ) * x) =
      (cos ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * x) + cos ((((n : ℤ) + (m : ℤ) : ℤ) : ℝ) * x)) / 2 := by
    intro x
    have h1 : ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ)) * x = (n : ℝ) * x - (m : ℝ) * x := by
      push_cast; ring
    have h2 : ((((n : ℤ) + (m : ℤ) : ℤ) : ℝ)) * x = (n : ℝ) * x + (m : ℝ) * x := by
      push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [key]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add
      ((continuous_cos_mul _).intervalIntegrable 0 π)
      ((continuous_cos_mul _).intervalIntegrable 0 π),
    integral_cos_int_mul, integral_cos_int_mul]
  rcases eq_or_ne n m with rfl | hne
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have e1 : ((n : ℤ) - (n : ℤ)) = 0 := by omega
      have e2 : ((n : ℤ) + (n : ℤ)) ≠ 0 := by omega
      rw [ite_eq_left e1, ite_eq_right e2, ite_eq_left rfl, ite_eq_right hn.ne']
      ring
  · have e1 : ((n : ℤ) - (m : ℤ)) ≠ 0 := by omega
    have e2 : ((n : ℤ) + (m : ℤ)) ≠ 0 := by omega
    rw [ite_eq_right e1, ite_eq_right e2, ite_eq_right hne]
    ring

private lemma integral_cos_mul_cos_self {n : ℕ} (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..π, cos ((n : ℝ) * x) * cos ((n : ℝ) * x)) = π / 2 := by
  rw [integral_cos_mul_cos]
  simp [hn]

private lemma integral_cos_mul_cos_of_ne {n m : ℕ} (h : n ≠ m) :
    (∫ x in (0 : ℝ)..π, cos ((n : ℝ) * x) * cos ((m : ℝ) * x)) = 0 := by
  rw [integral_cos_mul_cos]
  simp [h]

/-- The `L²(0,π)` scalar product of two linear combinations of two cosines each. -/
private lemma integral_cos_comb (n₁ n₂ n₃ n₄ : ℕ) (s t A B C E : ℝ)
    (hA : (∫ x in (0 : ℝ)..π, cos ((n₁ : ℝ) * x) * cos ((n₃ : ℝ) * x)) = A)
    (hB : (∫ x in (0 : ℝ)..π, cos ((n₁ : ℝ) * x) * cos ((n₄ : ℝ) * x)) = B)
    (hC : (∫ x in (0 : ℝ)..π, cos ((n₂ : ℝ) * x) * cos ((n₃ : ℝ) * x)) = C)
    (hE : (∫ x in (0 : ℝ)..π, cos ((n₂ : ℝ) * x) * cos ((n₄ : ℝ) * x)) = E) :
    (∫ x in (0 : ℝ)..π, (cos ((n₁ : ℝ) * x) + s * cos ((n₂ : ℝ) * x)) / 2 *
        ((cos ((n₃ : ℝ) * x) + t * cos ((n₄ : ℝ) * x)) / 2))
      = (A + t * B + s * C + s * t * E) / 4 := by
  have hi : ∀ (r : ℝ) (a b : ℕ),
      IntervalIntegrable (fun x : ℝ => r * (cos ((a : ℝ) * x) * cos ((b : ℝ) * x)))
        MeasureTheory.volume 0 π := by
    intro r a b
    apply Continuous.intervalIntegrable
    exact continuous_const.fun_mul ((continuous_cos_mul _).fun_mul (continuous_cos_mul _))
  have key : ∀ x : ℝ,
      (cos ((n₁ : ℝ) * x) + s * cos ((n₂ : ℝ) * x)) / 2 *
          ((cos ((n₃ : ℝ) * x) + t * cos ((n₄ : ℝ) * x)) / 2)
        = 1 / 4 * (cos ((n₁ : ℝ) * x) * cos ((n₃ : ℝ) * x))
          + t / 4 * (cos ((n₁ : ℝ) * x) * cos ((n₄ : ℝ) * x))
          + s / 4 * (cos ((n₂ : ℝ) * x) * cos ((n₃ : ℝ) * x))
          + s * t / 4 * (cos ((n₂ : ℝ) * x) * cos ((n₄ : ℝ) * x)) := by
    intro x; ring
  simp_rw [key]
  rw [intervalIntegral.integral_add (((hi _ _ _).add (hi _ _ _)).add (hi _ _ _)) (hi _ _ _),
    intervalIntegral.integral_add ((hi _ _ _).add (hi _ _ _)) (hi _ _ _),
    intervalIntegral.integral_add (hi _ _ _) (hi _ _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hA, hB, hC, hE]
  ring

/-! ## `L²(0,π)`-norms and orthogonality -/

theorem normSq_eq_inner (g : ℝ → ℝ) : normSq g = inner g g := by
  show (∫ x in (0 : ℝ)..π, g x ^ 2) = ∫ x in (0 : ℝ)..π, g x * g x
  simp_rw [pow_two]

theorem normSq_nonneg (g : ℝ → ℝ) : 0 ≤ normSq g := by
  show 0 ≤ ∫ x in (0 : ℝ)..π, g x ^ 2
  exact intervalIntegral.integral_nonneg Real.pi_pos.le fun u _ => sq_nonneg _

theorem inner_comm (g h : ℝ → ℝ) : inner g h = inner h g := by
  show (∫ x in (0 : ℝ)..π, g x * h x) = ∫ x in (0 : ℝ)..π, h x * g x
  have e : ∀ x : ℝ, g x * h x = h x * g x := fun x => mul_comm _ _
  simp_rw [e]

/-- `p_K` written with natural number frequencies `K-2` and `K+2`. -/
private lemma p_eq_nat {K : ℕ} (hK : 2 ≤ K) (x : ℝ) :
    p K x = (cos (((K - 2 : ℕ) : ℝ) * x) + (-1) * cos (((K + 2 : ℕ) : ℝ) * x)) / 2 := by
  have h1 : ((K - 2 : ℕ) : ℝ) = (K : ℝ) - 2 := by
    have h : ((K - 2 : ℕ) : ℝ) = ((K : ℕ) : ℝ) - ((2 : ℕ) : ℝ) := Nat.cast_sub hK
    simpa using h
  have h2 : ((K + 2 : ℕ) : ℝ) = (K : ℝ) + 2 := by norm_cast
  rw [h1, h2, p_eq]
  ring

/-- `c_K` written with natural number frequencies `K-2` and `K+2`. -/
private lemma c_eq_nat {K : ℕ} (hK : 2 ≤ K) (x : ℝ) :
    c K x = (cos (((K - 2 : ℕ) : ℝ) * x) + (1 : ℝ) * cos (((K + 2 : ℕ) : ℝ) * x)) / 2 := by
  have h1 : ((K - 2 : ℕ) : ℝ) = (K : ℝ) - 2 := by
    have h : ((K - 2 : ℕ) : ℝ) = ((K : ℕ) : ℝ) - ((2 : ℕ) : ℝ) := Nat.cast_sub hK
    simpa using h
  have h2 : ((K + 2 : ℕ) : ℝ) = (K : ℝ) + 2 := by norm_cast
  rw [h1, h2, c_eq]
  ring

theorem normSq_p {K : ℕ} (hK : 2 < K) : normSq (p K) = π / 4 := by
  have hK2 : 2 ≤ K := le_of_lt hK
  show (∫ x in (0 : ℝ)..π, p K x ^ 2) = π / 4
  have key : ∀ x : ℝ, p K x ^ 2 =
      (cos (((K - 2 : ℕ) : ℝ) * x) + (-1) * cos (((K + 2 : ℕ) : ℝ) * x)) / 2 *
        ((cos (((K - 2 : ℕ) : ℝ) * x) + (-1) * cos (((K + 2 : ℕ) : ℝ) * x)) / 2) := by
    intro x; rw [pow_two, p_eq_nat hK2]
  simp_rw [key]
  rw [integral_cos_comb (K - 2) (K + 2) (K - 2) (K + 2) (-1) (-1) (π / 2) 0 0 (π / 2)
    (integral_cos_mul_cos_self (by omega)) (integral_cos_mul_cos_of_ne (by omega))
    (integral_cos_mul_cos_of_ne (by omega)) (integral_cos_mul_cos_self (by omega))]
  ring

theorem normSq_c {K : ℕ} (hK : 2 < K) : normSq (c K) = π / 4 := by
  have hK2 : 2 ≤ K := le_of_lt hK
  show (∫ x in (0 : ℝ)..π, c K x ^ 2) = π / 4
  have key : ∀ x : ℝ, c K x ^ 2 =
      (cos (((K - 2 : ℕ) : ℝ) * x) + (1 : ℝ) * cos (((K + 2 : ℕ) : ℝ) * x)) / 2 *
        ((cos (((K - 2 : ℕ) : ℝ) * x) + (1 : ℝ) * cos (((K + 2 : ℕ) : ℝ) * x)) / 2) := by
    intro x; rw [pow_two, c_eq_nat hK2]
  simp_rw [key]
  rw [integral_cos_comb (K - 2) (K + 2) (K - 2) (K + 2) 1 1 (π / 2) 0 0 (π / 2)
    (integral_cos_mul_cos_self (by omega)) (integral_cos_mul_cos_of_ne (by omega))
    (integral_cos_mul_cos_of_ne (by omega)) (integral_cos_mul_cos_self (by omega))]
  ring

theorem inner_p_c {K : ℕ} (hK : 2 < K) : inner (p K) (c K) = 0 := by
  have hK2 : 2 ≤ K := le_of_lt hK
  show (∫ x in (0 : ℝ)..π, p K x * c K x) = 0
  simp_rw [p_eq_nat hK2, c_eq_nat hK2]
  rw [integral_cos_comb (K - 2) (K + 2) (K - 2) (K + 2) (-1) 1 (π / 2) 0 0 (π / 2)
    (integral_cos_mul_cos_self (by omega)) (integral_cos_mul_cos_of_ne (by omega))
    (integral_cos_mul_cos_of_ne (by omega)) (integral_cos_mul_cos_self (by omega))]
  ring

/-- Orthogonality of different frequency pairs (`L ≥ K+5` suffices). -/
theorem inner_p_p {K L : ℕ} (hK : 2 < K) (hKL : K + 4 < L) : inner (p K) (p L) = 0 := by
  have hK2 : 2 ≤ K := le_of_lt hK
  have hL2 : 2 ≤ L := by omega
  show (∫ x in (0 : ℝ)..π, p K x * p L x) = 0
  simp_rw [p_eq_nat hK2, p_eq_nat hL2]
  rw [integral_cos_comb (K - 2) (K + 2) (L - 2) (L + 2) (-1) (-1) 0 0 0 0
    (integral_cos_mul_cos_of_ne (by omega)) (integral_cos_mul_cos_of_ne (by omega))
    (integral_cos_mul_cos_of_ne (by omega)) (integral_cos_mul_cos_of_ne (by omega))]
  ring

theorem inner_p_c' {K L : ℕ} (hK : 2 < K) (hKL : K + 4 < L) : inner (p K) (c L) = 0 := by
  have hK2 : 2 ≤ K := le_of_lt hK
  have hL2 : 2 ≤ L := by omega
  show (∫ x in (0 : ℝ)..π, p K x * c L x) = 0
  simp_rw [p_eq_nat hK2, c_eq_nat hL2]
  rw [integral_cos_comb (K - 2) (K + 2) (L - 2) (L + 2) (-1) 1 0 0 0 0
    (integral_cos_mul_cos_of_ne (by omega)) (integral_cos_mul_cos_of_ne (by omega))
    (integral_cos_mul_cos_of_ne (by omega)) (integral_cos_mul_cos_of_ne (by omega))]
  ring

theorem inner_c_p {K L : ℕ} (hK : 2 < K) (hKL : K + 4 < L) : inner (c K) (p L) = 0 := by
  have hK2 : 2 ≤ K := le_of_lt hK
  have hL2 : 2 ≤ L := by omega
  show (∫ x in (0 : ℝ)..π, c K x * p L x) = 0
  simp_rw [c_eq_nat hK2, p_eq_nat hL2]
  rw [integral_cos_comb (K - 2) (K + 2) (L - 2) (L + 2) 1 (-1) 0 0 0 0
    (integral_cos_mul_cos_of_ne (by omega)) (integral_cos_mul_cos_of_ne (by omega))
    (integral_cos_mul_cos_of_ne (by omega)) (integral_cos_mul_cos_of_ne (by omega))]
  ring

theorem inner_c_c {K L : ℕ} (hK : 2 < K) (hKL : K + 4 < L) : inner (c K) (c L) = 0 := by
  have hK2 : 2 ≤ K := le_of_lt hK
  have hL2 : 2 ≤ L := by omega
  show (∫ x in (0 : ℝ)..π, c K x * c L x) = 0
  simp_rw [c_eq_nat hK2, c_eq_nat hL2]
  rw [integral_cos_comb (K - 2) (K + 2) (L - 2) (L + 2) 1 1 0 0 0 0
    (integral_cos_mul_cos_of_ne (by omega)) (integral_cos_mul_cos_of_ne (by omega))
    (integral_cos_mul_cos_of_ne (by omega)) (integral_cos_mul_cos_of_ne (by omega))]
  ring

/-- Pythagoras for a finite combination of separated modes. -/
theorem normSq_sum_p (s : Finset ℕ) (Kf : ℕ → ℕ) (a : ℕ → ℝ) (hK : ∀ m ∈ s, 2 < Kf m)
    (hsep : ∀ m ∈ s, ∀ m' ∈ s, m < m' → Kf m + 4 < Kf m') :
    normSq (fun x => ∑ m ∈ s, a m * p (Kf m) x) = π / 4 * ∑ m ∈ s, (a m) ^ 2 := by
  have hcont : ∀ (m m' : ℕ) (r : ℝ),
      IntervalIntegrable (fun x : ℝ => r * (p (Kf m) x * p (Kf m') x))
        MeasureTheory.volume 0 π := by
    intro m m' r
    apply Continuous.intervalIntegrable
    exact continuous_const.fun_mul ((continuous_p _).fun_mul (continuous_p _))
  have horth : ∀ m ∈ s, ∀ m' ∈ s, m ≠ m' →
      (∫ x in (0 : ℝ)..π, p (Kf m) x * p (Kf m') x) = 0 := by
    intro m hm m' hm' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact inner_p_p (hK m hm) (hsep m hm m' hm' h)
    · have h2 := inner_p_p (hK m' hm') (hsep m' hm' m hm h)
      rw [inner_comm] at h2
      exact h2
  have hdiag : ∀ m ∈ s, (∫ x in (0 : ℝ)..π, p (Kf m) x * p (Kf m) x) = π / 4 := by
    intro m hm
    have h2 := normSq_p (hK m hm)
    rw [normSq_eq_inner] at h2
    exact h2
  show (∫ x in (0 : ℝ)..π, (∑ m ∈ s, a m * p (Kf m) x) ^ 2) = π / 4 * ∑ m ∈ s, (a m) ^ 2
  have key : ∀ x : ℝ, (∑ m ∈ s, a m * p (Kf m) x) ^ 2
      = ∑ m ∈ s, ∑ m' ∈ s, (a m * a m') * (p (Kf m) x * p (Kf m') x) := by
    intro x
    rw [pow_two, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by ring
  simp_rw [key]
  have hsum_int : ∀ m ∈ s, IntervalIntegrable
      (fun x : ℝ => ∑ m' ∈ s, (a m * a m') * (p (Kf m) x * p (Kf m') x))
      MeasureTheory.volume 0 π := by
    intro m _
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum s fun m' _ =>
      continuous_const.fun_mul ((continuous_p _).fun_mul (continuous_p _))
  rw [intervalIntegral.integral_finsetSum hsum_int]
  have hterm : ∀ m ∈ s,
      (∫ x in (0 : ℝ)..π, ∑ m' ∈ s, (a m * a m') * (p (Kf m) x * p (Kf m') x))
        = π / 4 * (a m) ^ 2 := by
    intro m hm
    have hint : ∀ m' ∈ s, IntervalIntegrable
        (fun x : ℝ => (a m * a m') * (p (Kf m) x * p (Kf m') x)) MeasureTheory.volume 0 π :=
      fun m' _ => hcont m m' (a m * a m')
    rw [intervalIntegral.integral_finsetSum hint]
    have hsingle : (∑ m' ∈ s, ∫ x in (0 : ℝ)..π, (a m * a m') * (p (Kf m) x * p (Kf m') x))
        = ∫ x in (0 : ℝ)..π, (a m * a m) * (p (Kf m) x * p (Kf m) x) := by
      refine Finset.sum_eq_single m ?_ ?_
      · intro m' hm' hne
        rw [intervalIntegral.integral_const_mul, horth m hm m' hm' (Ne.symm hne), mul_zero]
      · intro hns
        exact absurd hm hns
    rw [hsingle, intervalIntegral.integral_const_mul, hdiag m hm]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]

end LionsC12

end
