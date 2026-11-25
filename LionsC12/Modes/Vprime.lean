module

public import LionsC12.Construction.Defs
public import LionsC12.Modes.Trig
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# The `V'`-estimate for the oscillatory modes (Lemma 2.1 of the paper)

This file proves the dual-norm bound `‖p_K‖_{V'} ≤ 3 K⁻¹` used in Lemma 2.1 of

> L. Niebel, *Lions' Maximal Regularity Problem for Divergence-Form Differential
> Operators: Failure at the ½-Hölder Endpoint* (2026).

The argument is: `p_K` has the explicit antiderivative

* `P_K(x) = ½ (sin((K-2)x)/(K-2) - sin((K+2)x)/(K+2))`,

which vanishes at `x = 0`; integrating by parts against a test function `w ∈ V`
(here: `C¹` with `w(0) = w(π) = 0`) gives `⟨p_K, w⟩ = -⟨P_K, w'⟩`, and
Cauchy–Schwarz together with `‖P_K‖²_{L²} = (π/8)((K-2)^{-2} + (K+2)^{-2}) ≤ 9 K⁻²`
finishes the proof.

Along the way we prove the sine orthogonality relations on `(0,π)`
(`integral_sin_mul_sin`) and Cauchy–Schwarz for the `L²(0,π)` pairing
(`abs_inner_le`).
-/


@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ## The sine orthogonality relations on `(0,π)` -/

/-- `∫₀^π cos (n x) dx` for a natural number `n`. -/
theorem integral_cos_nat_mul (n : ℕ) :
    (∫ x in (0 : ℝ)..π, cos ((n : ℝ) * x)) = if n = 0 then π else 0 := by
  have h := integral_cos_mul_cos n 0
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one] at h
  rw [h]
  by_cases hn : n = 0 <;> simp [hn]

/-- `∫₀^π sin(n x) sin(m x) dx` for natural `n, m`. -/
theorem integral_sin_mul_sin (n m : ℕ) :
    (∫ x in (0 : ℝ)..π, sin ((n : ℝ) * x) * sin ((m : ℝ) * x)) =
      if n = m then (if n = 0 then 0 else π / 2) else 0 := by
  have key : ∀ x : ℝ, sin ((n : ℝ) * x) * sin ((m : ℝ) * x) =
      cos ((n : ℝ) * x) * cos ((m : ℝ) * x) - cos (((n + m : ℕ) : ℝ) * x) := by
    intro x
    have h : (((n + m : ℕ) : ℝ)) * x = (n : ℝ) * x + (m : ℝ) * x := by push_cast; ring
    rw [h, Real.cos_add]
    ring
  simp_rw [key]
  rw [intervalIntegral.integral_sub
      (((continuous_cos_mul _).fun_mul (continuous_cos_mul _)).intervalIntegrable 0 π)
      ((continuous_cos_mul _).intervalIntegrable 0 π),
    integral_cos_mul_cos, integral_cos_nat_mul]
  rcases eq_or_ne n m with rfl | hne
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have h1 : n ≠ 0 := hn.ne'
      simp [h1]
  · simp [hne]
    omega

private lemma integral_sin_sq_nat {n : ℕ} (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..π, sin ((n : ℝ) * x) * sin ((n : ℝ) * x)) = π / 2 := by
  rw [integral_sin_mul_sin]; simp [hn]

private lemma integral_sin_mul_sin_of_ne {n m : ℕ} (h : n ≠ m) :
    (∫ x in (0 : ℝ)..π, sin ((n : ℝ) * x) * sin ((m : ℝ) * x)) = 0 := by
  rw [integral_sin_mul_sin]; simp [h]

/-- Linearity of the integral for a quadratic combination of two sine modes. -/
private lemma integral_sin_comb (n m : ℕ) (A B C : ℝ) :
    (∫ x in (0 : ℝ)..π, A * (sin ((n : ℝ) * x) * sin ((n : ℝ) * x))
        + B * (sin ((n : ℝ) * x) * sin ((m : ℝ) * x))
        + C * (sin ((m : ℝ) * x) * sin ((m : ℝ) * x)))
      = A * (∫ x in (0 : ℝ)..π, sin ((n : ℝ) * x) * sin ((n : ℝ) * x))
        + B * (∫ x in (0 : ℝ)..π, sin ((n : ℝ) * x) * sin ((m : ℝ) * x))
        + C * (∫ x in (0 : ℝ)..π, sin ((m : ℝ) * x) * sin ((m : ℝ) * x)) := by
  have hi : ∀ (a b : ℕ) (r : ℝ),
      IntervalIntegrable (fun x : ℝ => r * (sin ((a : ℝ) * x) * sin ((b : ℝ) * x)))
        MeasureTheory.volume 0 π := by
    intro a b r
    exact (continuous_const.fun_mul
      ((continuous_sin_mul _).fun_mul (continuous_sin_mul _))).intervalIntegrable 0 π
  rw [intervalIntegral.integral_add ((hi _ _ _).add (hi _ _ _)) (hi _ _ _),
    intervalIntegral.integral_add (hi _ _ _) (hi _ _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-! ## The antiderivative `P_K` of `p_K` -/

/-- The antiderivative `P_K` of `p_K`: `P_K = ½ (sin((K-2)x)/(K-2) - sin((K+2)x)/(K+2))`. -/
def P (K : ℕ) (x : ℝ) : ℝ :=
  (sin (((K : ℝ) - 2) * x) / ((K : ℝ) - 2) - sin (((K : ℝ) + 2) * x) / ((K : ℝ) + 2)) / 2

theorem P_zero (K : ℕ) : P K 0 = 0 := by simp [P]

theorem continuous_P (K : ℕ) : Continuous (P K) :=
  (((continuous_sin_mul _).div_const _).sub ((continuous_sin_mul _).div_const _)).div_const 2

theorem hasDerivAt_P {K : ℕ} (hK : 2 < K) (x : ℝ) : HasDerivAt (P K) (p K x) x := by
  have hKR : (2 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hm : ((K : ℝ) - 2) ≠ 0 := ne_of_gt (by linarith)
  have hp : ((K : ℝ) + 2) ≠ 0 := ne_of_gt (by linarith)
  have h := (((hasDerivAt_sin_mul ((K : ℝ) - 2) x).div_const ((K : ℝ) - 2)).sub
    ((hasDerivAt_sin_mul ((K : ℝ) + 2) x).div_const ((K : ℝ) + 2))).div_const 2
  have e : (cos (((K : ℝ) - 2) * x) * ((K : ℝ) - 2) / ((K : ℝ) - 2)
      - cos (((K : ℝ) + 2) * x) * ((K : ℝ) + 2) / ((K : ℝ) + 2)) / 2 = p K x := by
    rw [p_eq, mul_div_assoc, mul_div_assoc, div_self hm, div_self hp]
    ring
  rw [← e]
  exact h

theorem normSq_P {K : ℕ} (hK : 2 < K) :
    normSq (P K) = π / 8 * (1 / ((K : ℝ) - 2) ^ 2 + 1 / ((K : ℝ) + 2) ^ 2) := by
  have hKR : (2 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hm : ((K : ℝ) - 2) ≠ 0 := ne_of_gt (by linarith)
  have hp : ((K : ℝ) + 2) ≠ 0 := ne_of_gt (by linarith)
  have hn : (((K - 2 : ℕ)) : ℝ) = (K : ℝ) - 2 := by
    have h : ((K - 2 : ℕ) : ℝ) = ((K : ℕ) : ℝ) - ((2 : ℕ) : ℝ) := Nat.cast_sub hK.le
    simpa using h
  have hq : (((K + 2 : ℕ)) : ℝ) = (K : ℝ) + 2 := by push_cast; ring
  have h1 : (K - 2 : ℕ) ≠ 0 := by omega
  have h2 : (K + 2 : ℕ) ≠ 0 := by omega
  have h3 : (K - 2 : ℕ) ≠ (K + 2 : ℕ) := by omega
  have alg : ∀ s t : ℝ, ((s / ((K : ℝ) - 2) - t / ((K : ℝ) + 2)) / 2) ^ 2
      = 1 / (4 * ((K : ℝ) - 2) ^ 2) * (s * s)
        + (-(1 / (2 * ((K : ℝ) - 2) * ((K : ℝ) + 2)))) * (s * t)
        + 1 / (4 * ((K : ℝ) + 2) ^ 2) * (t * t) := by
    intro s t; field_simp; ring
  show (∫ x in (0 : ℝ)..π, P K x ^ 2) = _
  have key : ∀ x : ℝ, P K x ^ 2 =
      1 / (4 * ((K : ℝ) - 2) ^ 2) * (sin (((K - 2 : ℕ) : ℝ) * x) * sin (((K - 2 : ℕ) : ℝ) * x))
      + (-(1 / (2 * ((K : ℝ) - 2) * ((K : ℝ) + 2))))
          * (sin (((K - 2 : ℕ) : ℝ) * x) * sin (((K + 2 : ℕ) : ℝ) * x))
      + 1 / (4 * ((K : ℝ) + 2) ^ 2)
          * (sin (((K + 2 : ℕ) : ℝ) * x) * sin (((K + 2 : ℕ) : ℝ) * x)) := by
    intro x
    rw [hn, hq]
    exact alg _ _
  simp_rw [key]
  rw [integral_sin_comb, integral_sin_sq_nat h1, integral_sin_mul_sin_of_ne h3,
    integral_sin_sq_nat h2]
  field_simp
  ring

theorem normSq_P_le {K : ℕ} (hK : 2 < K) : normSq (P K) ≤ 9 / (K : ℝ) ^ 2 := by
  rw [normSq_P hK]
  have h3 : (3 : ℕ) ≤ K := hK
  have hKR : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast h3
  have ha : (0 : ℝ) < (K : ℝ) - 2 := by linarith
  have hb : (0 : ℝ) < (K : ℝ) + 2 := by linarith
  have hk : (0 : ℝ) < (K : ℝ) := by linarith
  have hu : (0 : ℝ) < 1 / (K : ℝ) ^ 2 := by positivity
  have e1 : 1 / ((K : ℝ) - 2) ^ 2 ≤ 9 * (1 / (K : ℝ) ^ 2) := by
    rw [show (9 : ℝ) * (1 / (K : ℝ) ^ 2) = 9 / (K : ℝ) ^ 2 by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (K : ℝ) - 3)
      (by linarith : (0:ℝ) ≤ 8 * (K : ℝ) - 12)]
  have e2 : 1 / ((K : ℝ) + 2) ^ 2 ≤ 1 / (K : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hπ : π * (1 / (K : ℝ) ^ 2) ≤ 4 * (1 / (K : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right Real.pi_le_four hu.le
  have hsum : 1 / ((K : ℝ) - 2) ^ 2 + 1 / ((K : ℝ) + 2) ^ 2 ≤ 10 * (1 / (K : ℝ) ^ 2) := by
    linarith
  have hstep : π / 8 * (1 / ((K : ℝ) - 2) ^ 2 + 1 / ((K : ℝ) + 2) ^ 2)
      ≤ π / 8 * (10 * (1 / (K : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have hfin : π / 8 * (10 * (1 / (K : ℝ) ^ 2)) ≤ 9 / (K : ℝ) ^ 2 := by
    rw [show (9 : ℝ) / (K : ℝ) ^ 2 = 9 * (1 / (K : ℝ) ^ 2) by ring]
    nlinarith
  linarith

/-! ## Cauchy–Schwarz for the `L²(0,π)` pairing -/

/-- Cauchy–Schwarz for the real `L²(0,π)` pairing of continuous functions. -/
theorem abs_inner_le (g h : ℝ → ℝ) (hg : Continuous g) (hh : Continuous h) :
    |inner g h| ≤ Real.sqrt (normSq g) * Real.sqrt (normSq h) := by
  have iA : IntervalIntegrable (fun x : ℝ => g x ^ 2) MeasureTheory.volume 0 π :=
    (by fun_prop : Continuous fun x : ℝ => g x ^ 2).intervalIntegrable 0 π
  have expand : ∀ lam : ℝ,
      (∫ x in (0 : ℝ)..π, (g x - lam * h x) ^ 2)
        = normSq g + (-(2 * lam)) * inner g h + (lam * lam) * normSq h := by
    intro lam
    have iB : IntervalIntegrable (fun x : ℝ => (-(2 * lam)) * (g x * h x))
        MeasureTheory.volume 0 π :=
      (by fun_prop : Continuous fun x : ℝ => (-(2 * lam)) * (g x * h x)).intervalIntegrable 0 π
    have iC : IntervalIntegrable (fun x : ℝ => (lam * lam) * (h x ^ 2))
        MeasureTheory.volume 0 π :=
      (by fun_prop : Continuous fun x : ℝ => (lam * lam) * (h x ^ 2)).intervalIntegrable 0 π
    have e : ∀ x : ℝ, (g x - lam * h x) ^ 2
        = g x ^ 2 + (-(2 * lam)) * (g x * h x) + (lam * lam) * (h x ^ 2) := by
      intro x; ring
    simp_rw [e]
    rw [intervalIntegral.integral_add (iA.add iB) iC,
      intervalIntegral.integral_add iA iB,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rfl
  have key : ∀ lam : ℝ, 0 ≤ normSq h * (lam * lam) + (-2 * inner g h) * lam + normSq g := by
    intro lam
    have h0 : (0 : ℝ) ≤ ∫ x in (0 : ℝ)..π, (g x - lam * h x) ^ 2 :=
      intervalIntegral.integral_nonneg Real.pi_pos.le fun _ _ => sq_nonneg _
    rw [expand lam] at h0
    nlinarith [h0]
  have hd := discrim_le_zero key
  rw [discrim] at hd
  have hsq : (inner g h) ^ 2 ≤ normSq g * normSq h := by nlinarith [hd]
  calc |inner g h| = Real.sqrt ((inner g h) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (normSq g * normSq h) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (normSq g) * Real.sqrt (normSq h) := Real.sqrt_mul (normSq_nonneg g) _

/-! ## The `V'`-bound -/

/-- `‖p_K‖_{V'} ≤ 3 K⁻¹`: for every `w ∈ V` (here: `C¹` with `w(0) = w(π) = 0`),
`|⟨p_K, w⟩| ≤ 3 K⁻¹ ‖w'‖_{L²}`. -/
theorem abs_inner_p_le {K : ℕ} (hK : 2 < K) (w w' : ℝ → ℝ) (hw : ∀ x, HasDerivAt w (w' x) x)
    (hw' : Continuous w') (h0 : w 0 = 0) (hπ : w π = 0) :
    |inner (p K) w| ≤ 3 / (K : ℝ) * Real.sqrt (normSq w') := by
  have hk : (0 : ℝ) < (K : ℝ) := by
    have : (2 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    linarith
  have hcw : Continuous w :=
    continuous_iff_continuousAt.mpr fun x => (hw x).continuousAt
  have hIBP : inner (P K) w' = -inner (p K) w := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := P K) (u' := p K) (v := w) (v' := w') (a := (0 : ℝ)) (b := π)
      (continuous_P K).continuousOn hcw.continuousOn
      (fun x _ => hasDerivAt_P hK x) (fun x _ => hw x)
      ((continuous_p K).intervalIntegrable 0 π) (hw'.intervalIntegrable 0 π)
    show (∫ x in (0 : ℝ)..π, P K x * w' x) = -∫ x in (0 : ℝ)..π, p K x * w x
    rw [h, hπ, h0]
    ring
  have habs : |inner (p K) w| = |inner (P K) w'| := by
    rw [hIBP, abs_neg]
  have hsqrtP : Real.sqrt (normSq (P K)) ≤ 3 / (K : ℝ) := by
    have h9 : Real.sqrt (9 / (K : ℝ) ^ 2) = 3 / (K : ℝ) := by
      rw [show (9 : ℝ) / (K : ℝ) ^ 2 = (3 / (K : ℝ)) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    calc Real.sqrt (normSq (P K)) ≤ Real.sqrt (9 / (K : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (normSq_P_le hK)
      _ = 3 / (K : ℝ) := h9
  calc |inner (p K) w| = |inner (P K) w'| := habs
    _ ≤ Real.sqrt (normSq (P K)) * Real.sqrt (normSq w') :=
        abs_inner_le _ _ (continuous_P K) hw'
    _ ≤ 3 / (K : ℝ) * Real.sqrt (normSq w') :=
        mul_le_mul_of_nonneg_right hsqrtP (Real.sqrt_nonneg _)

end LionsC12

end
