module

public import LionsC12.Interval.FrozenDomain

/-!
# Lemma 2.1 in the paper's spaces

The oscillatory modes `p_K = sin(Kx) sin(2x)` and `c_K = cos(Kx) cos(2x)`, `K > 2`, as elements of
`H = L²((0,π);ℂ)`, `V = H¹₀((0,π);ℂ)` and `V'`:

* `‖p_K‖²_H = ‖c_K‖²_H = π/4` and `‖∂ₓp_K‖²_H = (π/4)(K² + 4)` (`normSq_p'`);
* `‖p_K‖_{V'} ≤ 6/K` in the anti-dual norm (`norm_p_Hm1_le`; the paper: `≤ C K⁻¹`);
* `A_{0,H}p_K = (K² + 4)p_K - 4K c_K` (`isRealisation_pV`);
* for `L ≥ 16K` the spans of `{p_K, c_K}` and `{p_L, c_L}` are orthogonal in `H`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped InnerProductSpace ComplexConjugate

theorem p'_eq (K : ℕ) (hK : 2 ≤ K) (x : ℝ) :
    p' K x = (1 / 2) * (-(((K - 2 : ℕ) : ℝ)) * sin (((K - 2 : ℕ) : ℝ) * x)
      + ((K + 2 : ℕ) : ℝ) * sin (((K + 2 : ℕ) : ℝ) * x)) := by
  have h1 : (((K - 2 : ℕ) : ℝ)) = (K : ℝ) - 2 := by
    rw [Nat.cast_sub hK]; norm_num
  have h2 : (((K + 2 : ℕ) : ℝ)) = (K : ℝ) + 2 := by push_cast; ring
  rw [h1, h2, p', show ((K : ℝ) - 2) * x = K * x - 2 * x by ring,
    show ((K : ℝ) + 2) * x = K * x + 2 * x by ring, sin_sub, sin_add]
  ring

/-- `‖∂ₓp_K‖²_{L²(0,π)} = (π/4)(K² + 4)`. -/
theorem normSq_p' {K : ℕ} (hK : 2 < K) : normSq (p' K) = π / 4 * ((K : ℝ) ^ 2 + 4) := by
  set n := K - 2
  set m := K + 2
  have hnm : n ≠ m := by omega
  have hn0 : n ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  have hc : Continuous fun x : ℝ => sin ((n : ℝ) * x) := continuous_sin_mul _
  have hc' : Continuous fun x : ℝ => sin ((m : ℝ) * x) := continuous_sin_mul _
  have e : (fun x => p' K x ^ 2) = fun x => (1 / 4) * ((n : ℝ) ^ 2 * (sin ((n : ℝ) * x) *
      sin ((n : ℝ) * x)) + (m : ℝ) ^ 2 * (sin ((m : ℝ) * x) * sin ((m : ℝ) * x))
      - 2 * (n : ℝ) * (m : ℝ) * (sin ((n : ℝ) * x) * sin ((m : ℝ) * x))) := by
    funext x; rw [p'_eq K hK.le]; ring
  have i1 : IntervalIntegrable (fun x : ℝ => (n : ℝ) ^ 2 * (sin ((n : ℝ) * x) *
      sin ((n : ℝ) * x))) MeasureTheory.volume 0 π :=
    (continuous_const.mul (hc.mul hc)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => (m : ℝ) ^ 2 * (sin ((m : ℝ) * x) *
      sin ((m : ℝ) * x))) MeasureTheory.volume 0 π :=
    (continuous_const.mul (hc'.mul hc')).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun x : ℝ => 2 * (n : ℝ) * (m : ℝ) * (sin ((n : ℝ) * x) *
      sin ((m : ℝ) * x))) MeasureTheory.volume 0 π :=
    (continuous_const.mul (hc.mul hc')).intervalIntegrable _ _
  rw [normSq, e, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (i1.add i2) i3,
    intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sin_mul_sin, integral_sin_mul_sin, integral_sin_mul_sin]
  simp only [hnm, hn0, hm0, ite_true, ite_false]
  have h1 : (n : ℝ) = (K : ℝ) - 2 := by rw [Nat.cast_sub hK.le]; norm_num
  have h2 : (m : ℝ) = (K : ℝ) + 2 := by push_cast [m]; ring
  rw [h1, h2]
  ring

theorem isC1Vanish_p (K : ℕ) : IsC1Vanish (p K) (p' K) where
  hasDerivAt := hasDerivAt_p K
  cont' := continuous_p' K
  zero_left := p_zero K
  zero_right := p_pi K
  zero_left' := p'_zero K
  zero_right' := p'_pi K

/-- The mode `p_K ∈ V`. -/
def pV (K : ℕ) : H10 Iπ := ofC1Z (isC1Vanish_p K)

theorem val_pV (K : ℕ) : val Iπ (pV K) = toL2c (p K) (continuous_p K) := val_ofC1Z _

theorem dx_pV (K : ℕ) : dx Iπ (pV K) = toL2c (p' K) (continuous_p' K) := dx_ofC1Z _

/-- `A_{0,H} p_K = (K² + 4) p_K - 4K c_K`. -/
theorem isRealisation_pV (K : ℕ) :
    IsRealisation one 0 (pV K) (toL2c (fun x => -p'' K x) (continuous_p'' K).neg) := by
  intro w
  have hG : ∀ x, HasDerivAt (fun x => (p' K x : ℂ)) (p'' K x : ℂ) x :=
    fun x => (hasDerivAt_p' K x).ofReal_comp
  have key := inner_dx_eq hG (continuous_cplx (continuous_p'' K))
    (memLp_Ioo_of_continuous (a := 0) (b := π) (continuous_cplx (continuous_p' K)))
    (memLp_Ioo_of_continuous (a := 0) (b := π) (continuous_cplx (continuous_p'' K))) w
  rw [formH_one_eq, dx_pV]
  change ⟪dx Iπ w, toL2c (p' K) _⟫_ℂ = ⟪val Iπ w, _⟫_ℂ
  have e : toL2c (fun x => -p'' K x) (continuous_p'' K).neg
      = -toL2c (p'' K) (continuous_p'' K) := by
    apply Lp.ext
    filter_upwards [coe_toL2c (g := fun x => -p'' K x) (continuous_p'' K).neg,
      coe_toL2c (continuous_p'' K), Lp.coeFn_neg (toL2c (p'' K) (continuous_p'' K))]
      with x h1 h2 h3
    rw [h1, h3, Pi.neg_apply, h2, Complex.ofReal_neg]
  rw [e, inner_neg_right]
  exact key

theorem neg_p''_eq (K : ℕ) (x : ℝ) : -p'' K x = ((K : ℝ) ^ 2 + 4) * p K x - 4 * K * c K x := by
  simp only [p'']; ring

/-- `‖p_K‖_{V'} ≤ 6/K`. -/
theorem norm_p_Hm1_le {K : ℕ} (hK : 2 < K) :
    ‖ofL2 Iπ (toL2c (p K) (continuous_p K))‖ ≤ 6 / (K : ℝ) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have := norm_ofL2_toL2c_le (continuous_p K) (C := 3 / K) (by positivity)
    (fun w w' hw => abs_inner_p_le hK w w' hw.hasDerivAt hw.cont' hw.zero_left hw.zero_right)
  calc _ ≤ 2 * (3 / (K : ℝ)) := this
    _ = 6 / (K : ℝ) := by ring

/-- **Lemma 2.1** in the paper's spaces. -/
theorem lemma_2_1 {K : ℕ} (hK : 2 < K) :
    ‖toL2c (p K) (continuous_p K)‖ ^ 2 = π / 4 ∧
    ‖toL2c (c K) (continuous_c K)‖ ^ 2 = π / 4 ∧
    ‖dx Iπ (pV K)‖ ^ 2 = π / 4 * ((K : ℝ) ^ 2 + 4) ∧
    ‖ofL2 Iπ (toL2c (p K) (continuous_p K))‖ ≤ 6 / (K : ℝ) ∧
    IsRealisation one 0 (pV K) (toL2c (fun x => ((K : ℝ) ^ 2 + 4) * p K x - 4 * K * c K x)
      ((continuous_const.mul (continuous_p K)).sub (continuous_const.mul (continuous_c K)))) ∧
    ∀ L : ℕ, 16 * K ≤ L →
      ⟪toL2c (p K) (continuous_p K), toL2c (p L) (continuous_p L)⟫_ℂ = 0 ∧
      ⟪toL2c (p K) (continuous_p K), toL2c (c L) (continuous_c L)⟫_ℂ = 0 ∧
      ⟪toL2c (c K) (continuous_c K), toL2c (p L) (continuous_p L)⟫_ℂ = 0 ∧
      ⟪toL2c (c K) (continuous_c K), toL2c (c L) (continuous_c L)⟫_ℂ = 0 := by
  refine ⟨by rw [norm_toL2c_sq, normSq_p hK], by rw [norm_toL2c_sq, normSq_c hK],
    by rw [dx_pV, norm_toL2c_sq, normSq_p' hK], norm_p_Hm1_le hK, ?_, fun L hL => ?_⟩
  · have h := isRealisation_pV K
    rwa [toL2c_congr _ _ fun x _ => neg_p''_eq K x] at h
  · have hKL : K + 4 < L := by omega
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [inner_toL2c]
    · rw [inner_p_p hK hKL]; simp
    · rw [inner_p_c' hK hKL]; simp
    · rw [inner_c_p hK hKL]; simp
    · rw [inner_c_c hK hKL]; simp

end LionsC12
