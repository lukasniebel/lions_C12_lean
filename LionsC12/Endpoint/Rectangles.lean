module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The Gagliardo `H^{1/2}` energy of a single oscillation

For a frequency `A > 0` (in the application `A = K_{j,m}²`) and an interval `(p,q)` of length
`L` with `A L ≥ 8π`,

`∫∫_{(p,q)²} (sin(A(t−τ)) − sin(A(s−τ)))² / (t − s)² ds dt ≥ A L / (36π)`

(`lintegral_sin_sub_sq_ge`).  The integrals are lower Lebesgue integrals in `ℝ≥0∞`, so no
measurability or integrability is needed.

The proof uses rectangles: for every full period `[τ + 2πn/A, τ + 2π(n+1)/A] ⊆ (p,q)` let
`T_n` (`S_n`) be the set of times where the phase `A(t−τ) − 2πn` lies in `[π/4, 3π/4]`
(`[5π/4, 7π/4]`).  On `T_n × S_n` the sine difference is `≥ 1` and `|t − s| ≤ 3π/(2A)`, so the
integrand is `≥ 4A²/(9π²)`; the rectangle has area `(π/(2A))²`, hence contributes `≥ 1/9`.
There are at least `A L/(2π) − 2 ≥ A L/(4π)` full periods.  (The paper restricts instead to
`t − s ∈ [π/(2K²), 3π/(2K²)]` and averages `cos²` in `t`; the constant is immaterial.)
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Real
open scoped ENNReal

/-- `sin y ≥ 1/2` for `y ∈ [π/4, 3π/4]` (Jordan's inequality). -/
theorem half_le_sin_of_mem {y : ℝ} (h1 : π / 4 ≤ y) (h2 : y ≤ 3 * π / 4) : 1 / 2 ≤ sin y := by
  have hπ := pi_pos
  rcases le_total y (π / 2) with hy | hy
  · have := mul_le_sin (by linarith) hy
    have e : 2 / π * (π / 4) = 1 / 2 := by field_simp; ring
    have : 2 / π * (π / 4) ≤ 2 / π * y := by gcongr
    linarith
  · rw [← sin_pi_sub]
    have := mul_le_sin (x := π - y) (by linarith) (by linarith)
    have e : 2 / π * (π / 4) = 1 / 2 := by field_simp; ring
    have : 2 / π * (π / 4) ≤ 2 / π * (π - y) := by gcongr; linarith
    linarith

/-- The point `τ + (2πn + r)/A` with phase `A(t − τ) = 2πn + r`. -/
def phasePt (A τ : ℝ) (n : ℕ) (r : ℝ) : ℝ := τ + (2 * π * n + r) / A

theorem phase_phasePt {A : ℝ} (hA : 0 < A) (τ : ℝ) (n : ℕ) (r : ℝ) :
    A * (phasePt A τ n r - τ) = 2 * π * n + r := by
  unfold phasePt
  field_simp
  ring

/-- `T_n`: the phase lies in `2πn + [π/4, 3π/4]`. -/
def rectT (A τ : ℝ) (n : ℕ) : Set ℝ := Icc (phasePt A τ n (π / 4)) (phasePt A τ n (3 * π / 4))

/-- `S_n`: the phase lies in `2πn + [5π/4, 7π/4]`. -/
def rectS (A τ : ℝ) (n : ℕ) : Set ℝ :=
  Icc (phasePt A τ n (5 * π / 4)) (phasePt A τ n (7 * π / 4))

theorem phasePt_le_phasePt {A : ℝ} (hA : 0 < A) (τ : ℝ) {n n' : ℕ} {r r' : ℝ}
    (h : 2 * π * n + r ≤ 2 * π * n' + r') : phasePt A τ n r ≤ phasePt A τ n' r' := by
  unfold phasePt
  gcongr

theorem phasePt_sub {A : ℝ} (hA : 0 < A) (τ : ℝ) (n : ℕ) (r r' : ℝ) :
    phasePt A τ n r' - phasePt A τ n r = (r' - r) / A := by
  unfold phasePt
  field_simp
  ring

theorem half_le_sin_of_mem_rectT {A : ℝ} (hA : 0 < A) {τ : ℝ} {n : ℕ} {t : ℝ}
    (ht : t ∈ rectT A τ n) : 1 / 2 ≤ sin (A * (t - τ)) := by
  have h1 : A * (phasePt A τ n (π / 4) - τ) ≤ A * (t - τ) := by gcongr; exact ht.1
  have h2 : A * (t - τ) ≤ A * (phasePt A τ n (3 * π / 4) - τ) := by gcongr; exact ht.2
  rw [phase_phasePt hA] at h1 h2
  have e : sin (A * (t - τ)) = sin (A * (t - τ) - 2 * π * n) := by
    rw [show A * (t - τ) = (A * (t - τ) - 2 * π * n) + (n : ℝ) * (2 * π) by ring,
      sin_add_nat_mul_two_pi]
    congr 1
    ring
  rw [e]
  exact half_le_sin_of_mem (by linarith) (by linarith)

theorem sin_le_neg_half_of_mem_rectS {A : ℝ} (hA : 0 < A) {τ : ℝ} {n : ℕ} {s : ℝ}
    (hs : s ∈ rectS A τ n) : sin (A * (s - τ)) ≤ -(1 / 2) := by
  have h1 : A * (phasePt A τ n (5 * π / 4) - τ) ≤ A * (s - τ) := by gcongr; exact hs.1
  have h2 : A * (s - τ) ≤ A * (phasePt A τ n (7 * π / 4) - τ) := by gcongr; exact hs.2
  rw [phase_phasePt hA] at h1 h2
  have e : sin (A * (s - τ)) = -sin (A * (s - τ) - 2 * π * n - π) := by
    rw [show A * (s - τ) = (A * (s - τ) - 2 * π * n - π + π) + (n : ℝ) * (2 * π) by ring,
      sin_add_nat_mul_two_pi, sin_add_pi]
    congr 2
    ring
  rw [e]
  have := half_le_sin_of_mem (y := A * (s - τ) - 2 * π * n - π) (by linarith) (by linarith)
  linarith

/-- On a rectangle `T_n × S_n` the integrand is at least `4A²/(9π²)`. -/
theorem integrand_ge_of_mem_rect {A : ℝ} (hA : 0 < A) {τ : ℝ} {n : ℕ} {t s : ℝ}
    (ht : t ∈ rectT A τ n) (hs : s ∈ rectS A τ n) :
    4 * A ^ 2 / (9 * π ^ 2) ≤ (sin (A * (t - τ)) - sin (A * (s - τ))) ^ 2 / (t - s) ^ 2 := by
  have hπ := pi_pos
  have h1 := half_le_sin_of_mem_rectT hA ht
  have h2 := sin_le_neg_half_of_mem_rectS hA hs
  have hsin : 1 ≤ (sin (A * (t - τ)) - sin (A * (s - τ))) ^ 2 := by nlinarith
  -- `π/(2A) ≤ s − t ≤ 3π/(2A)`
  have hlo : phasePt A τ n (3 * π / 4) ≤ phasePt A τ n (5 * π / 4) :=
    phasePt_le_phasePt hA τ (by linarith)
  have hst : s - t ≤ 3 * π / (2 * A) := by
    have e := phasePt_sub hA τ n (π / 4) (7 * π / 4)
    have : s - t ≤ phasePt A τ n (7 * π / 4) - phasePt A τ n (π / 4) := by
      linarith [ht.1, hs.2]
    rw [e] at this
    calc s - t ≤ (7 * π / 4 - π / 4) / A := this
      _ = 3 * π / (2 * A) := by field_simp; ring
  have hpos : 0 < s - t := by
    have e := phasePt_sub hA τ n (3 * π / 4) (5 * π / 4)
    have : 0 < phasePt A τ n (5 * π / 4) - phasePt A τ n (3 * π / 4) := by
      rw [e]; exact div_pos (by linarith) hA
    linarith [ht.2, hs.1]
  have hsq : (t - s) ^ 2 ≤ (3 * π / (2 * A)) ^ 2 := by
    rw [show (t - s) ^ 2 = (s - t) ^ 2 by ring]
    exact pow_le_pow_left₀ hpos.le hst 2
  have hts : 0 < (t - s) ^ 2 := by
    have : t - s ≠ 0 := by linarith
    positivity
  rw [le_div_iff₀ hts]
  calc 4 * A ^ 2 / (9 * π ^ 2) * (t - s) ^ 2 ≤ 4 * A ^ 2 / (9 * π ^ 2) * (3 * π / (2 * A)) ^ 2 := by
        gcongr
    _ = 1 := by field_simp; ring
    _ ≤ _ := hsin

/-- **The Gagliardo energy of one oscillation.**  For `A > 0`, `τ ≤ p` and `A (q − p) ≥ 8π`,
`∫∫_{(p,q)²} (sin(A(t−τ)) − sin(A(s−τ)))²/(t − s)² ≥ A (q − p)/(36π)`. -/
theorem lintegral_sin_sub_sq_ge {A τ p q : ℝ} (hA : 0 < A) (hτp : τ ≤ p)
    (hpq : 8 * π ≤ A * (q - p)) :
    ENNReal.ofReal (A * (q - p) / (36 * π)) ≤
      ∫⁻ t in Ioo p q, ∫⁻ s in Ioo p q,
        ENNReal.ofReal ((sin (A * (t - τ)) - sin (A * (s - τ))) ^ 2 / (t - s) ^ 2) := by
  have hπ := pi_pos
  set F : ℝ → ℝ → ℝ≥0∞ := fun t s =>
    ENNReal.ofReal ((sin (A * (t - τ)) - sin (A * (s - τ))) ^ 2 / (t - s) ^ 2) with hF
  -- the number of full periods
  set n₀ : ℕ := ⌈(p - τ) * A / (2 * π)⌉₊ with hn₀
  set Fl : ℕ := ⌊(q - p) * A / (2 * π)⌋₊ with hFl
  have hn₀1 : (p - τ) * A / (2 * π) ≤ n₀ := Nat.le_ceil _
  have hn₀2 : (n₀ : ℝ) < (p - τ) * A / (2 * π) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by linarith) hA.le) (by positivity))
  have hFl1 : (Fl : ℝ) ≤ (q - p) * A / (2 * π) :=
    Nat.floor_le (div_nonneg (mul_nonneg (by nlinarith) hA.le) (by positivity))
  have hFl2 : (q - p) * A / (2 * π) - 1 < Fl := Nat.sub_one_lt_floor _
  have h4 : 4 ≤ (q - p) * A / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hFl4 : 4 ≤ Fl := Nat.le_floor (by exact_mod_cast h4)
  set N : ℕ := Fl - 1 with hN
  have hNr : (N : ℝ) = Fl - 1 := by rw [hN, Nat.cast_sub (by omega)]; simp
  -- the rectangles lie in `(p,q)`
  have hstart : ∀ i : ℕ, p < phasePt A τ (n₀ + i) (π / 4) := by
    intro i
    have : p - τ ≤ 2 * π * n₀ / A := by
      rw [le_div_iff₀ hA]
      rw [div_le_iff₀ (by positivity)] at hn₀1
      linarith
    unfold phasePt
    have : 2 * π * (n₀ : ℝ) / A < (2 * π * ((n₀ + i : ℕ) : ℝ) + π / 4) / A := by
      apply div_lt_div_of_pos_right _ hA
      push_cast
      nlinarith
    linarith
  have hend : ∀ i < N, phasePt A τ (n₀ + i) (7 * π / 4) < q := by
    intro i hi
    have hi' : (i : ℝ) + 2 ≤ Fl := by
      have : i + 2 ≤ Fl := by omega
      exact_mod_cast this
    unfold phasePt
    rw [← lt_sub_iff_add_lt', div_lt_iff₀ hA]
    push_cast
    have e1 : 2 * π * (n₀ : ℝ) < (p - τ) * A + 2 * π := by
      have := hn₀2
      rw [← sub_lt_iff_lt_add, lt_div_iff₀ (by positivity)] at this
      nlinarith
    have e2 : 2 * π * (Fl : ℝ) ≤ (q - p) * A := by
      rw [le_div_iff₀ (by positivity)] at hFl1
      linarith
    nlinarith
  have hTsub : ∀ i < N, rectT A τ (n₀ + i) ⊆ Ioo p q := by
    intro i hi t ht
    refine ⟨lt_of_lt_of_le (hstart i) ht.1, lt_of_le_of_lt ht.2 ?_⟩
    exact lt_of_le_of_lt (phasePt_le_phasePt hA τ (by linarith)) (hend i hi)
  have hSsub : ∀ i < N, rectS A τ (n₀ + i) ⊆ Ioo p q := by
    intro i hi s hs
    refine ⟨lt_of_lt_of_le ?_ hs.1, lt_of_le_of_lt hs.2 (hend i hi)⟩
    exact lt_of_lt_of_le (hstart i) (phasePt_le_phasePt hA τ (by linarith))
  -- disjointness of the `T`'s
  have hdisj : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint fun i => rectT A τ (n₀ + i) := by
    intro i _ i' _ hii'
    rw [Function.onFun, Set.disjoint_left]
    intro t ht ht'
    rcases lt_or_gt_of_ne hii' with h | h
    · have h1 : (i : ℝ) + 1 ≤ i' := by exact_mod_cast h
      have : phasePt A τ (n₀ + i) (3 * π / 4) < phasePt A τ (n₀ + i') (π / 4) := by
        unfold phasePt
        apply add_lt_add_right
        apply div_lt_div_of_pos_right _ hA
        push_cast
        nlinarith
      linarith [ht.2, ht'.1]
    · have h1 : (i' : ℝ) + 1 ≤ i := by exact_mod_cast h
      have : phasePt A τ (n₀ + i') (3 * π / 4) < phasePt A τ (n₀ + i) (π / 4) := by
        unfold phasePt
        apply add_lt_add_right
        apply div_lt_div_of_pos_right _ hA
        push_cast
        nlinarith
      linarith [ht.1, ht'.2]
  -- one rectangle contributes `1/9`
  have hvolT : ∀ n, volume (rectT A τ n) = ENNReal.ofReal (π / (2 * A)) := by
    intro n
    rw [rectT, Real.volume_Icc, phasePt_sub hA]
    congr 1; field_simp; ring
  have hvolS : ∀ n, volume (rectS A τ n) = ENNReal.ofReal (π / (2 * A)) := by
    intro n
    rw [rectS, Real.volume_Icc, phasePt_sub hA]
    congr 1; field_simp; ring
  have hone : ∀ i < N, ENNReal.ofReal (1 / 9) ≤
      ∫⁻ t in rectT A τ (n₀ + i), ∫⁻ s in Ioo p q, F t s := by
    intro i hi
    have hc : ∀ t ∈ rectT A τ (n₀ + i),
        ENNReal.ofReal (4 * A ^ 2 / (9 * π ^ 2)) * ENNReal.ofReal (π / (2 * A))
          ≤ ∫⁻ s in Ioo p q, F t s := by
      intro t ht
      calc ENNReal.ofReal (4 * A ^ 2 / (9 * π ^ 2)) * ENNReal.ofReal (π / (2 * A))
          = ∫⁻ _ in rectS A τ (n₀ + i), ENNReal.ofReal (4 * A ^ 2 / (9 * π ^ 2)) := by
            rw [setLIntegral_const, hvolS]
        _ ≤ ∫⁻ s in rectS A τ (n₀ + i), F t s :=
            setLIntegral_mono' measurableSet_Icc fun s hs =>
              ENNReal.ofReal_le_ofReal (integrand_ge_of_mem_rect hA ht hs)
        _ ≤ ∫⁻ s in Ioo p q, F t s := lintegral_mono_set (hSsub i hi)
    calc ENNReal.ofReal (1 / 9)
        = ∫⁻ _ in rectT A τ (n₀ + i),
            ENNReal.ofReal (4 * A ^ 2 / (9 * π ^ 2)) * ENNReal.ofReal (π / (2 * A)) := by
          rw [setLIntegral_const, hvolT, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp; ring
      _ ≤ _ := setLIntegral_mono' measurableSet_Icc hc
  -- sum over the rectangles
  calc ENNReal.ofReal (A * (q - p) / (36 * π))
      ≤ ENNReal.ofReal (∑ _i ∈ Finset.range N, (1 / 9 : ℝ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hNr]
        have : (q - p) * A / (2 * π) - 2 < (Fl : ℝ) - 1 := by linarith
        have h5 : A * (q - p) / (36 * π) ≤ ((q - p) * A / (2 * π) - 2) / 9 := by
          have hX : A * (q - p) / (36 * π) = ((q - p) * A / (2 * π)) / 18 := by
            field_simp; ring
          rw [hX]
          linarith
        linarith
    _ = ∑ i ∈ Finset.range N, ENNReal.ofReal (1 / 9) :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => by norm_num
    _ ≤ ∑ i ∈ Finset.range N, ∫⁻ t in rectT A τ (n₀ + i), ∫⁻ s in Ioo p q, F t s :=
        Finset.sum_le_sum fun i hi => hone i (Finset.mem_range.1 hi)
    _ = ∫⁻ t in ⋃ i ∈ Finset.range N, rectT A τ (n₀ + i), ∫⁻ s in Ioo p q, F t s :=
        (lintegral_biUnion_finset hdisj (fun _ _ => measurableSet_Icc) _).symm
    _ ≤ ∫⁻ t in Ioo p q, ∫⁻ s in Ioo p q, F t s :=
        lintegral_mono_set (iUnion₂_subset fun i hi => hTsub i (Finset.mem_range.1 hi))

end LionsC12
