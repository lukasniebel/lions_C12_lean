module

public import LionsC12.Construction.Defs
public import LionsC12.Coefficient.Blocks
public import LionsC12.Coefficient.Support
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Proposition 3.2: ellipticity and `1/2`-Hölder time regularity of the coefficient

This file contains the proof of Proposition 3.2 of the paper: the coefficient
`𝔞 = 1 + ε β` is bounded, uniformly close to `1`, and `1/2`-Hölder continuous in
time, uniformly in `x`.

The heart of the matter is the *lacunary sum estimate* `lacunary_min_sum_le`:
for a geometric sequence of frequencies with ratio `16`,
`∑_m min (2 / K_m) (K_m h) ≤ (64/15) √h`,
which is the origin of the exponent `1/2`.  It is proved via an elementary (private)
"tent" estimate: for any `c > 0`,
`∑_{m=1}^N min ((16^m c)⁻¹) (16^m c) ≤ 32/15`, obtained by an induction on `N`
with the potential `16/15 * min 1 z - 1/15 * min 1 z⁻¹ + 1/15` evaluated at the
top frequency `z = 16^N c`.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ### Uniform bounds on `β` and `𝔞` -/

/-- The `0`-th block is trivial (the mode index set `Icc 1 (M 0)` is empty). -/
private lemma βblock_zero (t x : ℝ) : βblock D 0 t x = 0 := by
  have hemp : Finset.Icc 1 (M 0) = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by simp [M])
  unfold βblock
  rw [hemp, Finset.sum_empty]

theorem abs_β_le (t x : ℝ) : |β D t x| ≤ 1 / 480 := by
  by_cases hex : ∃ j, t ∈ I j
  · obtain ⟨j, ht⟩ := hex
    have hj1 : 1 ≤ j := one_le_of_mem_I ht
    rw [β_eq_block D ht x]
    have h1 := abs_βblock_le D hj1 t x
    have h2 := S_le hj1
    have h3 := ℓ_le hj1
    linarith
  · simp only [not_exists] at hex
    rw [β_eq_zero D hex x]
    rw [abs_zero]
    norm_num

theorem a_ge {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (t x : ℝ) : 479 / 480 ≤ a D ε t x := by
  have hb := abs_le.mp (abs_β_le D t x)
  unfold a
  nlinarith [hb.1, hb.2, hε0, hε]

theorem a_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (t x : ℝ) : a D ε t x ≤ 481 / 480 := by
  have hb := abs_le.mp (abs_β_le D t x)
  unfold a
  nlinarith [hb.1, hb.2, hε0, hε]

theorem abs_a_sub_one_le {ε : ℝ} (hε0 : 0 ≤ ε) (t x : ℝ) : |a D ε t x - 1| ≤ ε / 480 := by
  have he : a D ε t x - 1 = ε * β D t x := by unfold a; ring
  rw [he, abs_mul, abs_of_nonneg hε0]
  have h := mul_le_mul_of_nonneg_left (abs_β_le D t x) hε0
  linarith

/-! ### The lacunary sum estimate -/

/-- The elementary one-step estimate driving `lacunary_aux`:  with
`F z = 16/15 * min 1 z - 1/15 * min 1 z⁻¹ + 1/15` one has `min (16z)⁻¹ (16z) + F z ≤ F (16 z)`. -/
private lemma key_step {z : ℝ} (hz : 0 < z) :
    min ((16 * z)⁻¹) (16 * z) + (16 / 15 * min 1 z - 1 / 15 * min 1 z⁻¹ + 1 / 15)
      ≤ 16 / 15 * min 1 (16 * z) - 1 / 15 * min 1 ((16 * z)⁻¹) + 1 / 15 := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hu : (0 : ℝ) < z⁻¹ := inv_pos.mpr hz
  have hzu : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  have hmi : (16 * z)⁻¹ = z⁻¹ / 16 := by
    rw [mul_inv]; ring
  rw [hmi]
  rcases le_total z (1 / 16) with hA | hA
  · -- below the peak: all mins are attained by the "small" branch
    have hA1 : 16 * z ≤ 1 := by linarith
    have hA2 : z ≤ 1 := by linarith
    have hA3 : (1 : ℝ) ≤ z⁻¹ := by
      nlinarith [mul_nonneg hu.le (by linarith : (0:ℝ) ≤ 1 - z)]
    have hA4 : (1 : ℝ) ≤ z⁻¹ / 16 := by
      nlinarith [mul_nonneg (by linarith [hu.le] : (0:ℝ) ≤ z⁻¹ / 16)
        (by linarith : (0:ℝ) ≤ 1 - 16 * z)]
    rw [min_eq_right (by linarith : 16 * z ≤ z⁻¹ / 16), min_eq_right hA2, min_eq_left hA3,
      min_eq_right hA1, min_eq_left hA4]
    linarith
  · rcases le_total z 1 with hB | hC
    · -- at the peak
      have hB1 : (1 : ℝ) ≤ 16 * z := by linarith
      have hB3 : (1 : ℝ) ≤ z⁻¹ := by
        nlinarith [mul_nonneg hu.le (by linarith : (0:ℝ) ≤ 1 - z)]
      have hB4 : z⁻¹ / 16 ≤ 1 := by
        nlinarith [mul_nonneg (by linarith [hu.le] : (0:ℝ) ≤ z⁻¹ / 16)
          (by linarith : (0:ℝ) ≤ 16 * z - 1)]
      have hkey : z⁻¹ + 16 * z ≤ 17 := by
        have h1 : (0:ℝ) ≤ (1 - z) * (16 * z - 1) :=
          mul_nonneg (by linarith) (by linarith)
        have h2 : (z⁻¹ + 16 * z) * z ≤ 17 * z := by nlinarith [hzu, h1]
        exact le_of_mul_le_mul_right h2 hz
      rw [min_eq_left (by linarith : z⁻¹ / 16 ≤ 16 * z), min_eq_right hB, min_eq_left hB3,
        min_eq_left hB1, min_eq_right hB4]
      linarith
    · -- above the peak
      have hC1 : (1 : ℝ) ≤ 16 * z := by linarith
      have hC2 : z⁻¹ ≤ 1 := by
        nlinarith [mul_nonneg hu.le (by linarith : (0:ℝ) ≤ z - 1)]
      have hC3 : z⁻¹ / 16 ≤ 1 := by linarith
      rw [min_eq_left (by linarith : z⁻¹ / 16 ≤ 16 * z), min_eq_left hC, min_eq_right hC2,
        min_eq_left hC1, min_eq_right hC3]
      linarith

/-- The "tent" estimate for a lacunary sequence with ratio `16`:  the sum of
`min ((16^m c)⁻¹) (16^m c)` over `1 ≤ m ≤ N` is bounded by a constant.  The right-hand side is
the potential `F` evaluated at the top frequency; it is `≤ 17/15 ≤ 32/15`. -/
private lemma lacunary_aux (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, min (((16 : ℝ) ^ m * c)⁻¹) ((16 : ℝ) ^ m * c)
      ≤ 16 / 15 * min 1 ((16 : ℝ) ^ N * c)
        - 1 / 15 * min 1 (((16 : ℝ) ^ N * c)⁻¹) + 1 / 15 := by
  induction N with
  | zero =>
      have hemp : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
      rw [hemp, Finset.sum_empty, pow_zero, one_mul]
      have h1 : (0:ℝ) ≤ min 1 c := le_min zero_le_one hc.le
      have h2 : min 1 c⁻¹ ≤ 1 := min_le_left _ _
      linarith
  | succ n ih =>
      have hsplit : ∑ m ∈ Finset.Icc 1 (n + 1), min (((16 : ℝ) ^ m * c)⁻¹) ((16 : ℝ) ^ m * c)
          = (∑ m ∈ Finset.Icc 1 n, min (((16 : ℝ) ^ m * c)⁻¹) ((16 : ℝ) ^ m * c))
            + min (((16 : ℝ) ^ (n + 1) * c)⁻¹) ((16 : ℝ) ^ (n + 1) * c) :=
        Finset.sum_Icc_succ_top (by omega) _
      have he : (16 : ℝ) ^ (n + 1) * c = 16 * ((16 : ℝ) ^ n * c) := by ring
      have hz : (0 : ℝ) < (16 : ℝ) ^ n * c := mul_pos (by positivity) hc
      rw [hsplit, he]
      linarith [ih, key_step hz]

/-- Lacunary sum estimate: for `K₀ > 0` and `h ≥ 0`,
`∑_{m=1}^{N} min (2/(16^m K₀)) (16^m K₀ h) ≤ (64/15) √h`. -/
theorem lacunary_min_sum_le (K₀ : ℝ) (hK₀ : 0 < K₀) (h : ℝ) (hh : 0 ≤ h) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, min (2 / (16 ^ m * K₀)) (16 ^ m * K₀ * h) ≤ 64 / 15 * Real.sqrt h := by
  rcases hh.eq_or_lt with hzero | hpos
  · -- `h = 0`: every term vanishes
    have hzero' : h = 0 := hzero.symm
    subst hzero'
    have hterm : ∀ m ∈ Finset.Icc 1 N,
        min (2 / ((16 : ℝ) ^ m * K₀)) ((16 : ℝ) ^ m * K₀ * 0) = 0 := by
      intro m _
      rw [mul_zero, min_eq_right (le_of_lt (by positivity : (0:ℝ) < 2 / ((16 : ℝ) ^ m * K₀)))]
    rw [Finset.sum_eq_zero hterm, Real.sqrt_zero]
    norm_num
  · have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hpos
    have hsq2 : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh
    have hK0' : K₀ ≠ 0 := ne_of_gt hK₀
    have hsne : Real.sqrt h ≠ 0 := ne_of_gt hs
    have hc : 0 < K₀ * Real.sqrt h := mul_pos hK₀ hs
    have hterm : ∀ m ∈ Finset.Icc 1 N,
        min (2 / ((16 : ℝ) ^ m * K₀)) ((16 : ℝ) ^ m * K₀ * h)
          ≤ 2 * Real.sqrt h *
              min (((16 : ℝ) ^ m * (K₀ * Real.sqrt h))⁻¹) ((16 : ℝ) ^ m * (K₀ * Real.sqrt h)) := by
      intro m _
      have hp : (0 : ℝ) < (16 : ℝ) ^ m := by positivity
      have hpne : ((16 : ℝ) ^ m) ≠ 0 := ne_of_gt hp
      rcases le_total (((16 : ℝ) ^ m * (K₀ * Real.sqrt h))⁻¹)
          ((16 : ℝ) ^ m * (K₀ * Real.sqrt h)) with hcase | hcase
      · rw [min_eq_left hcase]
        refine (min_le_left _ _).trans ?_
        have e1 : ((16 : ℝ) ^ m * (K₀ * Real.sqrt h))⁻¹
            = ((16 : ℝ) ^ m)⁻¹ * K₀⁻¹ * (Real.sqrt h)⁻¹ := by
          rw [mul_inv, mul_inv]; ring
        have e2 : (2 : ℝ) / ((16 : ℝ) ^ m * K₀) = 2 * (((16 : ℝ) ^ m)⁻¹ * K₀⁻¹) := by
          rw [div_eq_mul_inv, mul_inv]
        have hss : Real.sqrt h * (Real.sqrt h)⁻¹ = 1 := mul_inv_cancel₀ hsne
        have e3 : 2 * Real.sqrt h * ((16 : ℝ) ^ m * (K₀ * Real.sqrt h))⁻¹
            = 2 / ((16 : ℝ) ^ m * K₀) := by
          calc 2 * Real.sqrt h * ((16 : ℝ) ^ m * (K₀ * Real.sqrt h))⁻¹
              = (Real.sqrt h * (Real.sqrt h)⁻¹) * (2 * (((16 : ℝ) ^ m)⁻¹ * K₀⁻¹)) := by
                rw [e1]; ring
            _ = 2 * (((16 : ℝ) ^ m)⁻¹ * K₀⁻¹) := by rw [hss, one_mul]
            _ = 2 / ((16 : ℝ) ^ m * K₀) := e2.symm
        exact le_of_eq e3.symm
      · rw [min_eq_right hcase]
        refine (min_le_right _ _).trans ?_
        have he : 2 * Real.sqrt h * ((16 : ℝ) ^ m * (K₀ * Real.sqrt h))
            = 2 * ((16 : ℝ) ^ m * K₀ * h) := by
          calc 2 * Real.sqrt h * ((16 : ℝ) ^ m * (K₀ * Real.sqrt h))
              = 2 * (16 : ℝ) ^ m * K₀ * (Real.sqrt h * Real.sqrt h) := by ring
            _ = 2 * ((16 : ℝ) ^ m * K₀ * h) := by rw [hsq2]; ring
        rw [he]
        have : (0:ℝ) ≤ (16 : ℝ) ^ m * K₀ * h :=
          mul_nonneg (mul_nonneg hp.le hK₀.le) hh
        linarith
    have hb := lacunary_aux (K₀ * Real.sqrt h) hc N
    have hb2 : ∑ m ∈ Finset.Icc 1 N,
        min (((16 : ℝ) ^ m * (K₀ * Real.sqrt h))⁻¹) ((16 : ℝ) ^ m * (K₀ * Real.sqrt h))
          ≤ 32 / 15 := by
      have h1 : min 1 ((16 : ℝ) ^ N * (K₀ * Real.sqrt h)) ≤ 1 := min_le_left _ _
      have h2 : (0:ℝ) ≤ min 1 (((16 : ℝ) ^ N * (K₀ * Real.sqrt h))⁻¹) :=
        le_min zero_le_one (inv_nonneg.mpr (le_of_lt (mul_pos (by positivity) hc)))
      linarith
    calc ∑ m ∈ Finset.Icc 1 N, min (2 / (16 ^ m * K₀)) (16 ^ m * K₀ * h)
        ≤ ∑ m ∈ Finset.Icc 1 N, 2 * Real.sqrt h *
            min (((16 : ℝ) ^ m * (K₀ * Real.sqrt h))⁻¹) ((16 : ℝ) ^ m * (K₀ * Real.sqrt h)) :=
          Finset.sum_le_sum hterm
      _ = 2 * Real.sqrt h * ∑ m ∈ Finset.Icc 1 N,
            min (((16 : ℝ) ^ m * (K₀ * Real.sqrt h))⁻¹) ((16 : ℝ) ^ m * (K₀ * Real.sqrt h)) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * Real.sqrt h * (32 / 15) :=
          mul_le_mul_of_nonneg_left hb2 (mul_nonneg (by norm_num) hs.le)
      _ = 64 / 15 * Real.sqrt h := by ring

/-! ### The `1/2`-Hölder estimate -/

/-- The Hölder constant of one block. -/
def Cβ : ℝ := D.Cη / 15 + 64 / 15 + 2 / 15

theorem Cβ_nonneg : 0 ≤ Cβ D := by
  have := D.Cη_nonneg
  unfold Cβ
  linarith

/-- One mode of the difference: a Lipschitz part coming from the cutoff plus the oscillatory
part `min (2 K⁻¹) (K h)`. -/
theorem abs_βmode_sub_le {j : ℕ} (hj : 1 ≤ j) (m : ℕ) (s t x : ℝ) :
    |βmode D j m t x - βmode D j m s x|
      ≤ D.Cη / ℓ j * |t - s| * ((K j m : ℝ))⁻¹
        + min (2 / ((16 : ℝ) ^ m * (ℓ j)⁻¹)) ((16 : ℝ) ^ m * (ℓ j)⁻¹ * |t - s|) := by
  have hℓ : 0 < ℓ j := ℓ_pos hj
  have hℓ0 : ℓ j ≠ 0 := ne_of_gt hℓ
  have hK : (0 : ℝ) < (K j m : ℝ) := Nat.cast_pos.mpr (K_pos hj)
  have hK0 : (K j m : ℝ) ≠ 0 := ne_of_gt hK
  have hKi : (0 : ℝ) ≤ ((K j m : ℝ))⁻¹ := inv_nonneg.mpr hK.le
  have hKe : (K j m : ℝ) = (16 : ℝ) ^ m * (ℓ j)⁻¹ := by
    have hKℓ : (K j m : ℝ) * ℓ j = (16 : ℝ) ^ m := K_mul_ℓ (j := j) (m := m) hj
    rw [← hKℓ, mul_assoc, mul_inv_cancel₀ hℓ0, mul_one]
  -- the two pieces
  have hdecomp : βmode D j m t x - βmode D j m s x
      = (ηj D j t - ηj D j s) *
          (((K j m : ℝ))⁻¹ * sin (θ j m t) * cos ((K j m : ℝ) * x))
        + (ηj D j s * ((K j m : ℝ))⁻¹ * cos ((K j m : ℝ) * x)) *
            (sin (θ j m t) - sin (θ j m s)) := by
    unfold βmode
    ring
  have hbound1 : |((K j m : ℝ))⁻¹ * sin (θ j m t) * cos ((K j m : ℝ) * x)| ≤ ((K j m : ℝ))⁻¹ := by
    have e : |((K j m : ℝ))⁻¹ * sin (θ j m t) * cos ((K j m : ℝ) * x)|
        = ((K j m : ℝ))⁻¹ * |sin (θ j m t)| * |cos ((K j m : ℝ) * x)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hKi]
    rw [e]
    have h1 : ((K j m : ℝ))⁻¹ * |sin (θ j m t)| ≤ ((K j m : ℝ))⁻¹ :=
      mul_le_of_le_one_right hKi (Real.abs_sin_le_one _)
    have h2 : ((K j m : ℝ))⁻¹ * |sin (θ j m t)| * |cos ((K j m : ℝ) * x)|
        ≤ ((K j m : ℝ))⁻¹ * |sin (θ j m t)| :=
      mul_le_of_le_one_right (mul_nonneg hKi (abs_nonneg _)) (Real.abs_cos_le_one _)
    linarith
  have hbound2 : |ηj D j s * ((K j m : ℝ))⁻¹ * cos ((K j m : ℝ) * x)| ≤ ((K j m : ℝ))⁻¹ := by
    have e : |ηj D j s * ((K j m : ℝ))⁻¹ * cos ((K j m : ℝ) * x)|
        = |ηj D j s| * ((K j m : ℝ))⁻¹ * |cos ((K j m : ℝ) * x)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hKi]
    rw [e]
    have h1 : |ηj D j s| * ((K j m : ℝ))⁻¹ ≤ ((K j m : ℝ))⁻¹ :=
      mul_le_of_le_one_left hKi (abs_ηj_le_one D j s)
    have h2 : |ηj D j s| * ((K j m : ℝ))⁻¹ * |cos ((K j m : ℝ) * x)|
        ≤ |ηj D j s| * ((K j m : ℝ))⁻¹ :=
      mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) hKi) (Real.abs_cos_le_one _)
    linarith
  rw [hdecomp]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    refine mul_le_mul (abs_ηj_sub_le D hj s t) hbound1 (abs_nonneg _) ?_
    exact mul_nonneg (div_nonneg D.Cη_nonneg hℓ.le) (abs_nonneg _)
  · rw [abs_mul]
    rcases le_total (2 / ((16 : ℝ) ^ m * (ℓ j)⁻¹))
        ((16 : ℝ) ^ m * (ℓ j)⁻¹ * |t - s|) with hcase | hcase
    · rw [min_eq_left hcase]
      have hsin : |sin (θ j m t) - sin (θ j m s)| ≤ 2 := by
        calc |sin (θ j m t) - sin (θ j m s)| ≤ |sin (θ j m t)| + |sin (θ j m s)| :=
              abs_sub _ _
          _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
          _ = 2 := by norm_num
      calc |ηj D j s * ((K j m : ℝ))⁻¹ * cos ((K j m : ℝ) * x)| *
              |sin (θ j m t) - sin (θ j m s)|
          ≤ ((K j m : ℝ))⁻¹ * 2 := mul_le_mul hbound2 hsin (abs_nonneg _) hKi
        _ = 2 / ((16 : ℝ) ^ m * (ℓ j)⁻¹) := by rw [← hKe]; ring
    · rw [min_eq_right hcase]
      have hθ : θ j m t - θ j m s = (K j m : ℝ) ^ 2 * (t - s) := by
        unfold θ; ring
      have hsin : |sin (θ j m t) - sin (θ j m s)| ≤ (K j m : ℝ) ^ 2 * |t - s| := by
        have e : |θ j m t - θ j m s| = (K j m : ℝ) ^ 2 * |t - s| := by
          rw [hθ, abs_mul, abs_of_nonneg (sq_nonneg ((K j m : ℝ)))]
        exact (Real.abs_sin_sub_sin_le _ _).trans (le_of_eq e)
      calc |ηj D j s * ((K j m : ℝ))⁻¹ * cos ((K j m : ℝ) * x)| *
              |sin (θ j m t) - sin (θ j m s)|
          ≤ ((K j m : ℝ))⁻¹ * ((K j m : ℝ) ^ 2 * |t - s|) :=
            mul_le_mul hbound2 hsin (abs_nonneg _) hKi
        _ = (((K j m : ℝ))⁻¹ * (K j m : ℝ)) * ((K j m : ℝ) * |t - s|) := by ring
        _ = (K j m : ℝ) * |t - s| := by rw [inv_mul_cancel₀ hK0, one_mul]
        _ = (16 : ℝ) ^ m * (ℓ j)⁻¹ * |t - s| := by rw [hKe]

theorem abs_βblock_sub_le {j : ℕ} (hj : 1 ≤ j) (s t x : ℝ) :
    |βblock D j t x - βblock D j s x| ≤ Cβ D * Real.sqrt |t - s| := by
  have hCη := D.Cη_nonneg
  have hℓ : 0 < ℓ j := ℓ_pos hj
  have hℓ0 : ℓ j ≠ 0 := ne_of_gt hℓ
  have hℓ1 : ℓ j ≤ 1 := ℓ_le_one hj
  have hh : (0:ℝ) ≤ |t - s| := abs_nonneg _
  have hsq : (0:ℝ) ≤ Real.sqrt |t - s| := Real.sqrt_nonneg _
  rcases le_total (ℓ j) |t - s| with hcase | hcase
  · -- long time increments: use the uniform bound on each block
    have h1 : |βblock D j t x| ≤ S j := abs_βblock_le D hj t x
    have h2 : |βblock D j s x| ≤ S j := abs_βblock_le D hj s x
    have h3 : S j ≤ ℓ j / 15 := S_le hj
    have h4 : ℓ j ≤ Real.sqrt |t - s| := by
      have h5 : ℓ j ≤ Real.sqrt (ℓ j) := by
        rw [Real.le_sqrt hℓ.le hℓ.le]
        nlinarith [mul_nonneg hℓ.le (by linarith : (0:ℝ) ≤ 1 - ℓ j)]
      exact h5.trans (Real.sqrt_le_sqrt hcase)
    calc |βblock D j t x - βblock D j s x| ≤ |βblock D j t x| + |βblock D j s x| :=
          abs_sub _ _
      _ ≤ 2 * (ℓ j / 15) := by linarith
      _ ≤ 2 / 15 * Real.sqrt |t - s| := by linarith
      _ ≤ Cβ D * Real.sqrt |t - s| :=
          mul_le_mul_of_nonneg_right (by unfold Cβ; linarith) hsq
  · -- short time increments: the modewise estimate
    have hK₀ : (0:ℝ) < (ℓ j)⁻¹ := inv_pos.mpr hℓ
    have hsub : |t - s| ≤ Real.sqrt |t - s| := by
      rw [Real.le_sqrt hh hh]
      nlinarith [mul_nonneg hh (by linarith : (0:ℝ) ≤ 1 - |t - s|)]
    have hsum : |βblock D j t x - βblock D j s x|
        ≤ ∑ m ∈ Finset.Icc 1 (M j), (D.Cη / ℓ j * |t - s| * ((K j m : ℝ))⁻¹
            + min (2 / ((16 : ℝ) ^ m * (ℓ j)⁻¹)) ((16 : ℝ) ^ m * (ℓ j)⁻¹ * |t - s|)) := by
      have e : βblock D j t x - βblock D j s x
          = ∑ m ∈ Finset.Icc 1 (M j), (βmode D j m t x - βmode D j m s x) := by
        unfold βblock
        exact (Finset.sum_sub_distrib _ _).symm
      rw [e]
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun m _ => abs_βmode_sub_le D hj m s t x)
    have hsplit : ∑ m ∈ Finset.Icc 1 (M j), (D.Cη / ℓ j * |t - s| * ((K j m : ℝ))⁻¹
          + min (2 / ((16 : ℝ) ^ m * (ℓ j)⁻¹)) ((16 : ℝ) ^ m * (ℓ j)⁻¹ * |t - s|))
        = D.Cη / ℓ j * |t - s| * (∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹)
          + ∑ m ∈ Finset.Icc 1 (M j),
              min (2 / ((16 : ℝ) ^ m * (ℓ j)⁻¹)) ((16 : ℝ) ^ m * (ℓ j)⁻¹ * |t - s|) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    have hS : (∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹) ≤ ℓ j / 15 := S_le hj
    have hfirst : D.Cη / ℓ j * |t - s| * (∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹)
        ≤ D.Cη / 15 * Real.sqrt |t - s| := by
      have hpos : (0:ℝ) ≤ D.Cη / ℓ j * |t - s| :=
        mul_nonneg (div_nonneg hCη hℓ.le) hh
      have h1 : D.Cη / ℓ j * |t - s| * (∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹)
          ≤ D.Cη / ℓ j * |t - s| * (ℓ j / 15) := mul_le_mul_of_nonneg_left hS hpos
      have h2 : D.Cη / ℓ j * |t - s| * (ℓ j / 15) = D.Cη / 15 * |t - s| := by
        have hl : ℓ j / ℓ j = 1 := div_self hℓ0
        calc D.Cη / ℓ j * |t - s| * (ℓ j / 15)
            = (ℓ j / ℓ j) * (D.Cη / 15 * |t - s|) := by ring
          _ = D.Cη / 15 * |t - s| := by rw [hl, one_mul]
      have h3 : D.Cη / 15 * |t - s| ≤ D.Cη / 15 * Real.sqrt |t - s| :=
        mul_le_mul_of_nonneg_left hsub (by linarith)
      linarith
    have hsecond : ∑ m ∈ Finset.Icc 1 (M j),
        min (2 / ((16 : ℝ) ^ m * (ℓ j)⁻¹)) ((16 : ℝ) ^ m * (ℓ j)⁻¹ * |t - s|)
          ≤ 64 / 15 * Real.sqrt |t - s| :=
      lacunary_min_sum_le ((ℓ j)⁻¹) hK₀ (|t - s|) hh (M j)
    have hCβ : Cβ D * Real.sqrt |t - s|
        = D.Cη / 15 * Real.sqrt |t - s| + 64 / 15 * Real.sqrt |t - s|
          + 2 / 15 * Real.sqrt |t - s| := by
      unfold Cβ; ring
    have hlast : (0:ℝ) ≤ 2 / 15 * Real.sqrt |t - s| := by linarith
    rw [hsplit] at hsum
    rw [hCβ]
    linarith

/-- The one-block estimate, also for the (trivial) block `j = 0`. -/
private lemma abs_βblock_sub_le' (j : ℕ) (s t x : ℝ) :
    |βblock D j t x - βblock D j s x| ≤ Cβ D * Real.sqrt |t - s| := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [βblock_zero D t x, βblock_zero D s x, sub_zero, abs_zero]
    exact mul_nonneg (Cβ_nonneg D) (Real.sqrt_nonneg _)
  · exact abs_βblock_sub_le D hj s t x

/-- At each time, `β` is given by a single block, and all other blocks vanish. -/
private lemma exists_index (t x : ℝ) :
    ∃ j, β D t x = βblock D j t x ∧ ∀ i, i ≠ j → βblock D i t x = 0 := by
  by_cases hex : ∃ j, t ∈ I j
  · obtain ⟨j, ht⟩ := hex
    exact ⟨j, β_eq_block D ht x, fun i hij => βblock_eq_zero D (notMem_I_of_mem_I ht hij) x⟩
  · simp only [not_exists] at hex
    refine ⟨0, ?_, fun i _ => βblock_eq_zero D (hex i) x⟩
    rw [β_eq_zero D hex x, βblock_zero D t x]

theorem abs_β_sub_le (s t x : ℝ) : |β D t x - β D s x| ≤ 2 * Cβ D * Real.sqrt |t - s| := by
  obtain ⟨j, hjβ, hjz⟩ := exists_index D t x
  obtain ⟨k, hkβ, hkz⟩ := exists_index D s x
  by_cases hjk : j = k
  · subst hjk
    rw [hjβ, hkβ]
    have h1 := abs_βblock_sub_le' D j s t x
    have h2 : (0:ℝ) ≤ Cβ D * Real.sqrt |t - s| :=
      mul_nonneg (Cβ_nonneg D) (Real.sqrt_nonneg _)
    linarith
  · have h1 : βblock D k t x = 0 := hjz k (Ne.symm hjk)
    have h2 : βblock D j s x = 0 := hkz j hjk
    have hdiff : β D t x - β D s x
        = (βblock D j t x - βblock D j s x) + (βblock D k t x - βblock D k s x) := by
      rw [hjβ, hkβ, h1, h2]; ring
    rw [hdiff]
    calc |(βblock D j t x - βblock D j s x) + (βblock D k t x - βblock D k s x)|
        ≤ |βblock D j t x - βblock D j s x| + |βblock D k t x - βblock D k s x| :=
          abs_add_le _ _
      _ ≤ Cβ D * Real.sqrt |t - s| + Cβ D * Real.sqrt |t - s| :=
          add_le_add (abs_βblock_sub_le' D j s t x) (abs_βblock_sub_le' D k s t x)
      _ = 2 * Cβ D * Real.sqrt |t - s| := by ring

theorem abs_a_sub_le (ε : ℝ) (s t x : ℝ) :
    |a D ε t x - a D ε s x| ≤ 2 * |ε| * Cβ D * Real.sqrt |t - s| := by
  have hdiff : a D ε t x - a D ε s x = ε * (β D t x - β D s x) := by
    unfold a; ring
  rw [hdiff, abs_mul]
  calc |ε| * |β D t x - β D s x| ≤ |ε| * (2 * Cβ D * Real.sqrt |t - s|) :=
        mul_le_mul_of_nonneg_left (abs_β_sub_le D s t x) (abs_nonneg _)
    _ = 2 * |ε| * Cβ D * Real.sqrt |t - s| := by ring

end LionsC12

end
