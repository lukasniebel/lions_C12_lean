module

public import LionsC12.Construction.Defs
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.PSeries

/-!
# Arithmetic of the time blocks and lacunary frequencies (Section 3 of the paper)

This file proves elementary real/natural number facts about `τ`, `ℓ`, `θ`, `K`, `S`, `M`
defined in `LionsC12.Construction.Defs`, together with the elementary product bound
`abs_mul_le_mul` used throughout the construction.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ## An elementary product bound -/

/-- `|a b| ≤ A B` whenever `|a| ≤ A` and `|b| ≤ B`. -/
theorem abs_mul_le_mul {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg a).trans ha)

/-! ## `τ` and `ℓ` -/

theorem τ_zero : τ 0 = 5 / 16 := by
  unfold τ; push_cast; norm_num

theorem τ_one : τ 1 = 1 / 4 := by
  unfold τ; push_cast; norm_num

theorem ℓ_zero : ℓ 0 = 0 := by
  unfold ℓ; push_cast; norm_num

theorem ℓ_pos {j : ℕ} (hj : 1 ≤ j) : 0 < ℓ j := by
  have hj0 : 0 < j := by omega
  have hjR : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj0
  have hj1R : (0:ℝ) < (j:ℝ) + 1 := by linarith
  unfold ℓ
  positivity

theorem ℓ_le {j : ℕ} (hj : 1 ≤ j) : ℓ j ≤ 1 / 32 := by
  have hj' : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hj0 : (0:ℝ) < (j:ℝ) := by linarith
  have hj1 : (0:ℝ) < (j:ℝ) + 1 := by linarith
  unfold ℓ
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (j:ℝ) - 1) (by linarith : (0:ℝ) ≤ (j:ℝ) + 2)]

theorem ℓ_le_one {j : ℕ} (hj : 1 ≤ j) : ℓ j ≤ 1 := le_trans (ℓ_le hj) (by norm_num)

/-- `ℓ` is antitone on `j ≥ 1`. -/
theorem ℓ_antitone {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : ℓ j ≤ ℓ i := by
  have hi' : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  rw [ℓ, ℓ]
  exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)

theorem τ_add_ℓ {j : ℕ} (hj : 1 ≤ j) : τ j + ℓ j = τ (j + 1) := by
  have hj0 : (j:ℝ) ≠ 0 := by
    have : 0 < j := by omega
    exact_mod_cast this.ne'
  have hj1 : (j:ℝ) + 1 ≠ 0 := by positivity
  unfold τ ℓ
  push_cast
  field_simp [hj0, hj1]
  ring

theorem τ_ge {j : ℕ} (hj : 1 ≤ j) : 1 / 4 ≤ τ j := by
  unfold τ
  have h : (1:ℝ) / (16 * j) ≤ 1 / 16 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have hj' : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
    nlinarith
  linarith

theorem τ_lt {j : ℕ} (hj : 1 ≤ j) : τ j < 5 / 16 := by
  unfold τ
  have hj0 : 0 < j := by omega
  have hj' : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj0
  have : (0:ℝ) < 1 / (16 * (j:ℝ)) := by positivity
  linarith

theorem τ_succ_le_of_lt {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) : τ (i + 1) ≤ τ j := by
  have hij' : i + 1 ≤ j := by omega
  have h2 : (i:ℝ) + 1 ≤ (j:ℝ) := by exact_mod_cast hij'
  have hipos : (0:ℝ) < (i:ℝ) + 1 := by positivity
  have key : (1:ℝ) / (16 * (j:ℝ)) ≤ 1 / (16 * ((i:ℝ) + 1)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  unfold τ
  push_cast
  linarith

/-- `τ` is monotone on `j ≥ 1`. -/
theorem τ_mono {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : τ i ≤ τ j := by
  have hi' : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have h1 : (0 : ℝ) < 16 * (i : ℝ) := by linarith
  have h : 1 / (16 * (j : ℝ)) ≤ 1 / (16 * (i : ℝ)) := by
    apply one_div_le_one_div_of_le h1
    linarith
  simp only [τ]
  linarith

/-! ## The blocks `I j` and `J j` -/

theorem I_zero : I 0 = ∅ := by
  have h : I 0 = Set.Ioo (τ 0) (τ 1) := rfl
  rw [h, τ_zero, τ_one]
  apply Set.Ioo_eq_empty
  norm_num

/-- Every `t` lying in some block lies in a block with index `≥ 1`. -/
theorem one_le_of_mem_I {j : ℕ} {t : ℝ} (ht : t ∈ I j) : 1 ≤ j := by
  rcases Nat.eq_zero_or_pos j with rfl | h
  · rw [I_zero] at ht
    simp at ht
  · omega

theorem I_subset {j : ℕ} (hj : 1 ≤ j) : I j ⊆ Set.Icc (1 / 4 : ℝ) (5 / 16) := by
  intro t ht
  unfold I at ht
  obtain ⟨ht1, ht2⟩ := ht
  have h1 := τ_ge hj
  have h2 := τ_lt (j := j + 1) (by omega)
  exact ⟨by linarith, by linarith⟩

/-- The accumulation time `5/16` lies in no block. -/
theorem five_sixteenths_notMem_I (j : ℕ) : (5 / 16 : ℝ) ∉ I j := by
  intro h
  have h1 : (5 / 16 : ℝ) < τ (j + 1) := h.2
  have h2 : τ (j + 1) < 5 / 16 := τ_lt (by omega)
  linarith

private theorem I_disjoint_of_lt {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    Disjoint (I i) (I j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  unfold I at hxi hxj
  have h1 : x < τ (i + 1) := hxi.2
  have h2 : τ j < x := hxj.1
  have h3 := τ_succ_le_of_lt hi hij
  linarith

theorem I_disjoint {i j : ℕ} (hij : i ≠ j) : Disjoint (I i) (I j) := by
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    rw [I_zero]
    simp
  · rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [I_zero]
      simp
    · rcases lt_or_gt_of_ne hij with h | h
      · exact I_disjoint_of_lt hi0 h
      · exact (I_disjoint_of_lt hj0 h).symm

theorem J_subset_I {j : ℕ} (hj : 1 ≤ j) : J j ⊆ I j := by
  intro t ht
  unfold J at ht
  obtain ⟨ht1, ht2⟩ := ht
  have hℓ := ℓ_pos hj
  have hτ := τ_add_ℓ hj
  unfold I
  rw [← hτ]
  exact ⟨by linarith, by linarith⟩

theorem isOpen_I (j : ℕ) : IsOpen (I j) := by
  unfold I; exact isOpen_Ioo

/-! ## The phases `θ j m` -/

theorem continuous_θ (j m : ℕ) : Continuous (θ j m) := by
  show Continuous fun t : ℝ => (K j m : ℝ) ^ 2 * (t - τ j)
  exact continuous_const.mul (continuous_id.sub continuous_const)

/-! ## The lacunary frequencies `K j m` -/

theorem K_pos {j m : ℕ} (hj : 1 ≤ j) : 0 < K j m := by
  have hj0 : 0 < j := by omega
  unfold K
  positivity

theorem K_succ (j m : ℕ) : K j (m + 1) = 16 * K j m := by
  unfold K; ring

theorem K_ge {j m : ℕ} (hj : 1 ≤ j) (hm : 1 ≤ m) : 512 ≤ K j m := by
  unfold K
  have h1 : (256:ℕ) ≤ 16 ^ (m + 1) := by
    calc (256:ℕ) = 16 ^ 2 := by norm_num
      _ ≤ 16 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (2:ℕ) ≤ j * (j + 1) := by
    have h := Nat.mul_le_mul hj (show 2 ≤ j + 1 by omega)
    norm_num at h
    exact h
  calc (512:ℕ) = 256 * 2 := by norm_num
    _ ≤ 16 ^ (m + 1) * (j * (j + 1)) := Nat.mul_le_mul h1 h2
    _ = 16 ^ (m + 1) * j * (j + 1) := by ring

theorem two_lt_K {j m : ℕ} (hj : 1 ≤ j) (hm : 1 ≤ m) : 2 < K j m := by
  have h := K_ge hj hm
  omega

theorem K_le_of_lt {j m m' : ℕ} (h : m < m') : 16 * K j m ≤ K j m' := by
  unfold K
  have hp : 16 ^ (m + 2) ≤ 16 ^ (m' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 16 * (16 ^ (m + 1) * j * (j + 1)) = 16 ^ (m + 2) * j * (j + 1) := by ring
    _ ≤ 16 ^ (m' + 1) * j * (j + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hp le_rfl) le_rfl

theorem K_inv_eq {j m : ℕ} (hj : 1 ≤ j) : ((K j m : ℝ))⁻¹ = ℓ j / 16 ^ m := by
  have hj0 : (j:ℝ) ≠ 0 := by
    have : 0 < j := by omega
    exact_mod_cast this.ne'
  have hj1 : (j:ℝ) + 1 ≠ 0 := by positivity
  have h16m : (16:ℝ) ^ m ≠ 0 := by positivity
  unfold K ℓ
  push_cast
  field_simp [hj0, hj1, h16m]
  ring

theorem K_mul_ℓ {j m : ℕ} (hj : 1 ≤ j) : (K j m : ℝ) * ℓ j = 16 ^ m := by
  have hj0 : (j:ℝ) ≠ 0 := by
    have : 0 < j := by omega
    exact_mod_cast this.ne'
  have hj1 : (j:ℝ) + 1 ≠ 0 := by positivity
  unfold K ℓ
  push_cast
  field_simp [hj0, hj1]
  ring

theorem one_le_K_sq_mul_ℓ {j m : ℕ} (hj : 1 ≤ j) : 1 ≤ (K j m : ℝ) ^ 2 * ℓ j := by
  have hKl : (K j m : ℝ) * ℓ j = 16 ^ m := K_mul_ℓ hj
  have hpos : 0 < K j m := K_pos hj
  have hK1 : (1:ℝ) ≤ (K j m : ℝ) := by exact_mod_cast hpos
  have h16 : (1:ℝ) ≤ (16:ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hK0 : (0:ℝ) ≤ (K j m : ℝ) := by positivity
  calc (1:ℝ) = 1 * 1 := by norm_num
    _ ≤ (K j m : ℝ) * 16 ^ m := mul_le_mul hK1 h16 (by norm_num) hK0
    _ = (K j m : ℝ) * ((K j m : ℝ) * ℓ j) := by rw [hKl]
    _ = (K j m : ℝ) ^ 2 * ℓ j := by ring

theorem six_le_K_sq_mul_ℓ {j m : ℕ} (hj : 1 ≤ j) (hm : 1 ≤ m) :
    6 ≤ (K j m : ℝ) ^ 2 * ℓ j := by
  have hKl : (K j m : ℝ) * ℓ j = 16 ^ m := K_mul_ℓ hj
  have hK512 : (512:ℝ) ≤ (K j m : ℝ) := by
    have := K_ge hj hm
    exact_mod_cast this
  have h16 : (16:ℝ) ≤ 16 ^ m := by
    calc (16:ℝ) = 16 ^ 1 := by norm_num
      _ ≤ 16 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hK0 : (0:ℝ) ≤ (K j m : ℝ) := by positivity
  calc (6:ℝ) ≤ 512 * 16 := by norm_num
    _ ≤ (K j m : ℝ) * 16 ^ m := mul_le_mul hK512 h16 (by norm_num) hK0
    _ = (K j m : ℝ) * ((K j m : ℝ) * ℓ j) := by rw [hKl]
    _ = (K j m : ℝ) ^ 2 * ℓ j := by ring

/-! ## `S j` -/

theorem S_nonneg (j : ℕ) : 0 ≤ S j := by
  unfold S
  apply Finset.sum_nonneg
  intro m _
  positivity

theorem S_le {j : ℕ} (hj : 1 ≤ j) : S j ≤ ℓ j / 15 := by
  unfold S
  have hrw : ∀ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹ = ℓ j * (1 / 16 : ℝ) ^ m := by
    intro m _
    rw [K_inv_eq hj, div_pow, one_pow, mul_one_div]
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  have hbound : ∑ m ∈ Finset.Icc 1 (M j), (1 / 16 : ℝ) ^ m ≤ (1 / 16) / (1 - 1 / 16) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := M j + 1) (x := (1 / 16 : ℝ))
      (by norm_num) (by norm_num)
    rwa [Finset.Ico_add_one_right_eq_Icc, pow_one] at h
  have hval : (1 / 16 : ℝ) / (1 - 1 / 16) = 1 / 15 := by norm_num
  have hℓ : (0:ℝ) ≤ ℓ j := le_of_lt (ℓ_pos hj)
  calc ℓ j * ∑ m ∈ Finset.Icc 1 (M j), (1 / 16 : ℝ) ^ m
      ≤ ℓ j * ((1 / 16) / (1 - 1 / 16)) := mul_le_mul_of_nonneg_left hbound hℓ
    _ = ℓ j * (1 / 15) := by rw [hval]
    _ = ℓ j / 15 := by ring

theorem sum_K_inv_sq_le {j : ℕ} (hj : 1 ≤ j) :
    ∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹ ^ 2 ≤ ℓ j ^ 2 / 255 := by
  have hrw : ∀ m ∈ Finset.Icc 1 (M j),
      ((K j m : ℝ))⁻¹ ^ 2 = ℓ j ^ 2 * (1 / 256 : ℝ) ^ m := by
    intro m _
    have hK1 : ((K j m : ℝ))⁻¹ = ℓ j * (1 / 16 : ℝ) ^ m := by
      rw [K_inv_eq hj, div_pow, one_pow, mul_one_div]
    rw [hK1, mul_pow, ← pow_mul, mul_comm m 2, pow_mul,
        show ((1 / 16 : ℝ) ^ 2) = (1 / 256 : ℝ) from by norm_num]
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  have hbound : ∑ m ∈ Finset.Icc 1 (M j), (1 / 256 : ℝ) ^ m ≤ (1 / 256) / (1 - 1 / 256) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := M j + 1) (x := (1 / 256 : ℝ))
      (by norm_num) (by norm_num)
    rwa [Finset.Ico_add_one_right_eq_Icc, pow_one] at h
  have hval : (1 / 256 : ℝ) / (1 - 1 / 256) = 1 / 255 := by norm_num
  have hℓ2 : (0:ℝ) ≤ ℓ j ^ 2 := sq_nonneg _
  calc ℓ j ^ 2 * ∑ m ∈ Finset.Icc 1 (M j), (1 / 256 : ℝ) ^ m
      ≤ ℓ j ^ 2 * ((1 / 256) / (1 - 1 / 256)) := mul_le_mul_of_nonneg_left hbound hℓ2
    _ = ℓ j ^ 2 * (1 / 255) := by rw [hval]
    _ = ℓ j ^ 2 / 255 := by ring

/-! ## `M j` -/

theorem M_mul_ℓ {j : ℕ} (hj : 1 ≤ j) : (M j : ℝ) * ℓ j = 1 / (16 * ((j:ℝ) + 1)) := by
  have hj0 : (j:ℝ) ≠ 0 := by
    have : 0 < j := by omega
    exact_mod_cast this.ne'
  have hj1 : (j:ℝ) + 1 ≠ 0 := by positivity
  unfold M ℓ
  field_simp [hj0, hj1]

theorem M_mul_S_le {j : ℕ} (hj : 1 ≤ j) :
    (M j : ℝ) * S j ≤ 1 / (240 * ((j:ℝ) + 1)) := by
  have hM0 : (0:ℝ) ≤ (M j : ℝ) := Nat.cast_nonneg _
  have hSle := S_le hj
  have hMℓ := M_mul_ℓ hj
  have hj1 : (j:ℝ) + 1 ≠ 0 := by positivity
  calc (M j : ℝ) * S j ≤ (M j : ℝ) * (ℓ j / 15) := mul_le_mul_of_nonneg_left hSle hM0
    _ = (M j : ℝ) * ℓ j / 15 := by ring
    _ = (1 / (16 * ((j:ℝ) + 1))) / 15 := by rw [hMℓ]
    _ = 1 / (240 * ((j:ℝ) + 1)) := by field_simp; ring

/-! ## Divergence of the harmonic series -/

/-- Divergence of the harmonic series in the form used for the blow-up. -/
theorem exists_sum_inv_succ_gt (C : ℝ) :
    ∃ N : ℕ, C < ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / ((j : ℝ) + 1) := by
  have htendsto := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hev := htendsto.eventually_gt_atTop (C + 1)
  obtain ⟨n0, hn0⟩ := hev.exists
  refine ⟨n0, ?_⟩
  have heq : ∑ j ∈ Finset.Icc 1 n0, (1 / ((j : ℝ) + 1))
      = (∑ i ∈ Finset.range (n0 + 1), (1 / ((i : ℝ) + 1))) - 1 := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub _ (by omega)]
    simp
  rw [heq]
  have hrange : ∑ i ∈ Finset.range n0, (1 / ((i:ℝ) + 1))
      ≤ ∑ i ∈ Finset.range (n0 + 1), (1 / ((i:ℝ) + 1)) := by
    rw [Finset.sum_range_succ]
    have : (0:ℝ) ≤ 1 / ((n0:ℝ) + 1) := by positivity
    linarith
  linarith [hn0, hrange]

end LionsC12

end
