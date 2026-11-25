module

public import LionsC12.Construction.Defs
public import LionsC12.Coefficient.Blocks
public import LionsC12.Coefficient.Support

/-!
# Proposition 3.3: sharpness within the Hölder scale

We show that the coefficient `𝔞 = 1 + ε β` is not `α`-Hölder continuous in time for any
`1/2 < α < 1`, by exhibiting, inside each block `I_j`, two times `t`, `t + h` in the middle
third `J_j` with

* `h = π / (2 K_{j,1}²)`,
* `|β(t + h, 0) - β(t, 0)| ≥ 13 / (15 K_{j,1})`.

Compared with the paper we evaluate at the single point `x = 0` (where `cos (K x) = 1` for all
modes) instead of testing against the Fourier coefficient `Λ_K`; the lacunarity of the
frequencies makes the higher modes a geometrically small perturbation of the first one.

Since `h ^ α = (π / (2 K²)) ^ α`, the resulting Hölder quotient is bounded below by a constant
times `K ^ (2α - 1) → ∞`, which gives `not_holder`.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ### Arithmetic preliminaries -/

theorem K_one_nat (j : ℕ) : K j 1 = 256 * j * (j + 1) := by
  unfold K
  norm_num

theorem K_one_cast (j : ℕ) : (K j 1 : ℝ) = 256 * (j : ℝ) * ((j : ℝ) + 1) := by
  rw [K_one_nat]
  push_cast
  ring

/-- Any block index is dominated by its first frequency. -/
theorem le_K_one (j : ℕ) : (j : ℝ) ≤ (K j 1 : ℝ) := by
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  rw [K_one_cast]
  nlinarith [hj0]

/-- Choice of an integer multiple of `π / X` inside the middle third `[L/3, 2L/3]`, together with
a further half step `π / (2X)`.  This is the arithmetic core of the choice of `t_j` in the paper:
it only needs `9π ≤ 2 X L`, which for `X = K_{j,1}²` and `L = ℓ_j` holds with room to spare. -/
theorem exists_nat_step {X L : ℝ} (hX : 0 < X) (hL : 0 < L) (hXL : 9 * π ≤ 2 * X * L) :
    ∃ n : ℕ, L / 3 ≤ (n : ℝ) * π / X ∧ (n : ℝ) * π / X + π / (2 * X) ≤ 2 * L / 3 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hden : (0 : ℝ) < 3 * π := by positivity
  have hXne : X ≠ 0 := ne_of_gt hX
  have hπne : π ≠ 0 := ne_of_gt hπ
  refine ⟨⌈X * L / (3 * π)⌉₊, ?_, ?_⟩
  · rw [le_div_iff₀ hX]
    have h := Nat.le_ceil (X * L / (3 * π))
    rw [div_le_iff₀ hden] at h
    linarith
  · have hX2 : (0 : ℝ) < 2 * X := by linarith
    refine le_of_mul_le_mul_right ?_ hX2
    have e1 : ((⌈X * L / (3 * π)⌉₊ : ℝ) * π / X + π / (2 * X)) * (2 * X)
        = 2 * (⌈X * L / (3 * π)⌉₊ : ℝ) * π + π := by
      field_simp
    rw [e1]
    have h : (⌈X * L / (3 * π)⌉₊ : ℝ) < X * L / (3 * π) + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hX.le hL.le) hden.le)
    have h3 : (⌈X * L / (3 * π)⌉₊ : ℝ) * (3 * π) < (X * L / (3 * π) + 1) * (3 * π) :=
      mul_lt_mul_of_pos_right h hden
    have h4 : (X * L / (3 * π) + 1) * (3 * π) = X * L + 3 * π := by
      field_simp
    rw [h4] at h3
    linarith

/-! ### The coefficient at `x = 0` -/

/-- On the middle third of a block, `β(t, 0)` is the plain sum of the mode amplitudes:
`cos (K_{j,m} · 0) = 1` and `η_j(t) = 1` there. -/
theorem β_at_zero_of_mem_J {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ J j) :
    β D t 0 = ∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹ * sin (θ j m t) := by
  rw [β_eq_block D (J_subset_I hj ht) 0]
  simp only [βblock, βmode, mul_zero, Real.cos_zero, mul_one,
    ηj_eq_one_of_mem_J D hj ht, one_mul]

/-- The modes `m ≥ 2` of the block `j` carry at most `1/15` of the first amplitude. -/
theorem sum_erase_K_inv_le {j : ℕ} (hj : 1 ≤ j) :
    ∑ m ∈ (Finset.Icc 1 (M j)).erase 1, ((K j m : ℝ))⁻¹ ≤ ((K j 1 : ℝ))⁻¹ / 15 := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 (M j) := Finset.mem_Icc.mpr ⟨le_rfl, hj⟩
  have hsum : (∑ m ∈ (Finset.Icc 1 (M j)).erase 1, ((K j m : ℝ))⁻¹) + ((K j 1 : ℝ))⁻¹
      = ∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹ :=
    Finset.sum_erase_add _ _ h1
  have hSdef : S j = ∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹ := rfl
  have hS : S j ≤ ℓ j / 15 := S_le hj
  have hK1 : ((K j 1 : ℝ))⁻¹ = ℓ j / 16 := by
    rw [K_inv_eq hj]
    norm_num
  linarith

/-! ### The lower bound -/

/-- Lower bound at `x = 0` on the middle third: for `j ≥ 1` there are `t, t + h ∈ J j` with
`h = π / (2 K_{j,1}²)` and `|β(t+h,0) - β(t,0)| ≥ 13 / (15 K_{j,1})`. -/
theorem exists_pair_lower_bound {j : ℕ} (hj : 1 ≤ j) :
    ∃ t h : ℝ, 0 < h ∧ t ∈ J j ∧ t + h ∈ J j ∧ h = π / (2 * (K j 1 : ℝ) ^ 2) ∧
      13 / (15 * (K j 1 : ℝ)) ≤ |β D (t + h) 0 - β D t 0| := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπ4 : π ≤ 4 := Real.pi_le_four
  have hx512 : (512 : ℝ) ≤ (K j 1 : ℝ) := by exact_mod_cast K_ge hj le_rfl
  have hx0 : (0 : ℝ) < (K j 1 : ℝ) := by linarith
  have hxne : (K j 1 : ℝ) ≠ 0 := ne_of_gt hx0
  have hxsq : (0 : ℝ) < (K j 1 : ℝ) ^ 2 := pow_pos hx0 2
  have hℓ0 : 0 < ℓ j := ℓ_pos hj
  have hxℓ : (K j 1 : ℝ) * ℓ j = 16 := by
    simpa using K_mul_ℓ (j := j) (m := 1) hj
  have hℓx2 : (K j 1 : ℝ) ^ 2 * ℓ j = 16 * (K j 1 : ℝ) := by
    linear_combination (K j 1 : ℝ) * hxℓ
  -- choose the integer `n`
  obtain ⟨n, hn1, hn2⟩ :=
    exists_nat_step (X := (K j 1 : ℝ) ^ 2) (L := ℓ j) hxsq hℓ0 (by linarith)
  obtain ⟨t₀, ht₀⟩ : ∃ t : ℝ, t = τ j + (n : ℝ) * π / (K j 1 : ℝ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨h₀, hh₀⟩ : ∃ h : ℝ, h = π / (2 * (K j 1 : ℝ) ^ 2) := ⟨_, rfl⟩
  have hhalf : (0 : ℝ) < π / (2 * (K j 1 : ℝ) ^ 2) := div_pos hπ (by linarith)
  have hh0 : 0 < h₀ := by rw [hh₀]; exact hhalf
  have hcancel : ∀ c : ℝ, (K j 1 : ℝ) ^ 2 * (c / (K j 1 : ℝ) ^ 2) = c := by
    intro c
    field_simp
  -- both times lie in the middle third
  have hJ1 : t₀ ∈ J j := by
    have h1 : τ j + ℓ j / 3 ≤ t₀ := by rw [ht₀]; linarith
    have h2 : t₀ ≤ τ j + 2 * ℓ j / 3 := by rw [ht₀]; linarith
    exact Set.mem_Icc.mpr ⟨h1, h2⟩
  have hJ2 : t₀ + h₀ ∈ J j := by
    have h1 : τ j + ℓ j / 3 ≤ t₀ + h₀ := by rw [ht₀, hh₀]; linarith
    have h2 : t₀ + h₀ ≤ τ j + 2 * ℓ j / 3 := by rw [ht₀, hh₀]; linarith
    exact Set.mem_Icc.mpr ⟨h1, h2⟩
  -- the two phases of the first mode
  have hx2t : (K j 1 : ℝ) ^ 2 * (t₀ - τ j) = (n : ℝ) * π := by
    rw [ht₀, show τ j + (n : ℝ) * π / (K j 1 : ℝ) ^ 2 - τ j
        = (n : ℝ) * π / (K j 1 : ℝ) ^ 2 from by ring]
    exact hcancel ((n : ℝ) * π)
  have hx2h : (K j 1 : ℝ) ^ 2 * h₀ = π / 2 := by
    rw [hh₀, ← div_div]
    exact hcancel (π / 2)
  have hθ1 : θ j 1 t₀ = (n : ℝ) * π := hx2t
  have hθ2 : θ j 1 (t₀ + h₀) = (n : ℝ) * π + π / 2 := by
    show (K j 1 : ℝ) ^ 2 * (t₀ + h₀ - τ j) = (n : ℝ) * π + π / 2
    rw [show t₀ + h₀ - τ j = (t₀ - τ j) + h₀ from by ring, mul_add, hx2t, hx2h]
  refine ⟨t₀, h₀, hh0, hJ1, hJ2, hh₀, ?_⟩
  -- the difference is a single sum over the modes
  have hsum : β D (t₀ + h₀) 0 - β D t₀ 0
      = ∑ m ∈ Finset.Icc 1 (M j),
          ((K j m : ℝ))⁻¹ * (sin (θ j m (t₀ + h₀)) - sin (θ j m t₀)) := by
    rw [β_at_zero_of_mem_J D hj hJ2, β_at_zero_of_mem_J D hj hJ1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 (M j) := Finset.mem_Icc.mpr ⟨le_rfl, hj⟩
  have hsplit : ((K j 1 : ℝ))⁻¹ * (sin (θ j 1 (t₀ + h₀)) - sin (θ j 1 t₀))
      + ∑ m ∈ (Finset.Icc 1 (M j)).erase 1,
          ((K j m : ℝ))⁻¹ * (sin (θ j m (t₀ + h₀)) - sin (θ j m t₀))
      = ∑ m ∈ Finset.Icc 1 (M j),
          ((K j m : ℝ))⁻¹ * (sin (θ j m (t₀ + h₀)) - sin (θ j m t₀)) :=
    Finset.add_sum_erase _
      (fun m => ((K j m : ℝ))⁻¹ * (sin (θ j m (t₀ + h₀)) - sin (θ j m t₀))) h1mem
  -- the first mode contributes exactly `K⁻¹`
  have hfirst : |((K j 1 : ℝ))⁻¹ * (sin (θ j 1 (t₀ + h₀)) - sin (θ j 1 t₀))|
      = ((K j 1 : ℝ))⁻¹ := by
    rw [hθ1, hθ2, Real.sin_nat_mul_pi, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi, sub_zero,
      abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((K j 1 : ℝ))⁻¹), abs_neg_one_pow,
      mul_one]
  -- the remaining modes are geometrically small
  have htail : |∑ m ∈ (Finset.Icc 1 (M j)).erase 1,
      ((K j m : ℝ))⁻¹ * (sin (θ j m (t₀ + h₀)) - sin (θ j m t₀))|
      ≤ 2 * (((K j 1 : ℝ))⁻¹ / 15) := by
    have hstep : ∀ m ∈ (Finset.Icc 1 (M j)).erase 1,
        |((K j m : ℝ))⁻¹ * (sin (θ j m (t₀ + h₀)) - sin (θ j m t₀))|
          ≤ 2 * ((K j m : ℝ))⁻¹ := by
      intro m _
      have hpos : (0 : ℝ) ≤ ((K j m : ℝ))⁻¹ := by positivity
      rw [abs_mul, abs_of_nonneg hpos]
      have hb : |sin (θ j m (t₀ + h₀)) - sin (θ j m t₀)| ≤ 2 := by
        rw [abs_le]
        constructor
        · linarith [Real.neg_one_le_sin (θ j m (t₀ + h₀)), Real.sin_le_one (θ j m t₀)]
        · linarith [Real.sin_le_one (θ j m (t₀ + h₀)), Real.neg_one_le_sin (θ j m t₀)]
      have := mul_le_mul_of_nonneg_left hb hpos
      linarith
    calc |∑ m ∈ (Finset.Icc 1 (M j)).erase 1,
            ((K j m : ℝ))⁻¹ * (sin (θ j m (t₀ + h₀)) - sin (θ j m t₀))|
        ≤ ∑ m ∈ (Finset.Icc 1 (M j)).erase 1,
            |((K j m : ℝ))⁻¹ * (sin (θ j m (t₀ + h₀)) - sin (θ j m t₀))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ (Finset.Icc 1 (M j)).erase 1, 2 * ((K j m : ℝ))⁻¹ :=
          Finset.sum_le_sum hstep
      _ = 2 * ∑ m ∈ (Finset.Icc 1 (M j)).erase 1, ((K j m : ℝ))⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ 2 * (((K j 1 : ℝ))⁻¹ / 15) := by
          have := sum_erase_K_inv_le hj
          linarith
  -- combine the two contributions
  have hlow : ((K j 1 : ℝ))⁻¹ - 2 * (((K j 1 : ℝ))⁻¹ / 15)
      ≤ |β D (t₀ + h₀) 0 - β D t₀ 0| := by
    rw [hsum, ← hsplit]
    have habs := abs_sub_abs_le_abs_sub
      (((K j 1 : ℝ))⁻¹ * (sin (θ j 1 (t₀ + h₀)) - sin (θ j 1 t₀)))
      (-∑ m ∈ (Finset.Icc 1 (M j)).erase 1,
        ((K j m : ℝ))⁻¹ * (sin (θ j m (t₀ + h₀)) - sin (θ j m t₀)))
    rw [abs_neg, sub_neg_eq_add, hfirst] at habs
    linarith
  have hconv : 13 / (15 * (K j 1 : ℝ)) = ((K j 1 : ℝ))⁻¹ - 2 * (((K j 1 : ℝ))⁻¹ / 15) := by
    have e : ((K j 1 : ℝ))⁻¹ - 2 * (((K j 1 : ℝ))⁻¹ / 15) = 13 / 15 * ((K j 1 : ℝ))⁻¹ := by
      ring
    rw [e, ← div_div, div_eq_mul_inv]
  rw [hconv]
  exact hlow

/-! ### Proposition 3.3 -/

/-- Proposition 3.3: for every `1/2 < α < 1` and every `C` the `α`-Hölder quotient of
`𝔞(·, 0)` is unbounded on `[0,1]`. -/
theorem not_holder {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (C : ℝ) :
    ∃ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧ t ∈ Set.Icc (0 : ℝ) 1 ∧ s ≠ t ∧
      C * |t - s| ^ α < |a D ε t 0 - a D ε s 0| := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  obtain ⟨δ, hδdef⟩ : ∃ d : ℝ, d = 2 * α - 1 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδ2 : (2 : ℝ) * α = δ + 1 := by rw [hδdef]; ring
  have hcoef : (0 : ℝ) < 13 * ε * 2 ^ α :=
    mul_pos (by linarith : (0 : ℝ) < 13 * ε) (Real.rpow_pos_of_pos (by norm_num) α)
  -- choose a block index with a very large first frequency
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hδ).eventually_gt_atTop (15 * C * π ^ α / (13 * ε * 2 ^ α)))
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = max 1 ⌈N⌉₊ := ⟨_, rfl⟩
  have hj : 1 ≤ j := by rw [hjdef]; exact le_max_left _ _
  have hjN : N ≤ (j : ℝ) := by
    have h1 : ⌈N⌉₊ ≤ j := by rw [hjdef]; exact le_max_right _ _
    exact (Nat.le_ceil N).trans (Nat.cast_le.mpr h1)
  have hxδ : 15 * C * π ^ α / (13 * ε * 2 ^ α) < (K j 1 : ℝ) ^ δ :=
    hN _ (hjN.trans (le_K_one j))
  -- the pair of times supplied by the block construction
  obtain ⟨t₀, h₀, hh0, hJ1, hJ2, hheq, hlb⟩ := exists_pair_lower_bound D hj
  have hx512 : (512 : ℝ) ≤ (K j 1 : ℝ) := by exact_mod_cast K_ge hj le_rfl
  have hx0 : (0 : ℝ) < (K j 1 : ℝ) := by linarith
  have hmem : ∀ {s : ℝ}, s ∈ J j → s ∈ Set.Icc (0 : ℝ) 1 := by
    intro s hs
    have h := I_subset hj (J_subset_I hj hs)
    rw [Set.mem_Icc] at h ⊢
    exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  refine ⟨t₀, t₀ + h₀, hmem hJ1, hmem hJ2, by intro hEq; linarith, ?_⟩
  -- the increment
  have hdist : |t₀ + h₀ - t₀| = h₀ := by
    rw [show t₀ + h₀ - t₀ = h₀ by ring]
    exact abs_of_pos hh0
  rw [hdist]
  -- the coefficient difference
  have hRHS : |a D ε (t₀ + h₀) 0 - a D ε t₀ 0| = ε * |β D (t₀ + h₀) 0 - β D t₀ 0| := by
    have e : a D ε (t₀ + h₀) 0 - a D ε t₀ 0 = ε * (β D (t₀ + h₀) 0 - β D t₀ 0) := by
      simp only [a]; ring
    rw [e, abs_mul, abs_of_pos hε]
  rw [hRHS]
  have hstep1 : ε * (13 / (15 * (K j 1 : ℝ))) ≤ ε * |β D (t₀ + h₀) 0 - β D t₀ 0| :=
    mul_le_mul_of_nonneg_left hlb (le_of_lt hε)
  refine lt_of_lt_of_le ?_ hstep1
  -- rewrite the power of the increment
  have hsqrpow : ((K j 1 : ℝ) ^ 2) ^ α = (K j 1 : ℝ) ^ δ * (K j 1 : ℝ) := by
    rw [← Real.rpow_two (K j 1 : ℝ), ← Real.rpow_mul (le_of_lt hx0), hδ2, Real.rpow_add hx0,
      Real.rpow_one]
  have hpow : h₀ ^ α = π ^ α / (2 ^ α * ((K j 1 : ℝ) ^ δ * (K j 1 : ℝ))) := by
    rw [hheq, Real.div_rpow Real.pi_nonneg (show (0 : ℝ) ≤ 2 * (K j 1 : ℝ) ^ 2 by positivity),
      Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num)
        (show (0 : ℝ) ≤ (K j 1 : ℝ) ^ 2 by positivity), hsqrpow]
  rw [hpow]
  have hpos1 : (0 : ℝ) < 2 ^ α * ((K j 1 : ℝ) ^ δ * (K j 1 : ℝ)) :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) α)
      (mul_pos (Real.rpow_pos_of_pos hx0 δ) hx0)
  have hpos2 : (0 : ℝ) < 15 * (K j 1 : ℝ) := by linarith
  rw [← mul_div_assoc, ← mul_div_assoc, div_lt_div_iff₀ hpos1 hpos2]
  -- what remains is `15 C π^α K < 13 ε 2^α K^δ K`
  rw [div_lt_iff₀ hcoef] at hxδ
  have hfin := mul_lt_mul_of_pos_right hxδ hx0
  linarith

end LionsC12

end
