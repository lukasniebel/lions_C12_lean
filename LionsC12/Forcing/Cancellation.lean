module

public import LionsC12.Construction.Defs
public import LionsC12.Coefficient.Blocks
public import LionsC12.Coefficient.Support
public import LionsC12.Modes.Trig
public import LionsC12.Solution.Basic

/-!
# Section 5 of the paper: cancellation, the PDE, and the bounded forcing

This file contains

* `mode_cancellation` : the modewise cancellation (5.2)/(5.4);
* `block_identity`    : its sum over the modes of one block;
* `pde`               : the pointwise identity `∂_t u + 𝒜(t) u = f`;
* the uniform bounds on `f0`, `E`, `Rblock`, `vxblock`, `vxxblock`, `βxblock`, `Lβv`
  culminating in `abs_f_le : |f| ≤ Cf D`.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ## The modewise cancellation -/

/-- Modewise cancellation, equation (5.2)/(5.4): for the `(j,m)`-mode, with `K = K j m`,
`y' p_K - y p_K'' + ε ρ · (η_j sin θ) · (p_K - 2K⁻¹ c_K) = E_{j,m}`. -/
theorem mode_cancellation (ε : ℝ) {j : ℕ} (hj : 1 ≤ j) (m : ℕ) (t x : ℝ) :
    y' D ε j m t * p (K j m) x - y D ε j m t * p'' (K j m) x
      + ε * ηj D j t * sin (θ j m t) * (p (K j m) x - 2 * ((K j m : ℝ))⁻¹ * c (K j m) x)
      = E D ε j m t x := by
  have hK : ((K j m : ℝ)) ≠ 0 := (Nat.cast_pos.2 (K_pos hj)).ne'
  simp only [E, p'', y', y, r]
  field_simp
  ring

/-! ## The block identity -/

/-- Blockwise: for every `t` (in particular for `t ∈ I j`),
`vtblock - vxxblock - ε (βxblock · φ' + βblock · φ'') = Rblock`. -/
theorem block_identity (ε : ℝ) {j : ℕ} (hj : 1 ≤ j) (t x : ℝ) :
    vtblock D ε j t x - vxxblock D ε j t x - ε * (βxblock D j t x * φ' x + βblock D j t x * φ'' x)
      = Rblock D ε j t x := by
  have hterm : ∀ m ∈ Finset.Icc 1 (M j),
      y' D ε j m t * p (K j m) x - y D ε j m t * p'' (K j m) x
        - ε * ((-(ηj D j t * sin (θ j m t) * sin (K j m * x))) * φ' x
              + βmode D j m t x * φ'' x)
        = E D ε j m t x := by
    intro m _
    have hmc := mode_cancellation D ε hj m t x
    rw [← hmc]
    simp only [βmode]
    simp only [φ', φ'', p, c]
    ring
  have h1 : Rblock D ε j t x
      = ∑ m ∈ Finset.Icc 1 (M j),
        (y' D ε j m t * p (K j m) x - y D ε j m t * p'' (K j m) x
          - ε * ((-(ηj D j t * sin (θ j m t) * sin (K j m * x))) * φ' x
                + βmode D j m t x * φ'' x)) := by
    simp only [Rblock]
    exact (Finset.sum_congr rfl hterm).symm
  rw [h1]
  simp only [vtblock, vxxblock, βxblock, βblock]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]

/-! ## The partial differential equation -/

/-- The equation `∂_t u + 𝒜(t) u = f` holds pointwise for all `t, x`. -/
theorem pde (ε : ℝ) (t x : ℝ) : ut D ε t x + Au D ε t x = f D ε t x := by
  by_cases hex : ∃ j, t ∈ I j
  · obtain ⟨j, htj⟩ := hex
    have hj1 : 1 ≤ j := one_le_of_mem_I htj
    have hρ : D.ρ t = 1 := ρ_eq_one_of_mem_I D htj
    have hρ' : D.ρ' t = 0 := ρ'_eq_zero_of_mem_I D htj
    have hbi := block_identity D ε hj1 t x
    simp only [ut, Au, f, f0, Lβv, a, ux, uxx, vt_eq_block D ε htj, vx_eq_block D ε htj,
      vxx_eq_block D ε htj, β_eq_block D htj, βx_eq_block D htj, R_eq_block D ε htj, hρ, hρ']
    linear_combination hbi
  · rw [not_exists] at hex
    simp only [ut, Au, f, f0, Lβv, a, ux, uxx, vt_eq_zero D ε hex, vx_eq_zero D ε hex,
      vxx_eq_zero D ε hex, β_eq_zero D hex, βx_eq_zero D hex, R_eq_zero D ε hex]
    ring

/-! ## Bounds -/

theorem abs_f0_le (t x : ℝ) : |f0 D t x| ≤ D.Cρ + 2 := by
  have h1 : |D.ρ' t * φ x| ≤ D.Cρ * 1 := abs_mul_le_mul (D.ρ'_bound t) (abs_φ_le_one x)
  have h2 : |D.ρ t * φ'' x| ≤ 1 * 2 := abs_mul_le_mul (abs_ρ_le_one D t) (abs_φ''_le x)
  calc |f0 D t x| = |D.ρ' t * φ x - D.ρ t * φ'' x| := by simp only [f0]
    _ ≤ |D.ρ' t * φ x| + |D.ρ t * φ'' x| := abs_sub _ _
    _ ≤ D.Cρ + 2 := by linarith

/-- Bound for the mode remainder `E_{j,m}`.  (Any explicit bound summing to a `j`-independent
constant would do; this one is convenient for `abs_Rblock_le`.) -/
theorem abs_E_le {ε : ℝ} (hε0 : 0 ≤ ε) {j : ℕ} (hj : 1 ≤ j) (m : ℕ) (t x : ℝ) :
    |E D ε j m t x| ≤ ε * D.Cη * (ℓ j)⁻¹ * ((K j m : ℝ))⁻¹ ^ 2
      + 4 * ε * ((K j m : ℝ))⁻¹ ^ 2 + 2 * ε * ((K j m : ℝ))⁻¹ := by
  have hK0 : (0 : ℝ) < (K j m : ℝ) := Nat.cast_pos.2 (K_pos hj)
  have hK : ((K j m : ℝ)) ≠ 0 := hK0.ne'
  have hℓ0 : 0 < ℓ j := ℓ_pos hj
  have hℓ : ℓ j ≠ 0 := hℓ0.ne'
  have hE : E D ε j m t x = (r D ε j m t + 4 * y D ε j m t) * p (K j m) x
      - (2 * ε * ((K j m : ℝ))⁻¹) * (ηj D j t * (cos (θ j m t) * c (K j m) x)) := by
    simp only [E]; ring
  have hA1 : |r D ε j m t + 4 * y D ε j m t|
      ≤ ε * D.Cη / ((K j m : ℝ) ^ 2 * ℓ j) + 4 * (ε / (K j m : ℝ) ^ 2) := by
    refine (abs_add_le _ _).trans ?_
    have h4 : |4 * y D ε j m t| = 4 * |y D ε j m t| := by
      rw [abs_mul]; norm_num
    rw [h4]
    have hr := abs_r_le D hε0 hj m t
    have hy := abs_y_le D hε0 hj m t
    linarith
  have hA : |(r D ε j m t + 4 * y D ε j m t) * p (K j m) x|
      ≤ (ε * D.Cη / ((K j m : ℝ) ^ 2 * ℓ j) + 4 * (ε / (K j m : ℝ) ^ 2)) * 1 :=
    abs_mul_le_mul hA1 (abs_p_le_one _ _)
  have hBnn : (0 : ℝ) ≤ 2 * ε * ((K j m : ℝ))⁻¹ :=
    mul_nonneg (by linarith) (inv_nonneg.mpr hK0.le)
  have hB : |(2 * ε * ((K j m : ℝ))⁻¹) * (ηj D j t * (cos (θ j m t) * c (K j m) x))|
      ≤ (2 * ε * ((K j m : ℝ))⁻¹) * 1 := by
    refine abs_mul_le_mul (le_of_eq (abs_of_nonneg hBnn)) ?_
    simpa using
      abs_mul_le_mul (abs_ηj_le_one D j t)
        (abs_mul_le_mul (Real.abs_cos_le_one _) (abs_c_le_one _ _))
  have efinal : (ε * D.Cη / ((K j m : ℝ) ^ 2 * ℓ j) + 4 * (ε / (K j m : ℝ) ^ 2)) * 1
      + (2 * ε * ((K j m : ℝ))⁻¹) * 1
      = ε * D.Cη * (ℓ j)⁻¹ * ((K j m : ℝ))⁻¹ ^ 2 + 4 * ε * ((K j m : ℝ))⁻¹ ^ 2
        + 2 * ε * ((K j m : ℝ))⁻¹ := by
    field_simp
  calc |E D ε j m t x|
      ≤ |(r D ε j m t + 4 * y D ε j m t) * p (K j m) x|
        + |(2 * ε * ((K j m : ℝ))⁻¹) * (ηj D j t * (cos (θ j m t) * c (K j m) x))| := by
        rw [hE]; exact abs_sub _ _
    _ ≤ (ε * D.Cη / ((K j m : ℝ) ^ 2 * ℓ j) + 4 * (ε / (K j m : ℝ) ^ 2)) * 1
        + (2 * ε * ((K j m : ℝ))⁻¹) * 1 := add_le_add hA hB
    _ = _ := efinal

theorem abs_Rblock_le {ε : ℝ} (hε0 : 0 ≤ ε) {j : ℕ} (hj : 1 ≤ j) (t x : ℝ) :
    |Rblock D ε j t x| ≤ ε * (D.Cη + 5) := by
  have hℓ0 : 0 < ℓ j := ℓ_pos hj
  have hℓne : ℓ j ≠ 0 := hℓ0.ne'
  have hℓ : ℓ j ≤ 1 / 32 := ℓ_le hj
  have hA : (0 : ℝ) ≤ ε * D.Cη * (ℓ j)⁻¹ + 4 * ε := by
    have h1 : (0 : ℝ) ≤ ε * D.Cη * (ℓ j)⁻¹ :=
      mul_nonneg (mul_nonneg hε0 D.Cη_nonneg) (inv_nonneg.mpr hℓ0.le)
    linarith
  have hkey : (ε * D.Cη * (ℓ j)⁻¹ + 4 * ε) * (ℓ j ^ 2 / 255) + 2 * ε * (ℓ j / 15)
      = ε * D.Cη * ℓ j / 255 + 4 * ε * ℓ j ^ 2 / 255 + 2 * ε * ℓ j / 15 := by
    field_simp
  have hℓ2 : ℓ j ^ 2 ≤ 1 / 1024 := by nlinarith
  have h1 : ε * D.Cη * ℓ j / 255 ≤ ε * D.Cη := by
    have hnn : (0 : ℝ) ≤ ε * D.Cη := mul_nonneg hε0 D.Cη_nonneg
    have := mul_le_mul_of_nonneg_left hℓ hnn
    linarith
  have h2 : 4 * ε * ℓ j ^ 2 / 255 ≤ ε := by
    have := mul_le_mul_of_nonneg_left hℓ2 hε0
    linarith
  have h3 : 2 * ε * ℓ j / 15 ≤ ε := by
    have := mul_le_mul_of_nonneg_left hℓ hε0
    linarith
  calc |Rblock D ε j t x| ≤ ∑ m ∈ Finset.Icc 1 (M j), |E D ε j m t x| := by
        simp only [Rblock]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 (M j), (ε * D.Cη * (ℓ j)⁻¹ * ((K j m : ℝ))⁻¹ ^ 2
          + 4 * ε * ((K j m : ℝ))⁻¹ ^ 2 + 2 * ε * ((K j m : ℝ))⁻¹) :=
        Finset.sum_le_sum fun m _ => abs_E_le D hε0 hj m t x
    _ = (ε * D.Cη * (ℓ j)⁻¹ + 4 * ε) * (∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹ ^ 2)
          + 2 * ε * S j := by
        simp only [S]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ (ε * D.Cη * (ℓ j)⁻¹ + 4 * ε) * (ℓ j ^ 2 / 255) + 2 * ε * (ℓ j / 15) := by
        have hs1 : (∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹ ^ 2) ≤ ℓ j ^ 2 / 255 :=
          sum_K_inv_sq_le hj
        have hs2 : S j ≤ ℓ j / 15 := S_le hj
        have hε2 : (0 : ℝ) ≤ 2 * ε := by linarith
        exact add_le_add (mul_le_mul_of_nonneg_left hs1 hA) (mul_le_mul_of_nonneg_left hs2 hε2)
    _ = ε * D.Cη * ℓ j / 255 + 4 * ε * ℓ j ^ 2 / 255 + 2 * ε * ℓ j / 15 := hkey
    _ ≤ ε * (D.Cη + 5) := by nlinarith

theorem abs_βxblock_le (j : ℕ) (t x : ℝ) : |βxblock D j t x| ≤ M j := by
  calc |βxblock D j t x|
      ≤ ∑ m ∈ Finset.Icc 1 (M j), |(-(ηj D j t * sin (θ j m t) * sin (K j m * x)))| := by
        simp only [βxblock]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 (M j), (1 : ℝ) := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [abs_neg]
        simpa using
          abs_mul_le_mul (abs_mul_le_mul (abs_ηj_le_one D j t) (Real.abs_sin_le_one _))
            (Real.abs_sin_le_one _)
    _ = M j := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]

theorem abs_vxblock_le {ε : ℝ} (hε0 : 0 ≤ ε) {j : ℕ} (hj : 1 ≤ j) (t x : ℝ) :
    |vxblock D ε j t x| ≤ 2 * ε * S j := by
  calc |vxblock D ε j t x| ≤ ∑ m ∈ Finset.Icc 1 (M j), |y D ε j m t * p' (K j m) x| := by
        simp only [vxblock]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 (M j), 2 * ε * ((K j m : ℝ))⁻¹ := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have hK2 : (2 : ℝ) < (K j m : ℝ) := by exact_mod_cast two_lt_K hj hm1
        have hK0 : (0 : ℝ) < (K j m : ℝ) := by linarith
        have hKne : ((K j m : ℝ)) ≠ 0 := hK0.ne'
        refine (abs_mul_le_mul (abs_y_le D hε0 hj m t) (abs_p'_le (K j m) x)).trans ?_
        have key : 2 * ε * ((K j m : ℝ))⁻¹ - ε / (K j m : ℝ) ^ 2 * ((K j m : ℝ) + 2)
            = ε * ((K j m : ℝ) - 2) / (K j m : ℝ) ^ 2 := by
          field_simp
          ring
        have hnn : 0 ≤ ε * ((K j m : ℝ) - 2) / (K j m : ℝ) ^ 2 :=
          div_nonneg (mul_nonneg hε0 (by linarith)) (by positivity)
        linarith
    _ = 2 * ε * S j := by simp only [S]; rw [Finset.mul_sum]

theorem abs_vxxblock_le {ε : ℝ} (hε0 : 0 ≤ ε) {j : ℕ} (hj : 1 ≤ j) (t x : ℝ) :
    |vxxblock D ε j t x| ≤ 2 * ε * M j := by
  calc |vxxblock D ε j t x| ≤ ∑ m ∈ Finset.Icc 1 (M j), |y D ε j m t * p'' (K j m) x| := by
        simp only [vxxblock]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 (M j), 2 * ε := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have hK512 : (512 : ℝ) ≤ (K j m : ℝ) := by exact_mod_cast K_ge hj hm1
        have hK0 : (0 : ℝ) < (K j m : ℝ) := by linarith
        have hKne : ((K j m : ℝ)) ≠ 0 := hK0.ne'
        refine (abs_mul_le_mul (abs_y_le D hε0 hj m t) (abs_p''_le (K j m) x)).trans ?_
        have key : 2 * ε - ε / (K j m : ℝ) ^ 2 * ((K j m : ℝ) ^ 2 + 4 * (K j m : ℝ) + 4)
            = ε * ((K j m : ℝ) ^ 2 - 4 * (K j m : ℝ) - 4) / (K j m : ℝ) ^ 2 := by
          field_simp
          ring
        have hnn : 0 ≤ ε * ((K j m : ℝ) ^ 2 - 4 * (K j m : ℝ) - 4) / (K j m : ℝ) ^ 2 :=
          div_nonneg (mul_nonneg hε0 (by nlinarith)) (by positivity)
        linarith
    _ = 2 * ε * M j := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

theorem abs_Lβv_le {ε : ℝ} (hε0 : 0 ≤ ε) (t x : ℝ) : |Lβv D ε t x| ≤ ε / 60 := by
  by_cases hex : ∃ j, t ∈ I j
  · obtain ⟨j, htj⟩ := hex
    have hj1 : 1 ≤ j := one_le_of_mem_I htj
    have hjr : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have h1 : |βxblock D j t x * vxblock D ε j t x| ≤ (M j : ℝ) * (2 * ε * S j) :=
      abs_mul_le_mul (abs_βxblock_le D j t x) (abs_vxblock_le D hε0 hj1 t x)
    have h2 : |βblock D j t x * vxxblock D ε j t x| ≤ S j * (2 * ε * (M j : ℝ)) :=
      abs_mul_le_mul (abs_βblock_le D hj1 t x) (abs_vxxblock_le D hε0 hj1 t x)
    have h3 : -(βxblock D j t x * vxblock D ε j t x) - βblock D j t x * vxxblock D ε j t x
        = -(βxblock D j t x * vxblock D ε j t x + βblock D j t x * vxxblock D ε j t x) := by
      ring
    have h4 : (M j : ℝ) * S j ≤ 1 / (240 * ((j : ℝ) + 1)) := M_mul_S_le hj1
    have h5 : 4 * ε * ((M j : ℝ) * S j) ≤ 4 * ε * (1 / (240 * ((j : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left h4 (by linarith)
    have h6 : ε / 60 - 4 * ε * (1 / (240 * ((j : ℝ) + 1)))
        = ε * (j : ℝ) / (60 * ((j : ℝ) + 1)) := by
      field_simp
      ring
    have h7 : (0 : ℝ) ≤ ε * (j : ℝ) / (60 * ((j : ℝ) + 1)) :=
      div_nonneg (mul_nonneg hε0 (Nat.cast_nonneg j)) (by positivity)
    simp only [Lβv]
    rw [β_eq_block D htj, βx_eq_block D htj, vx_eq_block D ε htj,
      vxx_eq_block D ε htj, h3, abs_neg]
    refine (abs_add_le _ _).trans ?_
    have h8 : (M j : ℝ) * (2 * ε * S j) + S j * (2 * ε * (M j : ℝ))
        = 4 * ε * ((M j : ℝ) * S j) := by ring
    linarith
  · rw [not_exists] at hex
    simp only [Lβv]
    rw [β_eq_zero D hex, βx_eq_zero D hex, vx_eq_zero D ε hex, vxx_eq_zero D ε hex]
    have h0 : -((0 : ℝ) * 0) - (0 : ℝ) * 0 = 0 := by ring
    rw [h0, abs_zero]
    linarith

theorem abs_R_le {ε : ℝ} (hε0 : 0 ≤ ε) (t x : ℝ) : |R D ε t x| ≤ ε * (D.Cη + 5) := by
  by_cases hex : ∃ j, t ∈ I j
  · obtain ⟨j, htj⟩ := hex
    have hj1 : 1 ≤ j := one_le_of_mem_I htj
    rw [R_eq_block D ε htj]
    exact abs_Rblock_le D hε0 hj1 t x
  · rw [not_exists] at hex
    rw [R_eq_zero D ε hex, abs_zero]
    have := D.Cη_nonneg
    exact mul_nonneg hε0 (by linarith)

/-- The constant bounding the forcing. -/
def Cf : ℝ := D.Cρ + 2 + (D.Cη + 5) + 1 / 60

theorem abs_f_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t x : ℝ) : |f D ε t x| ≤ Cf D := by
  have h0 := abs_f0_le D t x
  have hR := abs_R_le D hε0 t x
  have hL := abs_Lβv_le D hε0 t x
  have hRε : ε * (D.Cη + 5) ≤ D.Cη + 5 := by
    have := D.Cη_nonneg
    nlinarith
  have hεL : |ε * Lβv D ε t x| ≤ 1 / 60 := by
    rw [abs_mul, abs_of_nonneg hε0]
    calc ε * |Lβv D ε t x| ≤ ε * (ε / 60) := mul_le_mul_of_nonneg_left hL hε0
      _ ≤ 1 / 60 := by nlinarith
  calc |f D ε t x| ≤ |f0 D t x| + |R D ε t x| + |ε * Lβv D ε t x| := by
        simp only [f]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ D.Cρ + 2 + (D.Cη + 5) + 1 / 60 := by linarith
    _ = Cf D := by simp only [Cf]

end LionsC12

end
