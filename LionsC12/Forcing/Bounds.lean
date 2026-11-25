module

public import LionsC12.Coefficient.Holder
public import LionsC12.Forcing.Continuity
public import LionsC12.Forcing.Elliptic
public import LionsC12.Solution.L1

/-!
# Uniform bounds and the time support of the construction

* every block lies in `(1/8, 7/8)`, so `ρ'`, `v` and `∂ₜu` vanish outside that interval
  (`notMem_I_of_time`, `ρ'_eq_zero_of_time`, `v_eq_zero_of_time`, `ut_eq_zero_of_time`);
* the uniform bounds `|v| ≤ |ε|`, `|∂ₓv| ≤ ε`, `|u|, |∂ₓu| ≤ 2` and `|𝔞| ≤ 481/480` for
  `0 ≤ ε ≤ 1` (`abs_v_le`, `abs_vx_le`, `abs_u_le`, `abs_ux_le`, `abs_a_le`);
* `‖∂ₜu(t)‖²_H ≤ (1 + ε²)‖∂ₜu(t)‖²_H|_{ε=1}` and hence `∂ₜu ∈ L¹(0,1;H)` for every real `ε`
  (`utNormSq_le_utNormSq_one`, `integrableOn_sqrt_utNormSq'`).
-/

@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ## The time support -/

/-- All blocks live inside `(1/8, 7/8)`. -/
theorem notMem_I_of_time {t : ℝ} (ht : t ∉ Set.Ioo (1 / 8 : ℝ) (7 / 8)) (j : ℕ) : t ∉ I j := by
  intro hmem
  have hj : 1 ≤ j := one_le_of_mem_I hmem
  have h := I_subset hj hmem
  exact ht ⟨by linarith [h.1], by linarith [h.2]⟩

theorem ρ'_eq_zero_of_time {t : ℝ} (ht : t ∉ Set.Ioo (1 / 8 : ℝ) (7 / 8)) : D.ρ' t = 0 := by
  by_contra h; exact ht (D.ρ'_supp t h)

theorem ut_eq_zero_of_time (ε : ℝ) {t : ℝ} (ht : t ∉ Set.Ioo (1 / 8 : ℝ) (7 / 8)) (x : ℝ) :
    ut D ε t x = 0 := by
  rw [ut, ρ'_eq_zero_of_time D ht, vt_eq_zero D ε (notMem_I_of_time ht) x]
  ring

theorem v_eq_zero_of_time (ε : ℝ) {t : ℝ} (ht : t ∉ Set.Ioo (1 / 8 : ℝ) (7 / 8)) (x : ℝ) :
    v D ε t x = 0 := v_eq_zero D ε (notMem_I_of_time ht) x

/-! ## Uniform bounds -/

/-- `|v| ≤ |ε|` globally (the oscillation lives in `[1/4, 5/16]`). -/
theorem abs_v_le (ε t x : ℝ) : |v D ε t x| ≤ |ε| := by
  by_cases ht : t ∈ Set.Ioo (1 / 8 : ℝ) (7 / 8)
  · have h := abs_v_le_dist' D ε t x
    have hd : |t - 5 / 16| ≤ 1 := by
      rw [abs_le]; constructor <;> [linarith [ht.1]; linarith [ht.2]]
    have hd0 : 0 ≤ |t - 5 / 16| := abs_nonneg _
    have hsq : |t - 5 / 16| ^ 2 ≤ 1 := by nlinarith
    calc |v D ε t x| ≤ |ε| * |t - 5 / 16| ^ 2 := h
      _ ≤ |ε| * 1 := mul_le_mul_of_nonneg_left hsq (abs_nonneg ε)
      _ = |ε| := by ring
  · rw [v_eq_zero_of_time D ε ht x, abs_zero]
    exact abs_nonneg ε

/-- `|∂_x v| ≤ ε` globally for `0 ≤ ε`. -/
theorem abs_vx_le {ε : ℝ} (hε0 : 0 ≤ ε) (t x : ℝ) : |vx D ε t x| ≤ ε := by
  rcases mem_block_or_not t with ⟨j, hj⟩ | h
  · have hj1 : 1 ≤ j := one_le_of_mem_I hj
    rw [vx_eq_block D ε hj x]
    have h1 := abs_vxblock_le D hε0 hj1 t x
    have h2 := S_le hj1
    have h3 := ℓ_le hj1
    have h4 := S_nonneg j
    nlinarith
  · rw [vx_eq_zero D ε h x, abs_zero]; exact hε0

theorem abs_u_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t x : ℝ) : |u D ε t x| ≤ 2 := by
  have h1 : |D.ρ t * φ x| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_ρ_le_one D t, abs_φ_le_one x, abs_nonneg (D.ρ t), abs_nonneg (φ x)]
  have h2 : |v D ε t x| ≤ ε := by
    have h := abs_v_le D ε t x
    rwa [abs_of_nonneg hε0] at h
  have h3 : |u D ε t x| ≤ |D.ρ t * φ x| + |v D ε t x| := abs_add_le _ _
  linarith

theorem abs_ux_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t x : ℝ) : |ux D ε t x| ≤ 2 := by
  have h1 : |D.ρ t * φ' x| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_ρ_le_one D t, abs_φ'_le_one x, abs_nonneg (D.ρ t), abs_nonneg (φ' x)]
  have h2 : |vx D ε t x| ≤ ε := abs_vx_le D hε0 t x
  have h3 : |ux D ε t x| ≤ |D.ρ t * φ' x| + |vx D ε t x| := abs_add_le _ _
  linarith

theorem abs_a_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t x : ℝ) : |a D ε t x| ≤ 481 / 480 := by
  have h1 := a_ge D hε0 hε1 t x
  have h2 := a_le D hε0 hε1 t x
  rw [abs_le]; constructor <;> linarith

/-! ## The time derivative for every real `ε` -/

private lemma y'_smul (ε : ℝ) (j m : ℕ) (t : ℝ) : y' D ε j m t = ε * y' D 1 j m t := by
  simp only [y']; ring

/-- The `ε`-scaling of `‖∂_t u(t)‖²_H`, valid for every real `ε` (also negative). -/
theorem utNormSq_le_utNormSq_one (ε t : ℝ) : utNormSq D ε t ≤ (1 + ε ^ 2) * utNormSq D 1 t := by
  rcases mem_block_or_not t with ⟨j, hj⟩ | h
  · rw [utNormSq_of_mem_I D ε hj, utNormSq_of_mem_I D 1 hj]
    have hsum : (∑ m ∈ Finset.Icc 1 (M j), (y' D ε j m t) ^ 2)
        = ε ^ 2 * ∑ m ∈ Finset.Icc 1 (M j), (y' D 1 j m t) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [y'_smul D ε j m t]; ring
    rw [hsum]
    have hnn : 0 ≤ ∑ m ∈ Finset.Icc 1 (M j), (y' D 1 j m t) ^ 2 :=
      Finset.sum_nonneg fun m _ => sq_nonneg _
    nlinarith [Real.pi_pos, sq_nonneg ε]
  · rw [utNormSq_of_notMem D ε h, utNormSq_of_notMem D 1 h]
    have hX : 0 ≤ D.ρ' t ^ 2 * normSq φ := mul_nonneg (sq_nonneg _) (normSq_nonneg φ)
    nlinarith [sq_nonneg ε, hX]

/-- `∂_t u ∈ L¹(0,1;H)` for every real `ε` (`integrableOn_sqrt_utNormSq` needs `0 ≤ ε`). -/
theorem integrableOn_sqrt_utNormSq' (ε : ℝ) :
    MeasureTheory.IntegrableOn (fun t => Real.sqrt (utNormSq D ε t)) (Set.Icc (0 : ℝ) 1) := by
  have hbase : MeasureTheory.IntegrableOn (fun t => Real.sqrt (utNormSq D 1 t))
      (Set.Icc (0 : ℝ) 1) := integrableOn_sqrt_utNormSq D zero_le_one
  refine MeasureTheory.Integrable.mono' (hbase.const_mul (Real.sqrt (1 + ε ^ 2)))
    (Real.continuous_sqrt.comp_aestronglyMeasurable (aestronglyMeasurable_utNormSq D ε)) ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt (utNormSq D ε t) ≤ Real.sqrt ((1 + ε ^ 2) * utNormSq D 1 t) :=
        Real.sqrt_le_sqrt (utNormSq_le_utNormSq_one D ε t)
    _ = Real.sqrt (1 + ε ^ 2) * Real.sqrt (utNormSq D 1 t) := Real.sqrt_mul (by positivity) _

end LionsC12
