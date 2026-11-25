module

public import LionsC12.Construction.Defs
public import LionsC12.Coefficient.Blocks

/-!
# Supports of the cutoffs, active blocks, and the `finsum` reductions

This file collects

* the elementary properties of the rescaled cutoffs `η_j`, `η_j'` (bounds, support,
  the value on the middle third `J_j`, differentiability, continuity and the Lipschitz
  estimate), and the vanishing of all of them near the block endpoints `τ_j`
  (`core_bounds`, `ηj_eq_zero_near_τ`, `ηj'_eq_zero_near_τ`, `eventually_ηj_zero_at_τ`);
* the properties of the global cutoff `ρ` used later;
* the fact that every block quantity vanishes outside its time interval `I_j`, and where
  the cutoffs vanish;
* the bounds `abs_βmode_le`, `abs_βblock_le` on the blocks of the perturbation `β`;
* the fact that at each time at most one block is active, and the resulting
  reduction of the `finsum`s defining `β`, `∂_x β`, `v`, `∂_t v`, `∂_x v`, `∂_x² v`, `R`
  to a single block.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ## The rescaled cutoffs `η_j` -/

theorem ηj_zero_block (t : ℝ) : ηj D 0 t = 0 := by
  have h0 : ηj D 0 t = D.η 0 := by
    show D.η ((t - τ 0) / ℓ 0) = D.η 0
    rw [ℓ_zero, div_zero]
  rw [h0]
  by_contra hne
  have hmem := D.η_supp 0 hne
  have h1 : (1 : ℝ) / 10 < 0 := (Set.mem_Ioo.1 hmem).1
  norm_num at h1

theorem ηj'_zero_block (t : ℝ) : ηj' D 0 t = 0 := by
  show D.η' ((t - τ 0) / ℓ 0) / ℓ 0 = 0
  rw [ℓ_zero, div_zero]

theorem ηj_nonneg (j : ℕ) (t : ℝ) : 0 ≤ ηj D j t := D.η_nonneg _

theorem ηj_le_one (j : ℕ) (t : ℝ) : ηj D j t ≤ 1 := D.η_le_one _

theorem abs_ηj_le_one (j : ℕ) (t : ℝ) : |ηj D j t| ≤ 1 :=
  abs_le.2 ⟨by linarith [ηj_nonneg D j t], ηj_le_one D j t⟩

/-- If the rescaled time lies in the support of `η`, then `t` lies in the block `I_j`. -/
private theorem mem_I_of_arg_mem {j : ℕ} (hj : 1 ≤ j) {t : ℝ}
    (h : (t - τ j) / ℓ j ∈ Set.Ioo (1 / 10 : ℝ) (9 / 10)) : t ∈ I j := by
  have hℓ : 0 < ℓ j := ℓ_pos hj
  obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 h
  rw [lt_div_iff₀ hℓ] at h1
  rw [div_lt_iff₀ hℓ] at h2
  have hmem : t ∈ Set.Ioo (τ j) (τ (j + 1)) := by
    rw [← τ_add_ℓ hj]
    exact Set.mem_Ioo.2 ⟨by linarith, by linarith⟩
  exact hmem

theorem mem_I_of_ηj_ne_zero {j : ℕ} {t : ℝ} (h : ηj D j t ≠ 0) : t ∈ I j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact absurd (ηj_zero_block D t) h
  · have hj1 : 1 ≤ j := by omega
    have h' : D.η ((t - τ j) / ℓ j) ≠ 0 := h
    exact mem_I_of_arg_mem hj1 (D.η_supp _ h')

theorem mem_I_of_ηj'_ne_zero {j : ℕ} {t : ℝ} (h : ηj' D j t ≠ 0) : t ∈ I j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact absurd (ηj'_zero_block D t) h
  · have hj1 : 1 ≤ j := by omega
    have h' : D.η' ((t - τ j) / ℓ j) / ℓ j ≠ 0 := h
    have h'' : D.η' ((t - τ j) / ℓ j) ≠ 0 := by
      intro hz
      exact h' (by rw [hz, zero_div])
    exact mem_I_of_arg_mem hj1 (D.η'_supp _ h'')

theorem ηj_eq_zero_of_notMem {j : ℕ} {t : ℝ} (h : t ∉ I j) : ηj D j t = 0 := by
  by_contra hne
  exact h (mem_I_of_ηj_ne_zero D hne)

theorem ηj'_eq_zero_of_notMem {j : ℕ} {t : ℝ} (h : t ∉ I j) : ηj' D j t = 0 := by
  by_contra hne
  exact h (mem_I_of_ηj'_ne_zero D hne)

/-- On the middle third the rescaled time lies in `[1/3, 2/3]`. -/
private theorem arg_mem_Icc_of_mem_J {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ J j) :
    (t - τ j) / ℓ j ∈ Set.Icc (1 / 3 : ℝ) (2 / 3) := by
  have hℓ : 0 < ℓ j := ℓ_pos hj
  have ht' : t ∈ Set.Icc (τ j + ℓ j / 3) (τ j + 2 * ℓ j / 3) := ht
  obtain ⟨h1, h2⟩ := Set.mem_Icc.1 ht'
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · rw [le_div_iff₀ hℓ]
    linarith
  · rw [div_le_iff₀ hℓ]
    linarith

theorem ηj_eq_one_of_mem_J {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ J j) : ηj D j t = 1 :=
  D.η_one _ (arg_mem_Icc_of_mem_J hj ht)

theorem ηj'_eq_zero_of_mem_J {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ J j) : ηj' D j t = 0 := by
  show D.η' ((t - τ j) / ℓ j) / ℓ j = 0
  rw [D.η'_zero _ (arg_mem_Icc_of_mem_J hj ht), zero_div]

theorem hasDerivAt_ηj (j : ℕ) (t : ℝ) : HasDerivAt (ηj D j) (ηj' D j t) t := by
  have hinner : HasDerivAt (fun s : ℝ => (s - τ j) / ℓ j) (1 / ℓ j) t :=
    ((hasDerivAt_id t).sub_const (τ j)).div_const (ℓ j)
  have h := (D.η_hasDerivAt ((t - τ j) / ℓ j)).comp t hinner
  have he : D.η' ((t - τ j) / ℓ j) * (1 / ℓ j) = ηj' D j t := by
    show D.η' ((t - τ j) / ℓ j) * (1 / ℓ j) = D.η' ((t - τ j) / ℓ j) / ℓ j
    rw [mul_one_div]
  rw [he] at h
  exact h

theorem continuous_η : Continuous D.η :=
  continuous_iff_continuousAt.2 fun t => (D.η_hasDerivAt t).continuousAt

theorem continuous_ηj (j : ℕ) : Continuous (ηj D j) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_ηj D j t).continuousAt

theorem continuous_ηj' (j : ℕ) : Continuous (ηj' D j) := by
  have hη : Continuous D.η' := D.η'_continuous
  show Continuous fun t : ℝ => D.η' ((t - τ j) / ℓ j) / ℓ j
  fun_prop

theorem abs_ηj'_le {j : ℕ} (hj : 1 ≤ j) (t : ℝ) : |ηj' D j t| ≤ D.Cη / ℓ j := by
  have hℓ : 0 < ℓ j := ℓ_pos hj
  show |D.η' ((t - τ j) / ℓ j) / ℓ j| ≤ D.Cη / ℓ j
  rw [abs_div, abs_of_pos hℓ, div_le_iff₀ hℓ, div_mul_cancel₀ _ hℓ.ne']
  exact D.η'_bound _

theorem abs_ηj_sub_le {j : ℕ} (hj : 1 ≤ j) (s t : ℝ) :
    |ηj D j t - ηj D j s| ≤ D.Cη / ℓ j * |t - s| := by
  have hd : ∀ x ∈ (Set.univ : Set ℝ), HasDerivWithinAt (ηj D j) (ηj' D j x) Set.univ x :=
    fun x _ => (hasDerivAt_ηj D j x).hasDerivWithinAt
  have hb : ∀ x ∈ (Set.univ : Set ℝ), ‖ηj' D j x‖ ≤ D.Cη / ℓ j := by
    intro x _
    rw [Real.norm_eq_abs]
    exact abs_ηj'_le D hj x
  have key := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (Set.mem_univ s) (Set.mem_univ t)
  simp only [Real.norm_eq_abs] at key
  exact key

theorem ηj_at_zero (j : ℕ) : ηj D j 0 = 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact ηj_zero_block D 0
  · have hj1 : 1 ≤ j := by omega
    refine ηj_eq_zero_of_notMem D ?_
    intro hmem
    have hmem' : (0 : ℝ) ∈ Set.Ioo (τ j) (τ (j + 1)) := hmem
    have h1 : τ j < 0 := (Set.mem_Ioo.1 hmem').1
    have h2 : (1 : ℝ) / 4 ≤ τ j := τ_ge hj1
    linarith

/-! ## The cutoffs near the block endpoints -/

/-- If a cutoff (or its derivative) is nonzero at `t`, then `t` lies in the interior core
`(τ_i + ℓ_i/10, τ_i + 9 ℓ_i/10)` of the block `I_i`. -/
theorem core_bounds {i : ℕ} {t : ℝ} (h : ηj D i t ≠ 0 ∨ ηj' D i t ≠ 0) :
    1 ≤ i ∧ τ i + ℓ i / 10 < t ∧ t < τ i + 9 * ℓ i / 10 := by
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rcases h with h | h
      · exact absurd (ηj_zero_block D t) h
      · exact absurd (ηj'_zero_block D t) h
    · omega
  have hℓ0 : 0 < ℓ i := ℓ_pos hi1
  have harg : (t - τ i) / ℓ i ∈ Set.Ioo (1 / 10 : ℝ) (9 / 10) := by
    rcases h with h | h
    · have h' : D.η ((t - τ i) / ℓ i) ≠ 0 := h
      exact D.η_supp _ h'
    · have h' : D.η' ((t - τ i) / ℓ i) / ℓ i ≠ 0 := h
      refine D.η'_supp _ ?_
      intro hz
      exact h' (by rw [hz, zero_div])
  obtain ⟨ha, hb⟩ := harg
  rw [lt_div_iff₀ hℓ0] at ha
  rw [div_lt_iff₀ hℓ0] at hb
  exact ⟨hi1, by linarith, by linarith⟩

/-- All cutoffs `η_i` and their derivatives vanish on `(τ_j - ℓ_j/10, τ_j + ℓ_j/10)`. -/
private lemma ηj_ηj'_eq_zero_near_τ {j : ℕ} (hj : 1 ≤ j) {t : ℝ}
    (htl : τ j - ℓ j / 10 < t) (htr : t < τ j + ℓ j / 10) (i : ℕ) :
    ηj D i t = 0 ∧ ηj' D i t = 0 := by
  by_contra hcon
  have h : ηj D i t ≠ 0 ∨ ηj' D i t ≠ 0 := by
    by_cases h1 : ηj D i t = 0
    · exact Or.inr fun h2 => hcon ⟨h1, h2⟩
    · exact Or.inl h1
  obtain ⟨hi1, hca, hcb⟩ := core_bounds D h
  have hℓi : 0 < ℓ i := ℓ_pos hi1
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have h1 : τ (i + 1) ≤ τ j := τ_succ_le_of_lt hi1 hlt
    have h2 : τ i + ℓ i = τ (i + 1) := τ_add_ℓ hi1
    have h3 : ℓ j ≤ ℓ i := ℓ_antitone hi1 (le_of_lt hlt)
    linarith
  · subst heq
    linarith
  · have h1 : τ (j + 1) ≤ τ i := τ_succ_le_of_lt hj hgt
    have h2 : τ j + ℓ j = τ (j + 1) := τ_add_ℓ hj
    linarith

/-- Near `τ_j` all cutoffs vanish. -/
theorem ηj_eq_zero_near_τ {j : ℕ} (hj : 1 ≤ j) {t : ℝ}
    (h1 : τ j - ℓ j / 10 < t) (h2 : t < τ j + ℓ j / 10) (i : ℕ) : ηj D i t = 0 :=
  (ηj_ηj'_eq_zero_near_τ D hj h1 h2 i).1

/-- Near `τ_j` the derivatives of all cutoffs vanish. -/
theorem ηj'_eq_zero_near_τ {j : ℕ} (hj : 1 ≤ j) {t : ℝ}
    (h1 : τ j - ℓ j / 10 < t) (h2 : t < τ j + ℓ j / 10) (i : ℕ) : ηj' D i t = 0 :=
  (ηj_ηj'_eq_zero_near_τ D hj h1 h2 i).2

/-- All cutoffs `η_i` and their derivatives vanish on a neighbourhood of `τ_j`. -/
theorem eventually_ηj_zero_at_τ {j : ℕ} (hj : 1 ≤ j) :
    ∀ᶠ t in nhds (τ j), ∀ i, ηj D i t = 0 ∧ ηj' D i t = 0 := by
  have hℓ0 : 0 < ℓ j := ℓ_pos hj
  refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds
    (show τ j ∈ Set.Ioo (τ j - ℓ j / 10) (τ j + ℓ j / 10) from ⟨by linarith, by linarith⟩)) ?_
  rintro t ⟨htl, htr⟩ i
  exact ηj_ηj'_eq_zero_near_τ D hj htl htr i

/-! ## The global cutoff `ρ` -/

theorem continuous_ρ : Continuous D.ρ :=
  continuous_iff_continuousAt.2 fun t => (D.ρ_hasDerivAt t).continuousAt

theorem ρ_zero : D.ρ 0 = 0 := by
  by_contra hne
  have hmem := D.ρ_supp 0 hne
  have h1 : (1 : ℝ) / 8 < 0 := (Set.mem_Ioo.1 hmem).1
  norm_num at h1

theorem ρ_eq_one_of_mem_I {j : ℕ} {t : ℝ} (ht : t ∈ I j) : D.ρ t = 1 := by
  have h := I_subset (one_le_of_mem_I ht) ht
  exact D.ρ_one t ⟨h.1, by linarith [h.2]⟩

theorem ρ'_eq_zero_of_mem_I {j : ℕ} {t : ℝ} (ht : t ∈ I j) : D.ρ' t = 0 := by
  have h := I_subset (one_le_of_mem_I ht) ht
  exact D.ρ'_zero t ⟨h.1, by linarith [h.2]⟩

theorem abs_ρ_le_one (t : ℝ) : |D.ρ t| ≤ 1 :=
  abs_le.2 ⟨by linarith [D.ρ_nonneg t], D.ρ_le_one t⟩

/-! ## The blocks vanish outside their time interval -/

theorem βblock_eq_zero {j : ℕ} {t : ℝ} (h : t ∉ I j) (x : ℝ) : βblock D j t x = 0 := by
  have hη : ηj D j t = 0 := ηj_eq_zero_of_notMem D h
  refine Finset.sum_eq_zero fun m _ => ?_
  simp [βmode, hη]

theorem βxblock_eq_zero {j : ℕ} {t : ℝ} (h : t ∉ I j) (x : ℝ) : βxblock D j t x = 0 := by
  have hη : ηj D j t = 0 := ηj_eq_zero_of_notMem D h
  refine Finset.sum_eq_zero fun m _ => ?_
  simp [hη]

theorem vblock_eq_zero (ε : ℝ) {j : ℕ} {t : ℝ} (h : t ∉ I j) (x : ℝ) : vblock D ε j t x = 0 := by
  have hη : ηj D j t = 0 := ηj_eq_zero_of_notMem D h
  refine Finset.sum_eq_zero fun m _ => ?_
  simp [y, hη]

theorem vtblock_eq_zero (ε : ℝ) {j : ℕ} {t : ℝ} (h : t ∉ I j) (x : ℝ) :
    vtblock D ε j t x = 0 := by
  have hη : ηj D j t = 0 := ηj_eq_zero_of_notMem D h
  have hη' : ηj' D j t = 0 := ηj'_eq_zero_of_notMem D h
  refine Finset.sum_eq_zero fun m _ => ?_
  simp [y', hη, hη']

theorem vxblock_eq_zero (ε : ℝ) {j : ℕ} {t : ℝ} (h : t ∉ I j) (x : ℝ) :
    vxblock D ε j t x = 0 := by
  have hη : ηj D j t = 0 := ηj_eq_zero_of_notMem D h
  refine Finset.sum_eq_zero fun m _ => ?_
  simp [y, hη]

theorem vxxblock_eq_zero (ε : ℝ) {j : ℕ} {t : ℝ} (h : t ∉ I j) (x : ℝ) :
    vxxblock D ε j t x = 0 := by
  have hη : ηj D j t = 0 := ηj_eq_zero_of_notMem D h
  refine Finset.sum_eq_zero fun m _ => ?_
  simp [y, hη]

theorem Rblock_eq_zero (ε : ℝ) {j : ℕ} {t : ℝ} (h : t ∉ I j) (x : ℝ) :
    Rblock D ε j t x = 0 := by
  have hη : ηj D j t = 0 := ηj_eq_zero_of_notMem D h
  have hη' : ηj' D j t = 0 := ηj'_eq_zero_of_notMem D h
  refine Finset.sum_eq_zero fun m _ => ?_
  simp [E, r, y, hη, hη']

/-! ## The blocks vanish where the cutoffs vanish -/

theorem βblock_eq_zero_of_ηj {i : ℕ} {t : ℝ} (h : ηj D i t = 0) (x : ℝ) :
    βblock D i t x = 0 := by
  simp [βblock, βmode, h]

theorem βxblock_eq_zero_of_ηj {i : ℕ} {t : ℝ} (h : ηj D i t = 0) (x : ℝ) :
    βxblock D i t x = 0 := by
  simp [βxblock, h]

theorem vblock_eq_zero_of_ηj (ε : ℝ) {i : ℕ} {t : ℝ} (h : ηj D i t = 0) (x : ℝ) :
    vblock D ε i t x = 0 := by
  simp [vblock, y, h]

theorem vtblock_eq_zero_of_ηj (ε : ℝ) {i : ℕ} {t : ℝ} (h : ηj D i t = 0) (h' : ηj' D i t = 0)
    (x : ℝ) : vtblock D ε i t x = 0 := by
  simp [vtblock, y', h, h']

theorem vxblock_eq_zero_of_ηj (ε : ℝ) {i : ℕ} {t : ℝ} (h : ηj D i t = 0) (x : ℝ) :
    vxblock D ε i t x = 0 := by
  simp [vxblock, y, h]

theorem vxxblock_eq_zero_of_ηj (ε : ℝ) {i : ℕ} {t : ℝ} (h : ηj D i t = 0) (x : ℝ) :
    vxxblock D ε i t x = 0 := by
  simp [vxxblock, y, h]

theorem Rblock_eq_zero_of_ηj (ε : ℝ) {i : ℕ} {t : ℝ} (h : ηj D i t = 0) (h' : ηj' D i t = 0)
    (x : ℝ) : Rblock D ε i t x = 0 := by
  simp [Rblock, E, r, y, h, h']

/-! ## Bounds on the blocks of `β` -/

/-- A product of three factors of modulus `≤ 1` and one nonnegative factor `r` is `≤ r`. -/
private lemma abs_prod_le {A B C r : ℝ} (hA : |A| ≤ 1) (hB : |B| ≤ 1) (hC : |C| ≤ 1)
    (hr : 0 ≤ r) : |A * r * B * C| ≤ r := by
  have e : |A * r * B * C| = |A| * r * |B| * |C| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hr]
  rw [e]
  have h1 : |A| * r ≤ r := mul_le_of_le_one_left hr hA
  have h2 : |A| * r * |B| ≤ |A| * r :=
    mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) hr) hB
  have h3 : |A| * r * |B| * |C| ≤ |A| * r * |B| :=
    mul_le_of_le_one_right (mul_nonneg (mul_nonneg (abs_nonneg _) hr) (abs_nonneg _)) hC
  linarith

theorem abs_βmode_le {j m : ℕ} (hj : 1 ≤ j) (t x : ℝ) : |βmode D j m t x| ≤ ((K j m : ℝ))⁻¹ := by
  have hK : (0 : ℝ) < (K j m : ℝ) := Nat.cast_pos.mpr (K_pos hj)
  unfold βmode
  exact abs_prod_le (abs_ηj_le_one D j t) (Real.abs_sin_le_one _) (Real.abs_cos_le_one _)
    (inv_nonneg.mpr hK.le)

theorem abs_βblock_le {j : ℕ} (hj : 1 ≤ j) (t x : ℝ) : |βblock D j t x| ≤ S j :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => abs_βmode_le D hj t x)

/-! ## At most one active block -/

theorem notMem_I_of_mem_I {i j : ℕ} {t : ℝ} (ht : t ∈ I j) (hij : i ≠ j) : t ∉ I i :=
  fun hi => (Set.disjoint_left.1 (I_disjoint hij) hi) ht

theorem exists_block (t : ℝ) : ∃ j, ∀ i, i ≠ j → t ∉ I i := by
  by_cases h : ∃ j, t ∈ I j
  · obtain ⟨j, hj⟩ := h
    exact ⟨j, fun i hij => notMem_I_of_mem_I hj hij⟩
  · exact ⟨0, fun i _ hi => h ⟨i, hi⟩⟩

theorem notMem_I_of_notMem_Ico {t : ℝ} (ht : t ∉ Set.Ico (1 / 4 : ℝ) (5 / 16)) (j : ℕ) :
    t ∉ I j := by
  intro hmem
  have hj1 : 1 ≤ j := one_le_of_mem_I hmem
  obtain ⟨h1, h2⟩ := Set.mem_Ioo.1 (show t ∈ Set.Ioo (τ j) (τ (j + 1)) from hmem)
  have h3 : (1 : ℝ) / 4 ≤ τ j := τ_ge hj1
  have h4 : τ (j + 1) < 5 / 16 := τ_lt (by omega)
  exact ht (Set.mem_Ico.2 ⟨by linarith, by linarith⟩)

/-! ## Reduction of the `finsum`s to a single block -/

theorem β_eq_block {j : ℕ} {t : ℝ} (ht : t ∈ I j) (x : ℝ) : β D t x = βblock D j t x :=
  finsum_eq_single (fun i => βblock D i t x) j fun _i hi =>
    βblock_eq_zero D (notMem_I_of_mem_I ht hi) x

theorem β_eq_zero {t : ℝ} (ht : ∀ j, t ∉ I j) (x : ℝ) : β D t x = 0 :=
  finsum_eq_zero_of_forall_eq_zero (f := fun i => βblock D i t x) fun i =>
    βblock_eq_zero D (ht i) x

theorem βx_eq_block {j : ℕ} {t : ℝ} (ht : t ∈ I j) (x : ℝ) : βx D t x = βxblock D j t x :=
  finsum_eq_single (fun i => βxblock D i t x) j fun _i hi =>
    βxblock_eq_zero D (notMem_I_of_mem_I ht hi) x

theorem βx_eq_zero {t : ℝ} (ht : ∀ j, t ∉ I j) (x : ℝ) : βx D t x = 0 :=
  finsum_eq_zero_of_forall_eq_zero (f := fun i => βxblock D i t x) fun i =>
    βxblock_eq_zero D (ht i) x

theorem v_eq_block (ε : ℝ) {j : ℕ} {t : ℝ} (ht : t ∈ I j) (x : ℝ) :
    v D ε t x = vblock D ε j t x :=
  finsum_eq_single (fun i => vblock D ε i t x) j fun _i hi =>
    vblock_eq_zero D ε (notMem_I_of_mem_I ht hi) x

theorem v_eq_zero (ε : ℝ) {t : ℝ} (ht : ∀ j, t ∉ I j) (x : ℝ) : v D ε t x = 0 :=
  finsum_eq_zero_of_forall_eq_zero (f := fun i => vblock D ε i t x) fun i =>
    vblock_eq_zero D ε (ht i) x

theorem vt_eq_block (ε : ℝ) {j : ℕ} {t : ℝ} (ht : t ∈ I j) (x : ℝ) :
    vt D ε t x = vtblock D ε j t x :=
  finsum_eq_single (fun i => vtblock D ε i t x) j fun _i hi =>
    vtblock_eq_zero D ε (notMem_I_of_mem_I ht hi) x

theorem vt_eq_zero (ε : ℝ) {t : ℝ} (ht : ∀ j, t ∉ I j) (x : ℝ) : vt D ε t x = 0 :=
  finsum_eq_zero_of_forall_eq_zero (f := fun i => vtblock D ε i t x) fun i =>
    vtblock_eq_zero D ε (ht i) x

theorem vx_eq_block (ε : ℝ) {j : ℕ} {t : ℝ} (ht : t ∈ I j) (x : ℝ) :
    vx D ε t x = vxblock D ε j t x :=
  finsum_eq_single (fun i => vxblock D ε i t x) j fun _i hi =>
    vxblock_eq_zero D ε (notMem_I_of_mem_I ht hi) x

theorem vx_eq_zero (ε : ℝ) {t : ℝ} (ht : ∀ j, t ∉ I j) (x : ℝ) : vx D ε t x = 0 :=
  finsum_eq_zero_of_forall_eq_zero (f := fun i => vxblock D ε i t x) fun i =>
    vxblock_eq_zero D ε (ht i) x

theorem vxx_eq_block (ε : ℝ) {j : ℕ} {t : ℝ} (ht : t ∈ I j) (x : ℝ) :
    vxx D ε t x = vxxblock D ε j t x :=
  finsum_eq_single (fun i => vxxblock D ε i t x) j fun _i hi =>
    vxxblock_eq_zero D ε (notMem_I_of_mem_I ht hi) x

theorem vxx_eq_zero (ε : ℝ) {t : ℝ} (ht : ∀ j, t ∉ I j) (x : ℝ) : vxx D ε t x = 0 :=
  finsum_eq_zero_of_forall_eq_zero (f := fun i => vxxblock D ε i t x) fun i =>
    vxxblock_eq_zero D ε (ht i) x

theorem R_eq_block (ε : ℝ) {j : ℕ} {t : ℝ} (ht : t ∈ I j) (x : ℝ) :
    R D ε t x = Rblock D ε j t x :=
  finsum_eq_single (fun i => Rblock D ε i t x) j fun _i hi =>
    Rblock_eq_zero D ε (notMem_I_of_mem_I ht hi) x

theorem R_eq_zero (ε : ℝ) {t : ℝ} (ht : ∀ j, t ∉ I j) (x : ℝ) : R D ε t x = 0 :=
  finsum_eq_zero_of_forall_eq_zero (f := fun i => Rblock D ε i t x) fun i =>
    Rblock_eq_zero D ε (ht i) x

/-! ## Local (in time) identification with a single block -/

theorem u_eventuallyEq_block (ε : ℝ) {j : ℕ} {t : ℝ} (ht : t ∈ I j) (x : ℝ) :
    (fun s => u D ε s x) =ᶠ[nhds t] fun s => D.ρ s * φ x + vblock D ε j s x :=
  Filter.eventuallyEq_of_mem ((isOpen_I j).mem_nhds ht) fun s hs => by
    show D.ρ s * φ x + v D ε s x = D.ρ s * φ x + vblock D ε j s x
    rw [v_eq_block D ε hs x]

end LionsC12

end
