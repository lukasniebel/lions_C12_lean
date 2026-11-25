module

public import LionsC12.Construction.Defs
public import LionsC12.Coefficient.Blocks
public import LionsC12.Coefficient.Support
public import LionsC12.Modes.Trig
public import LionsC12.Solution.Basic
public import LionsC12.Coefficient.Holder
public import LionsC12.Forcing.Cancellation

/-!
# Joint continuity (Proposition 5.1)

The forcing `f`, the coefficient `𝔞`, and the candidate solution `u` are jointly continuous
on `ℝ × ℝ`.  Away from the accumulation time `5/16` this is local: every point has a
neighbourhood on which at most one block is active, and each block is a finite sum of
continuous functions.  At `t = 5/16` one uses the quantitative decay estimates
`|f - f0| ≲ |t - 5/16|`, `|β| ≲ |t - 5/16|`, `|v| ≲ |t - 5/16|²`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ## Continuity of the profile part -/

theorem continuous_f0 : Continuous (fun q : ℝ × ℝ => f0 D q.1 q.2) := by
  have h1 : Continuous D.ρ := continuous_ρ D
  have h2 : Continuous D.ρ' := D.ρ'_continuous
  have h3 : Continuous φ := continuous_φ
  have h4 : Continuous φ'' := continuous_φ''
  show Continuous fun q : ℝ × ℝ => D.ρ' q.1 * φ q.2 - D.ρ q.1 * φ'' q.2
  fun_prop

/-! ## Continuity of the individual blocks (jointly in `(t, x)`) -/

theorem continuous_βblock (j : ℕ) : Continuous (fun q : ℝ × ℝ => βblock D j q.1 q.2) := by
  have hη : Continuous (ηj D j) := continuous_ηj D j
  simp only [βblock, βmode, θ]
  refine continuous_finsetSum _ fun m _ => ?_
  fun_prop

theorem continuous_βxblock (j : ℕ) : Continuous (fun q : ℝ × ℝ => βxblock D j q.1 q.2) := by
  have hη : Continuous (ηj D j) := continuous_ηj D j
  simp only [βxblock, θ]
  refine continuous_finsetSum _ fun m _ => ?_
  fun_prop

theorem continuous_vblock (ε : ℝ) (j : ℕ) :
    Continuous (fun q : ℝ × ℝ => vblock D ε j q.1 q.2) := by
  have hη : Continuous (ηj D j) := continuous_ηj D j
  simp only [vblock, y, θ]
  refine continuous_finsetSum _ fun m _ => ?_
  have hp : Continuous (p (K j m)) := continuous_p _
  fun_prop

theorem continuous_vxblock (ε : ℝ) (j : ℕ) :
    Continuous (fun q : ℝ × ℝ => vxblock D ε j q.1 q.2) := by
  have hη : Continuous (ηj D j) := continuous_ηj D j
  simp only [vxblock, y, θ]
  refine continuous_finsetSum _ fun m _ => ?_
  have hp : Continuous (p' (K j m)) := continuous_p' _
  fun_prop

theorem continuous_vxxblock (ε : ℝ) (j : ℕ) :
    Continuous (fun q : ℝ × ℝ => vxxblock D ε j q.1 q.2) := by
  have hη : Continuous (ηj D j) := continuous_ηj D j
  simp only [vxxblock, y, θ]
  refine continuous_finsetSum _ fun m _ => ?_
  have hp : Continuous (p'' (K j m)) := continuous_p'' _
  fun_prop

theorem continuous_vtblock (ε : ℝ) (j : ℕ) :
    Continuous (fun q : ℝ × ℝ => vtblock D ε j q.1 q.2) := by
  have hη : Continuous (ηj D j) := continuous_ηj D j
  have hη' : Continuous (ηj' D j) := continuous_ηj' D j
  simp only [vtblock, y', θ]
  refine continuous_finsetSum _ fun m _ => ?_
  have hp : Continuous (p (K j m)) := continuous_p _
  fun_prop

theorem continuous_Rblock (ε : ℝ) (j : ℕ) :
    Continuous (fun q : ℝ × ℝ => Rblock D ε j q.1 q.2) := by
  have hη : Continuous (ηj D j) := continuous_ηj D j
  have hη' : Continuous (ηj' D j) := continuous_ηj' D j
  simp only [Rblock, E, r, y, θ]
  refine continuous_finsetSum _ fun m _ => ?_
  have hp : Continuous (p (K j m)) := continuous_p _
  have hc : Continuous (c (K j m)) := continuous_c _
  fun_prop

/-! ## Reduction of the `finsum`s using only the cutoffs -/

theorem β_eq_block' {j : ℕ} {t : ℝ} (h : ∀ i, i ≠ j → ηj D i t = 0) (x : ℝ) :
    β D t x = βblock D j t x :=
  finsum_eq_single (fun i => βblock D i t x) j fun _i hi => βblock_eq_zero_of_ηj D (h _ hi) x

theorem βx_eq_block' {j : ℕ} {t : ℝ} (h : ∀ i, i ≠ j → ηj D i t = 0) (x : ℝ) :
    βx D t x = βxblock D j t x :=
  finsum_eq_single (fun i => βxblock D i t x) j fun _i hi => βxblock_eq_zero_of_ηj D (h _ hi) x

theorem v_eq_block' (ε : ℝ) {j : ℕ} {t : ℝ} (h : ∀ i, i ≠ j → ηj D i t = 0) (x : ℝ) :
    v D ε t x = vblock D ε j t x :=
  finsum_eq_single (fun i => vblock D ε i t x) j fun _i hi => vblock_eq_zero_of_ηj D ε (h _ hi) x

theorem vx_eq_block' (ε : ℝ) {j : ℕ} {t : ℝ} (h : ∀ i, i ≠ j → ηj D i t = 0) (x : ℝ) :
    vx D ε t x = vxblock D ε j t x :=
  finsum_eq_single (fun i => vxblock D ε i t x) j fun _i hi => vxblock_eq_zero_of_ηj D ε (h _ hi) x

theorem vxx_eq_block' (ε : ℝ) {j : ℕ} {t : ℝ} (h : ∀ i, i ≠ j → ηj D i t = 0) (x : ℝ) :
    vxx D ε t x = vxxblock D ε j t x :=
  finsum_eq_single (fun i => vxxblock D ε i t x) j fun _i hi =>
    vxxblock_eq_zero_of_ηj D ε (h _ hi) x

theorem R_eq_block' (ε : ℝ) {j : ℕ} {t : ℝ}
    (h : ∀ i, i ≠ j → ηj D i t = 0 ∧ ηj' D i t = 0) (x : ℝ) :
    R D ε t x = Rblock D ε j t x :=
  finsum_eq_single (fun i => Rblock D ε i t x) j fun _i hi =>
    Rblock_eq_zero_of_ηj D ε (h _ hi).1 (h _ hi).2 x

/-! ## A single active block near every time `≠ 5/16` -/

theorem eventually_ηj_zero_outside {t₀ : ℝ} (ht : t₀ ∉ Set.Icc (1 / 4 : ℝ) (5 / 16)) :
    ∀ᶠ t in nhds t₀, ∀ i, ηj D i t = 0 ∧ ηj' D i t = 0 := by
  refine Filter.eventually_of_mem (isClosed_Icc.isOpen_compl.mem_nhds ht) ?_
  intro t htm i
  have h : t ∉ Set.Ico (1 / 4 : ℝ) (5 / 16) := fun hc => htm (Set.Ico_subset_Icc_self hc)
  exact ⟨ηj_eq_zero_of_notMem D (notMem_I_of_notMem_Ico h i),
    ηj'_eq_zero_of_notMem D (notMem_I_of_notMem_Ico h i)⟩

private lemma exists_nat_between {d : ℝ} (hd0 : 0 < d) (hd : d ≤ 1 / 16) :
    ∃ j : ℕ, 1 ≤ j ∧ d ≤ 1 / (16 * (j : ℝ)) ∧ 1 / (16 * ((j : ℝ) + 1)) < d := by
  have h16d : (0 : ℝ) < 16 * d := by linarith
  have hX1 : (1 : ℝ) ≤ 1 / (16 * d) := by rw [le_div_iff₀ h16d]; linarith
  have hX0 : (0 : ℝ) ≤ 1 / (16 * d) := by linarith
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌊(1 : ℝ) / (16 * d)⌋₊ := ⟨_, rfl⟩
  have hj1 : 1 ≤ j := by rw [hj]; exact Nat.le_floor (by exact_mod_cast hX1)
  have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hjX : (j : ℝ) ≤ 1 / (16 * d) := by rw [hj]; exact Nat.floor_le hX0
  have hXj : (1 : ℝ) / (16 * d) < (j : ℝ) + 1 := by rw [hj]; exact Nat.lt_floor_add_one _
  have hh1 : (j : ℝ) * (16 * d) ≤ 1 := (le_div_iff₀ h16d).mp hjX
  have hh2 : (1 : ℝ) < ((j : ℝ) + 1) * (16 * d) := (div_lt_iff₀ h16d).mp hXj
  refine ⟨j, hj1, ?_, ?_⟩
  · rw [le_div_iff₀ (by linarith : (0 : ℝ) < 16 * (j : ℝ))]
    nlinarith
  · rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 16 * ((j : ℝ) + 1))]
    nlinarith

theorem exists_index_of_Ico {t : ℝ} (h1 : (1 : ℝ) / 4 ≤ t) (h2 : t < 5 / 16) :
    ∃ j, 1 ≤ j ∧ τ j ≤ t ∧ t < τ (j + 1) := by
  obtain ⟨j, hj1, hA, hB⟩ := exists_nat_between (d := 5 / 16 - t) (by linarith) (by linarith)
  refine ⟨j, hj1, ?_, ?_⟩
  · show (5 : ℝ) / 16 - 1 / (16 * (j : ℝ)) ≤ t
    linarith
  · have hτ : τ (j + 1) = 5 / 16 - 1 / (16 * ((j : ℝ) + 1)) := by
      unfold τ
      push_cast
      ring
    rw [hτ]
    linarith

theorem exists_eventually_single_block (t₀ : ℝ) (ht₀ : t₀ ≠ 5 / 16) :
    ∃ j : ℕ, ∀ᶠ t in nhds t₀, ∀ i, i ≠ j → ηj D i t = 0 ∧ ηj' D i t = 0 := by
  by_cases hIcc : t₀ ∈ Set.Icc (1 / 4 : ℝ) (5 / 16)
  · obtain ⟨ha, hb⟩ := hIcc
    have hb' : t₀ < 5 / 16 := lt_of_le_of_ne hb ht₀
    obtain ⟨j, hj1, hτle, hlt⟩ := exists_index_of_Ico ha hb'
    rcases eq_or_lt_of_le hτle with heq | hlt2
    · refine ⟨0, ?_⟩
      have hev := eventually_ηj_zero_at_τ D hj1
      rw [heq] at hev
      exact hev.mono fun t ht i _ => ht i
    · refine ⟨j, ?_⟩
      have hmem : t₀ ∈ I j := ⟨hlt2, hlt⟩
      refine Filter.eventually_of_mem ((isOpen_I j).mem_nhds hmem) ?_
      intro t htm i hi
      exact ⟨ηj_eq_zero_of_notMem D (notMem_I_of_mem_I htm hi),
        ηj'_eq_zero_of_notMem D (notMem_I_of_mem_I htm hi)⟩
  · exact ⟨0, (eventually_ηj_zero_outside D hIcc).mono fun t ht i _ => ht i⟩

/-! ## The general continuity criterion -/

/-- A function of `(t, x)` which locally (away from `t = 5/16`) agrees with one of the
continuous blocks is continuous at every point `(t₀, x₀)` with `t₀ ≠ 5/16`. -/
theorem continuousAt_of_blocks {g : ℝ → ℝ → ℝ} {gb : ℕ → ℝ → ℝ → ℝ}
    (hc : ∀ j, Continuous fun q : ℝ × ℝ => gb j q.1 q.2)
    (heq : ∀ (j : ℕ) (t : ℝ), (∀ i, i ≠ j → ηj D i t = 0 ∧ ηj' D i t = 0) →
      ∀ x, g t x = gb j t x)
    {t₀ : ℝ} (ht₀ : t₀ ≠ 5 / 16) (x₀ : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => g q.1 q.2) (t₀, x₀) := by
  obtain ⟨j, hj⟩ := exists_eventually_single_block D t₀ ht₀
  have hmem : ∀ᶠ q : ℝ × ℝ in nhds (t₀, x₀),
      ∀ i, i ≠ j → ηj D i q.1 = 0 ∧ ηj' D i q.1 = 0 :=
    (continuous_fst.continuousAt (x := (t₀, x₀))).eventually hj
  have hEq : (fun q : ℝ × ℝ => gb j q.1 q.2) =ᶠ[nhds (t₀, x₀)] fun q : ℝ × ℝ => g q.1 q.2 :=
    hmem.mono fun q hq => (heq j q.1 hq q.2).symm
  exact ((hc j).continuousAt).congr hEq

/-- A function of `(t, x)` which locally (away from `t = 5/16`) agrees with one of the
continuous blocks and which is dominated by a continuous function of `t` vanishing at `5/16`
is continuous. -/
theorem continuous_of_blocks {g : ℝ → ℝ → ℝ} {gb : ℕ → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hc : ∀ j, Continuous fun q : ℝ × ℝ => gb j q.1 q.2)
    (heq : ∀ (j : ℕ) (t : ℝ), (∀ i, i ≠ j → ηj D i t = 0 ∧ ηj' D i t = 0) →
      ∀ x, g t x = gb j t x)
    (hhc : Continuous h) (hh0 : h (5 / 16) = 0) (hb : ∀ t x, |g t x| ≤ h t) :
    Continuous fun q : ℝ × ℝ => g q.1 q.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, x₀⟩
  by_cases ht₀ : t₀ = 5 / 16
  · subst ht₀
    have hg0 : g (5 / 16) x₀ = 0 := by
      have h1 := hb (5 / 16) x₀
      rw [hh0] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    have hdom : Filter.Tendsto (fun q : ℝ × ℝ => h q.1) (nhds ((5 : ℝ) / 16, x₀)) (nhds 0) := by
      rw [← hh0]
      exact (hhc.comp continuous_fst).tendsto _
    have hT : Filter.Tendsto (fun q : ℝ × ℝ => g q.1 q.2) (nhds ((5 : ℝ) / 16, x₀)) (nhds 0) := by
      refine squeeze_zero_norm (fun q => ?_) hdom
      rw [Real.norm_eq_abs]
      exact hb q.1 q.2
    simpa [ContinuousAt, hg0] using hT
  · exact continuousAt_of_blocks D hc heq ht₀ x₀

/-! ## Scaling in `ε` -/

theorem vblock_smul (ε : ℝ) (j : ℕ) (t x : ℝ) : vblock D ε j t x = ε * vblock D 1 j t x := by
  simp only [vblock, y, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem vxblock_smul (ε : ℝ) (j : ℕ) (t x : ℝ) : vxblock D ε j t x = ε * vxblock D 1 j t x := by
  simp only [vxblock, y, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem vxxblock_smul (ε : ℝ) (j : ℕ) (t x : ℝ) :
    vxxblock D ε j t x = ε * vxxblock D 1 j t x := by
  simp only [vxxblock, y, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem Rblock_smul (ε : ℝ) (j : ℕ) (t x : ℝ) : Rblock D ε j t x = ε * Rblock D 1 j t x := by
  simp only [Rblock, E, r, y, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- The bound `abs_vxblock_le` for every real `ε`, by `ε`-scaling. -/
theorem abs_vxblock_le' (ε : ℝ) {j : ℕ} (hj : 1 ≤ j) (t x : ℝ) :
    |vxblock D ε j t x| ≤ |ε| * (2 * S j) := by
  rw [vxblock_smul D ε, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ε)
  have := abs_vxblock_le D (by norm_num : (0:ℝ) ≤ 1) hj t x
  linarith

/-! ## Decaying block bounds -/

theorem abs_Rblock_le_ℓ {ε : ℝ} (hε0 : 0 ≤ ε) {j : ℕ} (hj : 1 ≤ j) (t x : ℝ) :
    |Rblock D ε j t x| ≤ ε * (D.Cη + 1) * ℓ j := by
  have hℓ0 : 0 < ℓ j := ℓ_pos hj
  have hℓ : ℓ j ≤ 1 / 32 := ℓ_le hj
  have hA : (0 : ℝ) ≤ ε * D.Cη * (ℓ j)⁻¹ + 4 * ε := by
    have h1 : (0 : ℝ) ≤ ε * D.Cη * (ℓ j)⁻¹ :=
      mul_nonneg (mul_nonneg hε0 D.Cη_nonneg) (inv_nonneg.mpr hℓ0.le)
    linarith
  have hkey : (ε * D.Cη * (ℓ j)⁻¹ + 4 * ε) * (ℓ j ^ 2 / 255) + 2 * ε * (ℓ j / 15)
      = ε * D.Cη * ℓ j / 255 + 4 * ε * ℓ j ^ 2 / 255 + 2 * ε * ℓ j / 15 := by
    field_simp
  have hCη : (0 : ℝ) ≤ ε * D.Cη * ℓ j :=
    mul_nonneg (mul_nonneg hε0 D.Cη_nonneg) hℓ0.le
  have hεℓ : (0 : ℝ) ≤ ε * ℓ j := mul_nonneg hε0 hℓ0.le
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
    _ ≤ ε * (D.Cη + 1) * ℓ j := by nlinarith [hCη, hεℓ, hℓ, hℓ0]

theorem abs_Rblock_le_ℓ' (ε : ℝ) {j : ℕ} (hj : 1 ≤ j) (t x : ℝ) :
    |Rblock D ε j t x| ≤ |ε| * ((D.Cη + 1) * ℓ j) := by
  rw [Rblock_smul D ε, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ε)
  have := abs_Rblock_le_ℓ D (by norm_num : (0 : ℝ) ≤ 1) hj t x
  linarith [this]

theorem abs_Lβv_le_of_mem_I {ε : ℝ} (hε0 : 0 ≤ ε) {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ I j)
    (x : ℝ) : |Lβv D ε t x| ≤ ε / (60 * ((j : ℝ) + 1)) := by
  have hjr : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h1 : |βxblock D j t x * vxblock D ε j t x| ≤ (M j : ℝ) * (2 * ε * S j) :=
    abs_mul_le_mul (abs_βxblock_le D j t x) (abs_vxblock_le D hε0 hj t x)
  have h2 : |βblock D j t x * vxxblock D ε j t x| ≤ S j * (2 * ε * (M j : ℝ)) :=
    abs_mul_le_mul (abs_βblock_le D hj t x) (abs_vxxblock_le D hε0 hj t x)
  have h3 : -(βxblock D j t x * vxblock D ε j t x) - βblock D j t x * vxxblock D ε j t x
      = -(βxblock D j t x * vxblock D ε j t x + βblock D j t x * vxxblock D ε j t x) := by ring
  have h4 : (M j : ℝ) * S j ≤ 1 / (240 * ((j : ℝ) + 1)) := M_mul_S_le hj
  have h5 : 4 * ε * ((M j : ℝ) * S j) ≤ 4 * ε * (1 / (240 * ((j : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left h4 (by linarith)
  have h6 : 4 * ε * (1 / (240 * ((j : ℝ) + 1))) = ε / (60 * ((j : ℝ) + 1)) := by
    field_simp
    ring
  simp only [Lβv]
  rw [β_eq_block D ht, βx_eq_block D ht, vx_eq_block D ε ht, vxx_eq_block D ε ht, h3, abs_neg]
  refine (abs_add_le _ _).trans ?_
  have h8 : (M j : ℝ) * (2 * ε * S j) + S j * (2 * ε * (M j : ℝ))
      = 4 * ε * ((M j : ℝ) * S j) := by ring
  linarith

theorem Lβv_smul (ε : ℝ) (t x : ℝ) : Lβv D ε t x = ε * Lβv D 1 t x := by
  by_cases hex : ∃ j, t ∈ I j
  · obtain ⟨j, htj⟩ := hex
    simp only [Lβv]
    rw [β_eq_block D htj, βx_eq_block D htj, vx_eq_block D ε htj, vxx_eq_block D ε htj,
      vx_eq_block D 1 htj, vxx_eq_block D 1 htj, vxblock_smul D ε, vxxblock_smul D ε]
    ring
  · rw [not_exists] at hex
    simp only [Lβv]
    rw [β_eq_zero D hex, βx_eq_zero D hex, vx_eq_zero D ε hex, vxx_eq_zero D ε hex,
      vx_eq_zero D 1 hex, vxx_eq_zero D 1 hex]
    ring

theorem abs_Lβv_le_of_mem_I' (ε : ℝ) {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ I j) (x : ℝ) :
    |Lβv D ε t x| ≤ |ε| * (1 / (60 * ((j : ℝ) + 1))) := by
  rw [Lβv_smul D ε, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ε)
  have := abs_Lβv_le_of_mem_I D (by norm_num : (0 : ℝ) ≤ 1) hj ht x
  linarith [this]

/-! ## Distance to the accumulation point -/

theorem inv_le_dist_of_mem_I {j : ℕ} {t : ℝ} (ht : t ∈ I j) :
    1 / (16 * ((j : ℝ) + 1)) ≤ 5 / 16 - t := by
  have h2 : t < τ (j + 1) := ht.2
  have hτ : τ (j + 1) = 5 / 16 - 1 / (16 * ((j : ℝ) + 1)) := by
    unfold τ
    push_cast
    ring
  rw [hτ] at h2
  linarith

theorem ℓ_le_dist_of_mem_I {j : ℕ} {t : ℝ} (ht : t ∈ I j) : ℓ j ≤ 5 / 16 - t := by
  have hj1 : 1 ≤ j := one_le_of_mem_I ht
  have hj' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have h := inv_le_dist_of_mem_I ht
  have hℓ : ℓ j ≤ 1 / (16 * ((j : ℝ) + 1)) := by
    show (1 : ℝ) / (16 * (j : ℝ) * ((j : ℝ) + 1)) ≤ 1 / (16 * ((j : ℝ) + 1))
    refine one_div_le_one_div_of_le ?_ ?_
    · nlinarith
    · nlinarith
  linarith

/-! ## Decay of `β`, `v` and `f - f0` towards `t = 5/16` -/

theorem abs_β_le_dist (t x : ℝ) : |β D t x| ≤ |t - 5 / 16| / 15 := by
  by_cases hex : ∃ j, t ∈ I j
  · obtain ⟨j, htj⟩ := hex
    have hj1 : 1 ≤ j := one_le_of_mem_I htj
    have hℓ0 : 0 < ℓ j := ℓ_pos hj1
    have h1 : |βblock D j t x| ≤ S j := abs_βblock_le D hj1 t x
    have h2 : S j ≤ ℓ j / 15 := S_le hj1
    have h3 : ℓ j ≤ 5 / 16 - t := ℓ_le_dist_of_mem_I htj
    have h4 : |t - 5 / 16| = 5 / 16 - t := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [β_eq_block D htj, h4]
    linarith
  · rw [not_exists] at hex
    rw [β_eq_zero D hex, abs_zero]
    positivity

theorem abs_vblock_le_sq (ε : ℝ) {j : ℕ} (hj : 1 ≤ j) (t x : ℝ) :
    |vblock D ε j t x| ≤ |ε| * (ℓ j ^ 2 / 255) := by
  rw [vblock_smul D ε, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ε)
  calc |vblock D 1 j t x| ≤ ∑ m ∈ Finset.Icc 1 (M j), |y D 1 j m t * p (K j m) x| := by
        simp only [vblock]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹ ^ 2 := by
        refine Finset.sum_le_sum fun m _ => ?_
        have hE : (1 : ℝ) / (K j m : ℝ) ^ 2 * 1 = ((K j m : ℝ))⁻¹ ^ 2 := by
          rw [inv_pow]; ring
        rw [← hE]
        exact abs_mul_le_mul (abs_y_le D (by norm_num) hj m t) (abs_p_le_one _ _)
    _ ≤ ℓ j ^ 2 / 255 := sum_K_inv_sq_le hj

theorem abs_v_le_dist' (ε : ℝ) (t x : ℝ) : |v D ε t x| ≤ |ε| * |t - 5 / 16| ^ 2 := by
  by_cases hex : ∃ j, t ∈ I j
  · obtain ⟨j, htj⟩ := hex
    have hj1 : 1 ≤ j := one_le_of_mem_I htj
    have hℓ0 : 0 < ℓ j := ℓ_pos hj1
    have hd : ℓ j ≤ 5 / 16 - t := ℓ_le_dist_of_mem_I htj
    have habs : |t - 5 / 16| = 5 / 16 - t := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have hb := abs_vblock_le_sq D ε hj1 t x
    have hsq : ℓ j ^ 2 ≤ (5 / 16 - t) ^ 2 := by nlinarith
    have hmul : |ε| * (ℓ j ^ 2) ≤ |ε| * ((5 / 16 - t) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (abs_nonneg ε)
    have hnn : (0 : ℝ) ≤ |ε| * (ℓ j ^ 2) := mul_nonneg (abs_nonneg ε) (sq_nonneg _)
    rw [v_eq_block D ε htj, habs]
    nlinarith [hb, hmul, hnn]
  · rw [not_exists] at hex
    rw [v_eq_zero D ε hex, abs_zero]
    positivity

theorem abs_v_le_dist {ε : ℝ} (hε0 : 0 ≤ ε) (t x : ℝ) : |v D ε t x| ≤ ε * |t - 5 / 16| ^ 2 := by
  have := abs_v_le_dist' D ε t x
  rwa [abs_of_nonneg hε0] at this

theorem abs_f_sub_f0_le' (ε : ℝ) (t x : ℝ) :
    |f D ε t x - f0 D t x| ≤ (|ε| * (D.Cη + 1) + ε ^ 2) * |t - 5 / 16| := by
  have hCη := D.Cη_nonneg
  have hfd : f D ε t x - f0 D t x = R D ε t x + ε * Lβv D ε t x := by
    simp only [f]; ring
  rw [hfd]
  by_cases hex : ∃ j, t ∈ I j
  · obtain ⟨j, htj⟩ := hex
    have hj1 : 1 ≤ j := one_le_of_mem_I htj
    have hℓ0 : 0 < ℓ j := ℓ_pos hj1
    have hd : ℓ j ≤ 5 / 16 - t := ℓ_le_dist_of_mem_I htj
    have hd2 : 1 / (16 * ((j : ℝ) + 1)) ≤ 5 / 16 - t := inv_le_dist_of_mem_I htj
    have hw0 : (0 : ℝ) < 1 / (16 * ((j : ℝ) + 1)) := by positivity
    have habs : |t - 5 / 16| = 5 / 16 - t := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have hR : |Rblock D ε j t x| ≤ |ε| * ((D.Cη + 1) * ℓ j) := abs_Rblock_le_ℓ' D ε hj1 t x
    have hL : |Lβv D ε t x| ≤ |ε| * (1 / (60 * ((j : ℝ) + 1))) :=
      abs_Lβv_le_of_mem_I' D ε hj1 htj x
    have hL' : |ε * Lβv D ε t x| ≤ |ε| * (|ε| * (1 / (60 * ((j : ℝ) + 1)))) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hL (abs_nonneg ε)
    rw [R_eq_block D ε htj, habs]
    have hA : |ε| * ((D.Cη + 1) * ℓ j) ≤ |ε| * (D.Cη + 1) * (5 / 16 - t) := by
      have h1 : (0 : ℝ) ≤ |ε| * (D.Cη + 1) := mul_nonneg (abs_nonneg ε) (by linarith)
      nlinarith [h1, hd, hℓ0]
    have hB : |ε| * (|ε| * (1 / (60 * ((j : ℝ) + 1)))) ≤ ε ^ 2 * (5 / 16 - t) := by
      have hee : |ε| * |ε| = ε ^ 2 := by
        rw [abs_mul_abs_self]; ring
      have hw : 1 / (60 * ((j : ℝ) + 1)) ≤ 5 / 16 - t := by
        have : 1 / (60 * ((j : ℝ) + 1)) ≤ 1 / (16 * ((j : ℝ) + 1)) := by
          refine one_div_le_one_div_of_le (by positivity) ?_
          have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
          linarith
        linarith
      have hsq : (0 : ℝ) ≤ ε ^ 2 := sq_nonneg ε
      have : |ε| * (|ε| * (1 / (60 * ((j : ℝ) + 1)))) = ε ^ 2 * (1 / (60 * ((j : ℝ) + 1))) := by
        rw [← mul_assoc, hee]
      rw [this]
      exact mul_le_mul_of_nonneg_left hw hsq
    calc |Rblock D ε j t x + ε * Lβv D ε t x|
        ≤ |Rblock D ε j t x| + |ε * Lβv D ε t x| := abs_add_le _ _
      _ ≤ |ε| * ((D.Cη + 1) * ℓ j) + |ε| * (|ε| * (1 / (60 * ((j : ℝ) + 1)))) :=
          add_le_add hR hL'
      _ ≤ (|ε| * (D.Cη + 1) + ε ^ 2) * (5 / 16 - t) := by nlinarith [hA, hB]
  · rw [not_exists] at hex
    rw [R_eq_zero D ε hex]
    have hL : Lβv D ε t x = 0 := by
      simp only [Lβv]
      rw [β_eq_zero D hex, βx_eq_zero D hex, vx_eq_zero D ε hex, vxx_eq_zero D ε hex]
      ring
    rw [hL, mul_zero, add_zero, abs_zero]
    have h1 : (0 : ℝ) ≤ |ε| * (D.Cη + 1) + ε ^ 2 := by
      have := mul_nonneg (abs_nonneg ε) (by linarith : (0 : ℝ) ≤ D.Cη + 1)
      nlinarith [sq_nonneg ε]
    exact mul_nonneg h1 (abs_nonneg _)

/-! ## The continuity statements -/

theorem continuous_f (ε : ℝ) : Continuous (fun q : ℝ × ℝ => f D ε q.1 q.2) := by
  have hdiff : Continuous (fun q : ℝ × ℝ => f D ε q.1 q.2 - f0 D q.1 q.2) := by
    refine continuous_of_blocks (D := D)
      (g := fun t x => f D ε t x - f0 D t x)
      (gb := fun j t x => Rblock D ε j t x
        + ε * (-(βxblock D j t x * vxblock D ε j t x)
          - βblock D j t x * vxxblock D ε j t x))
      (h := fun t => (|ε| * (D.Cη + 1) + ε ^ 2) * |t - 5 / 16|) ?_ ?_ ?_ ?_ ?_
    · intro j
      have h1 := continuous_Rblock D ε j
      have h2 := continuous_βxblock D j
      have h3 := continuous_vxblock D ε j
      have h4 := continuous_βblock D j
      have h5 := continuous_vxxblock D ε j
      fun_prop
    · intro j t hj x
      have hη : ∀ i, i ≠ j → ηj D i t = 0 := fun i hi => (hj i hi).1
      simp only [f, Lβv]
      rw [R_eq_block' D ε hj, β_eq_block' D hη, βx_eq_block' D hη, vx_eq_block' D ε hη,
        vxx_eq_block' D ε hη]
      ring
    · fun_prop
    · norm_num
    · intro t x
      exact abs_f_sub_f0_le' D ε t x
  have heqf : (fun q : ℝ × ℝ => f D ε q.1 q.2)
      = fun q : ℝ × ℝ => f0 D q.1 q.2 + (f D ε q.1 q.2 - f0 D q.1 q.2) := by
    funext q; ring
  rw [heqf]
  exact (continuous_f0 D).fun_add hdiff

theorem continuous_β : Continuous (fun q : ℝ × ℝ => β D q.1 q.2) := by
  refine continuous_of_blocks (D := D) (gb := fun j t x => βblock D j t x)
    (h := fun t => |t - 5 / 16| / 15) (fun j => continuous_βblock D j) ?_ ?_ ?_ ?_
  · intro j t hj x
    exact β_eq_block' D (fun i hi => (hj i hi).1) x
  · fun_prop
  · norm_num
  · intro t x
    exact abs_β_le_dist D t x

theorem continuous_a (ε : ℝ) : Continuous (fun q : ℝ × ℝ => a D ε q.1 q.2) := by
  have hβ := continuous_β D
  show Continuous fun q : ℝ × ℝ => 1 + ε * β D q.1 q.2
  fun_prop

theorem continuous_v (ε : ℝ) : Continuous (fun q : ℝ × ℝ => v D ε q.1 q.2) := by
  refine continuous_of_blocks (D := D) (gb := fun j t x => vblock D ε j t x)
    (h := fun t => |ε| * |t - 5 / 16| ^ 2) (fun j => continuous_vblock D ε j) ?_ ?_ ?_ ?_
  · intro j t hj x
    exact v_eq_block' D ε (fun i hi => (hj i hi).1) x
  · fun_prop
  · norm_num
  · intro t x
    exact abs_v_le_dist' D ε t x

theorem continuous_u (ε : ℝ) : Continuous (fun q : ℝ × ℝ => u D ε q.1 q.2) := by
  have h1 : Continuous D.ρ := continuous_ρ D
  have h2 : Continuous φ := continuous_φ
  have h3 := continuous_v D ε
  show Continuous fun q : ℝ × ℝ => D.ρ q.1 * φ q.2 + v D ε q.1 q.2
  fun_prop

end LionsC12

end
