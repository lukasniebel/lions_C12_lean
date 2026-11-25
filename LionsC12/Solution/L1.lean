module

public import LionsC12.Construction.Defs
public import LionsC12.Coefficient.Blocks
public import LionsC12.Coefficient.Support
public import LionsC12.Modes.Trig
public import LionsC12.Solution.Basic
public import LionsC12.Solution.Divergence
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Lemma 4.1: `∂_t u ∈ L¹(0,1;H)`

This file contains the `W^{1,1}(0,1;H)` part of Lemma 4.1 of the paper.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ### Pythagoras on a block -/

/-- On a block, Pythagoras: `‖∂_t u(t)‖² = (π/4) ∑_m y'_{j,m}(t)²` (`ρ' = 0` on `I_j`). -/
theorem utNormSq_of_mem_I (ε : ℝ) {j : ℕ} {t : ℝ} (ht : t ∈ I j) :
    utNormSq D ε t = π / 4 * ∑ m ∈ Finset.Icc 1 (M j), (y' D ε j m t) ^ 2 := by
  have hj : 1 ≤ j := one_le_of_mem_I ht
  have hfun : ut D ε t = fun x => ∑ m ∈ Finset.Icc 1 (M j), y' D ε j m t * p (K j m) x := by
    funext x
    rw [ut, ρ'_eq_zero_of_mem_I D ht, zero_mul, zero_add, vt_eq_block D ε ht x, vtblock]
  have hK : ∀ m ∈ Finset.Icc 1 (M j), 2 < K j m := fun m hm =>
    two_lt_K hj (Finset.mem_Icc.mp hm).1
  have hsep : ∀ m ∈ Finset.Icc 1 (M j), ∀ m' ∈ Finset.Icc 1 (M j), m < m' →
      K j m + 4 < K j m' := by
    intro m hm m' _ hmm'
    have h1 : 16 * K j m ≤ K j m' := K_le_of_lt hmm'
    have h2 : 2 < K j m := two_lt_K hj (Finset.mem_Icc.mp hm).1
    omega
  show normSq (ut D ε t) = _
  rw [hfun]
  exact normSq_sum_p (Finset.Icc 1 (M j)) (K j) (fun m => y' D ε j m t) hK hsep

theorem utNormSq_le_of_mem_I {ε : ℝ} (hε0 : 0 ≤ ε) {j : ℕ} {t : ℝ} (ht : t ∈ I j) :
    utNormSq D ε t ≤ π / 4 * (ε * (D.Cη + 1)) ^ 2 * (M j : ℝ) := by
  have hj : 1 ≤ j := one_le_of_mem_I ht
  rw [utNormSq_of_mem_I D ε ht]
  have hb : ∀ m ∈ Finset.Icc 1 (M j), (y' D ε j m t) ^ 2 ≤ (ε * (D.Cη + 1)) ^ 2 := by
    intro m _
    have h := abs_le.mp (abs_y'_le D hε0 hj m t)
    exact sq_le_sq' h.1 h.2
  have hcard : ((Finset.Icc 1 (M j)).card : ℝ) = (M j : ℝ) := by
    rw [Nat.card_Icc]; norm_num
  calc π / 4 * ∑ m ∈ Finset.Icc 1 (M j), (y' D ε j m t) ^ 2
      ≤ π / 4 * ∑ _m ∈ Finset.Icc 1 (M j), (ε * (D.Cη + 1)) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hb) (by positivity)
    _ = π / 4 * (ε * (D.Cη + 1)) ^ 2 * (M j : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring

/-! ### Off the blocks -/

/-- If all cutoffs and their derivatives vanish at `t`, then `∂_t u(t) = ρ'(t) φ`. -/
theorem utNormSq_of_ηj_eq_zero (ε : ℝ) {t : ℝ}
    (h : ∀ i, ηj D i t = 0) (h' : ∀ i, ηj' D i t = 0) :
    utNormSq D ε t = (D.ρ' t) ^ 2 * normSq φ := by
  have hz : ∀ (x : ℝ) (i : ℕ), vtblock D ε i t x = 0 := by
    intro x i
    rw [vtblock]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [y', h i, h' i]
    ring
  have hut : ut D ε t = fun x => D.ρ' t * φ x := by
    funext x
    show D.ρ' t * φ x + vt D ε t x = D.ρ' t * φ x
    rw [vt, finsum_eq_zero_of_forall_eq_zero (hz x), add_zero]
  show normSq (ut D ε t) = _
  rw [hut]
  show (∫ x in (0:ℝ)..π, (D.ρ' t * φ x) ^ 2) = D.ρ' t ^ 2 * normSq φ
  rw [normSq, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun x _ => by ring

theorem utNormSq_of_notMem (ε : ℝ) {t : ℝ} (ht : ∀ j, t ∉ I j) :
    utNormSq D ε t = (D.ρ' t) ^ 2 * normSq φ :=
  utNormSq_of_ηj_eq_zero D ε (fun i => ηj_eq_zero_of_notMem D (ht i))
    (fun i => ηj'_eq_zero_of_notMem D (ht i))

/-! ### The norm of the profile -/

theorem normSq_φ : normSq φ = 3 * π / 8 := by
  have h : normSq φ = ∫ x in (0:ℝ)..π, sin x ^ (2 + 2) := by
    rw [normSq]
    exact intervalIntegral.integral_congr fun x _ => by rw [φ]; ring
  rw [h, integral_sin_pow 2, integral_sin_sq]
  simp [Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero]
  ring

theorem utNormSq_nonneg (ε t : ℝ) : 0 ≤ utNormSq D ε t := normSq_nonneg (ut D ε t)

/-! ### Summability of `√(M_j) ℓ_j` -/

theorem ℓ_nonneg (j : ℕ) : 0 ≤ ℓ j := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; rw [ℓ_zero]
  · exact (ℓ_pos h).le

/-- `∑_j √(M_j) ℓ_j < ∞`. -/
theorem summable_sqrt_M_mul_ℓ : Summable (fun j : ℕ => Real.sqrt (M j : ℝ) * ℓ j) := by
  have hsum : Summable (fun n : ℕ => (((n : ℝ)) ^ (3/2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (Real.sqrt_nonneg _) (ℓ_nonneg j))
    (fun j => ?_) hsum
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    rw [ℓ_zero, mul_zero]
    positivity
  · have hj0 : (0:ℝ) < (j:ℝ) := by exact_mod_cast h
    have hj1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast h
    have hrw : ((j:ℝ)) ^ (3/2 : ℝ) = (j:ℝ) * Real.sqrt j := by
      rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hj0, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    rw [hrw]
    have hs : Real.sqrt (j:ℝ) > 0 := Real.sqrt_pos.mpr hj0
    have hsq : Real.sqrt (j:ℝ) * Real.sqrt (j:ℝ) = (j:ℝ) := Real.mul_self_sqrt hj0.le
    have hM : (M j : ℝ) = (j : ℝ) := by rw [M]
    have hkey : Real.sqrt (j:ℝ) * ((j:ℝ) * Real.sqrt (j:ℝ)) = (j:ℝ) * (j:ℝ) := by
      have h' : Real.sqrt (j:ℝ) * ((j:ℝ) * Real.sqrt (j:ℝ))
          = (j:ℝ) * (Real.sqrt (j:ℝ) * Real.sqrt (j:ℝ)) := by ring
      rw [h', hsq]
    rw [hM, ℓ, mul_one_div, inv_eq_one_div,
      div_le_div_iff₀ (by positivity) (mul_pos hj0 hs), hkey]
    nlinarith [hj1]

/-! ### Continuity away from the accumulation point -/

theorem continuous_y' (ε : ℝ) (j m : ℕ) : Continuous (y' D ε j m) := by
  have hθ := continuous_θ j m
  have hs : Continuous fun t : ℝ => sin (θ j m t) := Real.continuous_sin.comp' hθ
  have hc : Continuous fun t : ℝ => cos (θ j m t) := Real.continuous_cos.comp' hθ
  have hη := continuous_ηj D j
  have hη' := continuous_ηj' D j
  show Continuous fun t => -(ε / (2 * (K j m : ℝ) ^ 2)) *
    (ηj' D j t * (sin (θ j m t) - cos (θ j m t)) +
      ηj D j t * (K j m : ℝ) ^ 2 * (cos (θ j m t) + sin (θ j m t)))
  exact continuous_const.fun_mul
    ((hη'.fun_mul (hs.fun_sub hc)).fun_add
      ((hη.fun_mul continuous_const).fun_mul (hc.fun_add hs)))

/-- The support of `η_j` is contained in the "core" `[τ_j + ℓ_j/10, τ_j + 9 ℓ_j/10]`. -/
theorem ηj_core {i : ℕ} {t : ℝ} (h : ηj D i t ≠ 0) :
    τ i + ℓ i / 10 ≤ t ∧ t ≤ τ i + 9 * ℓ i / 10 :=
  let ⟨_, h1, h2⟩ := core_bounds D (Or.inl h)
  ⟨h1.le, h2.le⟩

/-- The support of `η_j'` is contained in the "core" `[τ_j + ℓ_j/10, τ_j + 9 ℓ_j/10]`. -/
theorem ηj'_core {i : ℕ} {t : ℝ} (h : ηj' D i t ≠ 0) :
    τ i + ℓ i / 10 ≤ t ∧ t ≤ τ i + 9 * ℓ i / 10 :=
  let ⟨_, h1, h2⟩ := core_bounds D (Or.inr h)
  ⟨h1.le, h2.le⟩

/-- Every point of `[1/4, 5/16)` which lies in no block is one of the `τ_j`. -/
theorem exists_eq_τ {t : ℝ} (h1 : (1:ℝ)/4 ≤ t) (h2 : t < 5/16) (h : ∀ i, t ∉ I i) :
    ∃ j : ℕ, 1 ≤ j ∧ t = τ j := by
  have hs : (0:ℝ) < 16 * (5/16 - t) := by linarith
  have hr1 : (1:ℝ) ≤ 1 / (16 * (5/16 - t)) := by
    rw [le_div_iff₀ hs]; linarith
  have hj1 : 1 ≤ ⌊1 / (16 * (5/16 - t))⌋₊ := (Nat.one_le_floor_iff _).mpr hr1
  set j : ℕ := ⌊1 / (16 * (5/16 - t))⌋₊ with hjdef
  have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj1
  have hjle : (j:ℝ) ≤ 1 / (16 * (5/16 - t)) := Nat.floor_le (by positivity)
  have hjlt : 1 / (16 * (5/16 - t)) < (j:ℝ) + 1 := Nat.lt_floor_add_one _
  have hA : (j:ℝ) * (16 * (5/16 - t)) ≤ 1 := (le_div_iff₀ hs).mp hjle
  have hB : (1:ℝ) < ((j:ℝ) + 1) * (16 * (5/16 - t)) := (div_lt_iff₀ hs).mp hjlt
  have hτj : τ j ≤ t := by
    rw [τ, sub_le_iff_le_add]
    rw [← sub_le_iff_le_add']
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 16 * (j:ℝ))]
    nlinarith
  have hτj1 : t < τ (j + 1) := by
    have hcast : ((j + 1 : ℕ) : ℝ) = (j:ℝ) + 1 := by push_cast; ring
    rw [τ, hcast, lt_sub_iff_add_lt, ← lt_sub_iff_add_lt']
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < 16 * ((j:ℝ) + 1))]
    nlinarith
  refine ⟨j, hj1, ?_⟩
  by_contra hne
  exact (h j) (Set.mem_Ioo.mpr ⟨lt_of_le_of_ne hτj (fun hc => hne hc.symm), hτj1⟩)

/-- `t ↦ ‖∂_t u(t)‖²_H` is continuous away from the accumulation point `5/16`. -/
theorem continuousOn_utNormSq (ε : ℝ) : ContinuousOn (utNormSq D ε) {5 / 16}ᶜ := by
  refine continuousOn_of_forall_continuousAt fun t₀ ht₀ => ?_
  have ht₀' : t₀ ≠ 5 / 16 := ht₀
  by_cases hmem : ∃ j, t₀ ∈ I j
  · obtain ⟨j, hj⟩ := hmem
    have hc : Continuous fun t => π / 4 * ∑ m ∈ Finset.Icc 1 (M j), (y' D ε j m t) ^ 2 :=
      continuous_const.fun_mul
        (continuous_finsetSum _ fun m _ => (continuous_pow 2).comp' (continuous_y' D ε j m))
    have hcont : ContinuousOn (utNormSq D ε) (I j) :=
      hc.continuousOn.congr fun t ht => utNormSq_of_mem_I D ε ht
    exact hcont.continuousAt ((isOpen_I j).mem_nhds hj)
  · -- all blocks vanish near `t₀`
    have hnot : ∀ j, t₀ ∉ I j := by
      intro j hj; exact hmem ⟨j, hj⟩
    have key : ∃ U : Set ℝ, IsOpen U ∧ t₀ ∈ U ∧
        ∀ t ∈ U, utNormSq D ε t = (D.ρ' t) ^ 2 * normSq φ := by
      by_cases hIcc : t₀ ∈ Set.Icc (1/4 : ℝ) (5/16)
      · have hlt : t₀ < 5 / 16 := lt_of_le_of_ne hIcc.2 ht₀'
        obtain ⟨j, hj1, hjeq⟩ := exists_eq_τ hIcc.1 hlt hnot
        refine ⟨Set.Ioo (τ j - ℓ j / 10) (τ j + ℓ j / 10), isOpen_Ioo, ?_, ?_⟩
        · have hℓ : 0 < ℓ j := ℓ_pos hj1
          rw [hjeq]
          constructor <;> [linarith; linarith]
        · intro t ht
          exact utNormSq_of_ηj_eq_zero D ε
            (fun i => ηj_eq_zero_near_τ D hj1 ht.1 ht.2 i)
            (fun i => ηj'_eq_zero_near_τ D hj1 ht.1 ht.2 i)
      · refine ⟨(Set.Icc (1/4 : ℝ) (5/16))ᶜ, isClosed_Icc.isOpen_compl, hIcc, ?_⟩
        intro t ht
        refine utNormSq_of_notMem D ε fun i => ?_
        refine notMem_I_of_notMem_Ico ?_ i
        intro hc
        exact ht (Set.mem_Icc.mpr ⟨hc.1, hc.2.le⟩)
    obtain ⟨U, hUopen, ht₀U, hUeq⟩ := key
    have hc : Continuous fun t => (D.ρ' t) ^ 2 * normSq φ :=
      ((continuous_pow 2).comp' D.ρ'_continuous).mul_const _
    exact (hc.continuousOn.congr hUeq).continuousAt (hUopen.mem_nhds ht₀U)

theorem aestronglyMeasurable_utNormSq (ε : ℝ) :
    MeasureTheory.AEStronglyMeasurable (utNormSq D ε)
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have h1 : MeasureTheory.AEStronglyMeasurable (utNormSq D ε)
      (MeasureTheory.volume.restrict ({(5:ℝ)/16}ᶜ)) :=
    (continuousOn_utNormSq D ε).aestronglyMeasurable (measurableSet_singleton _).compl
  have h2 := h1.restrict (s := Set.Icc (0:ℝ) 1)
  rw [MeasureTheory.Measure.restrict_restrict measurableSet_Icc] at h2
  refine h2.mono_measure (le_of_eq ?_)
  refine (MeasureTheory.Measure.restrict_congr_set ?_).symm
  show (Set.Icc (0:ℝ) 1 \ ({(5:ℝ)/16} : Set ℝ)) =ᵐ[MeasureTheory.volume]
    (Set.Icc (0:ℝ) 1 : Set ℝ)
  exact MeasureTheory.sdiff_null_ae_eq_self (MeasureTheory.measure_singleton _)

/-! ### Finiteness of the `L¹`-norm -/

theorem volume_I (j : ℕ) : MeasureTheory.volume (I j) = ENNReal.ofReal (ℓ j) := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; rw [I_zero, ℓ_zero]; simp
  · show MeasureTheory.volume (Set.Ioo (τ j) (τ (j + 1))) = _
    rw [Real.volume_Ioo, ← τ_add_ℓ h]
    congr 1
    ring

theorem lintegral_sqrt_utNormSq_lt_top {ε : ℝ} (hε0 : 0 ≤ ε) :
    ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (utNormSq D ε t)) < ⊤ := by
  set g : ℝ → ENNReal := fun t => ENNReal.ofReal (Real.sqrt (utNormSq D ε t)) with hgdef
  set c : ℝ := Real.sqrt (π / 4 * (ε * (D.Cη + 1)) ^ 2) with hcdef
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  -- the bound on a block
  have hblock : ∀ (j : ℕ), ∀ t ∈ I j, g t ≤ ENNReal.ofReal (c * Real.sqrt (M j : ℝ)) := by
    intro j t ht
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : Real.sqrt (utNormSq D ε t)
        ≤ Real.sqrt (π / 4 * (ε * (D.Cη + 1)) ^ 2 * (M j : ℝ)) :=
      Real.sqrt_le_sqrt (utNormSq_le_of_mem_I D hε0 ht)
    rwa [Real.sqrt_mul (by positivity)] at h1
  -- the bound off the blocks
  have hoff : ∀ t ∈ Set.Icc (0:ℝ) 1 \ ⋃ j, I j,
      g t ≤ ENNReal.ofReal (D.Cρ * Real.sqrt (normSq φ)) := by
    intro t ht
    refine ENNReal.ofReal_le_ofReal ?_
    have hnot : ∀ j, t ∉ I j := by
      intro j hj
      exact ht.2 (Set.mem_iUnion.mpr ⟨j, hj⟩)
    rw [utNormSq_of_notMem D ε hnot, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    exact mul_le_mul_of_nonneg_right (D.ρ'_bound t) (Real.sqrt_nonneg _)
  have hsub : Set.Icc (0:ℝ) 1 ⊆ (Set.Icc (0:ℝ) 1 \ ⋃ j, I j) ∪ ⋃ j, I j := by
    intro t ht
    by_cases h : t ∈ ⋃ j, I j
    · exact Or.inr h
    · exact Or.inl ⟨ht, h⟩
  -- part one
  have hpart1 : ∫⁻ t in Set.Icc (0:ℝ) 1 \ ⋃ j, I j, g t < ⊤ := by
    have hmeas : MeasurableSet (Set.Icc (0:ℝ) 1 \ ⋃ j, I j) :=
      measurableSet_Icc.diff (MeasurableSet.iUnion fun j => (isOpen_I j).measurableSet)
    calc ∫⁻ t in Set.Icc (0:ℝ) 1 \ ⋃ j, I j, g t
        ≤ ∫⁻ _t in Set.Icc (0:ℝ) 1 \ ⋃ j, I j,
            ENNReal.ofReal (D.Cρ * Real.sqrt (normSq φ)) :=
          MeasureTheory.lintegral_mono_ae
            (MeasureTheory.ae_restrict_of_forall_mem hmeas hoff)
      _ = ENNReal.ofReal (D.Cρ * Real.sqrt (normSq φ)) *
            MeasureTheory.volume (Set.Icc (0:ℝ) 1 \ ⋃ j, I j) :=
          MeasureTheory.setLIntegral_const _ _
      _ < ⊤ := by
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
          refine lt_of_le_of_lt (MeasureTheory.measure_mono Set.sdiff_subset) ?_
          rw [Real.volume_Icc]
          exact ENNReal.ofReal_lt_top
  -- part two
  have hstep : ∀ j : ℕ, ∫⁻ t in I j, g t
      ≤ ENNReal.ofReal (c * (Real.sqrt (M j : ℝ) * ℓ j)) := by
    intro j
    calc ∫⁻ t in I j, g t
        ≤ ∫⁻ _t in I j, ENNReal.ofReal (c * Real.sqrt (M j : ℝ)) :=
          MeasureTheory.lintegral_mono_ae
            (MeasureTheory.ae_restrict_of_forall_mem (isOpen_I j).measurableSet (hblock j))
      _ = ENNReal.ofReal (c * Real.sqrt (M j : ℝ)) * MeasureTheory.volume (I j) :=
          MeasureTheory.setLIntegral_const _ _
      _ = ENNReal.ofReal (c * Real.sqrt (M j : ℝ)) * ENNReal.ofReal (ℓ j) := by
          rw [volume_I]
      _ = ENNReal.ofReal (c * (Real.sqrt (M j : ℝ) * ℓ j)) := by
          rw [← ENNReal.ofReal_mul (by positivity), mul_assoc]
  have hsummable : Summable (fun j : ℕ => c * (Real.sqrt (M j : ℝ) * ℓ j)) :=
    summable_sqrt_M_mul_ℓ.mul_left c
  have hpart2 : ∫⁻ t in ⋃ j, I j, g t < ⊤ := by
    calc ∫⁻ t in ⋃ j, I j, g t ≤ ∑' j : ℕ, ∫⁻ t in I j, g t :=
          MeasureTheory.lintegral_iUnion_le _ _
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (c * (Real.sqrt (M j : ℝ) * ℓ j)) :=
          ENNReal.tsum_le_tsum hstep
      _ = ENNReal.ofReal (∑' j : ℕ, c * (Real.sqrt (M j : ℝ) * ℓ j)) :=
          (ENNReal.ofReal_tsum_of_nonneg
            (fun n => mul_nonneg hc0 (mul_nonneg (Real.sqrt_nonneg _) (ℓ_nonneg n)))
            hsummable).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  calc ∫⁻ t in Set.Icc (0:ℝ) 1, g t
      ≤ ∫⁻ t in (Set.Icc (0:ℝ) 1 \ ⋃ j, I j) ∪ ⋃ j, I j, g t :=
        MeasureTheory.lintegral_mono_set hsub
    _ ≤ (∫⁻ t in Set.Icc (0:ℝ) 1 \ ⋃ j, I j, g t) + ∫⁻ t in ⋃ j, I j, g t :=
        MeasureTheory.lintegral_union_le _ _ _
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hpart1, hpart2⟩

/-- Lemma 4.1: `∂_t u ∈ L¹(0,1;H)`. -/
theorem integrableOn_sqrt_utNormSq {ε : ℝ} (hε0 : 0 ≤ ε) :
    MeasureTheory.IntegrableOn (fun t => Real.sqrt (utNormSq D ε t)) (Set.Icc (0 : ℝ) 1) := by
  constructor
  · exact Real.continuous_sqrt.comp_aestronglyMeasurable (aestronglyMeasurable_utNormSq D ε)
  · rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg _)]
    exact lintegral_sqrt_utNormSq_lt_top D hε0

end LionsC12

end
