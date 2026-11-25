module

public import LionsC12.Construction.Defs
public import LionsC12.Coefficient.Blocks
public import LionsC12.Coefficient.Support
public import LionsC12.Modes.Trig
public import LionsC12.Solution.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.Compact

/-!
# Proposition 3.4: blow-up of the frozen operator on the fixed domain element `φ`

This file proves that although `φ ∈ D₀ = D(A_{0,H})` is a fixed element of the common
operator domain, the family `t ↦ A_H(t) φ` is unbounded in `H = L²(0,π)` as `t` ranges
over `[0,1]`.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ## The frozen operator applied to `φ` -/

/-- `(𝒜(t)φ)(x) = -∂_x(𝔞(t,x) φ'(x)) = -ε (∂_x β) φ' - 𝔞 φ''`. -/
def Aφ (ε : ℝ) (t x : ℝ) : ℝ := -(ε * βx D t x * φ' x) - a D ε t x * φ'' x

theorem hasDerivAt_Aφ_flux (ε : ℝ) (t x : ℝ) :
    HasDerivAt (fun x => a D ε t x * φ' x) (-(Aφ D ε t x)) x := by
  have h := HasDerivAt.fun_mul (hasDerivAt_a_x D ε t x) (hasDerivAt_φ' x)
  refine h.congr_deriv ?_
  simp only [Aφ]
  ring

/-- `L_{β(t)} φ = -∂_x(β ∂_x φ) = -(∂_x β) φ' - β φ''`. -/
def Lβφ (t x : ℝ) : ℝ := -(βx D t x * φ' x) - β D t x * φ'' x

theorem Aφ_eq (ε : ℝ) (t x : ℝ) : Aφ D ε t x = ε * Lβφ D t x - φ'' x := by
  simp only [Aφ, Lβφ, a]
  ring

/-! ## Blockwise formula for `L_β φ` -/

theorem Lβφ_of_mem_I {j : ℕ} {t : ℝ} (ht : t ∈ I j) (x : ℝ) :
    Lβφ D t x = ∑ m ∈ Finset.Icc 1 (M j),
      ηj D j t * sin (θ j m t) * (p (K j m) x - 2 * ((K j m : ℝ))⁻¹ * c (K j m) x) := by
  have hβ : β D t x = βblock D j t x := β_eq_block D ht x
  have hβx : βx D t x = βxblock D j t x := βx_eq_block D ht x
  show -(βx D t x * φ' x) - β D t x * φ'' x = _
  rw [hβ, hβx]
  have e1 : βxblock D j t x * φ' x
      = ∑ m ∈ Finset.Icc 1 (M j), -(ηj D j t * sin (θ j m t) * sin (K j m * x)) * φ' x := by
    unfold βxblock; rw [Finset.sum_mul]
  have e2 : βblock D j t x * φ'' x
      = ∑ m ∈ Finset.Icc 1 (M j),
          (ηj D j t * ((K j m : ℝ))⁻¹ * sin (θ j m t) * cos (K j m * x)) * φ'' x := by
    unfold βblock βmode; rw [Finset.sum_mul]
  rw [e1, e2, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  simp only [φ', φ'', p, c]
  ring

theorem Lβφ_eq_zero {t : ℝ} (ht : ∀ j, t ∉ I j) (x : ℝ) : Lβφ D t x = 0 := by
  have hβ : β D t x = 0 := β_eq_zero D ht x
  have hβx : βx D t x = 0 := βx_eq_zero D ht x
  show -(βx D t x * φ' x) - β D t x * φ'' x = 0
  rw [hβ, hβx]; ring

/-! ## Pythagoras with the companion modes -/

private lemma integral_pc_comb (K L : ℕ) (α β A B C E : ℝ)
    (hA : (∫ x in (0 : ℝ)..π, p K x * p L x) = A)
    (hB : (∫ x in (0 : ℝ)..π, p K x * c L x) = B)
    (hC : (∫ x in (0 : ℝ)..π, c K x * p L x) = C)
    (hE : (∫ x in (0 : ℝ)..π, c K x * c L x) = E) :
    (∫ x in (0 : ℝ)..π, (p K x - α * c K x) * (p L x - β * c L x))
      = A - β * B - α * C + α * β * E := by
  have hi : ∀ (r : ℝ) (f g : ℝ → ℝ), Continuous f → Continuous g →
      IntervalIntegrable (fun x : ℝ => r * (f x * g x)) MeasureTheory.volume 0 π :=
    fun r f g hf hg => (continuous_const.fun_mul (hf.fun_mul hg)).intervalIntegrable 0 π
  have key : ∀ x : ℝ, (p K x - α * c K x) * (p L x - β * c L x)
      = 1 * (p K x * p L x) + (-β) * (p K x * c L x) + (-α) * (c K x * p L x)
        + (α * β) * (c K x * c L x) := by
    intro x; ring
  simp_rw [key]
  rw [intervalIntegral.integral_add
      (((hi 1 (p K) (p L) (continuous_p K) (continuous_p L)).add
        (hi (-β) (p K) (c L) (continuous_p K) (continuous_c L))).add
        (hi (-α) (c K) (p L) (continuous_c K) (continuous_p L)))
      (hi (α * β) (c K) (c L) (continuous_c K) (continuous_c L)),
    intervalIntegral.integral_add
      ((hi 1 (p K) (p L) (continuous_p K) (continuous_p L)).add
        (hi (-β) (p K) (c L) (continuous_p K) (continuous_c L)))
      (hi (-α) (c K) (p L) (continuous_c K) (continuous_p L)),
    intervalIntegral.integral_add
      (hi 1 (p K) (p L) (continuous_p K) (continuous_p L))
      (hi (-β) (p K) (c L) (continuous_p K) (continuous_c L)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hA, hB, hC, hE]
  ring

theorem normSq_sum_pc (s : Finset ℕ) (Kf : ℕ → ℕ) (a : ℕ → ℝ) (hK : ∀ m ∈ s, 4 < Kf m)
    (hsep : ∀ m ∈ s, ∀ m' ∈ s, m < m' → Kf m + 4 < Kf m') :
    normSq (fun x => ∑ m ∈ s, a m * (p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x))
      = π / 4 * ∑ m ∈ s, (a m) ^ 2 * (1 + 4 * ((Kf m : ℝ))⁻¹ ^ 2) := by
  have hK2 : ∀ m ∈ s, 2 < Kf m := fun m hm => by have := hK m hm; omega
  have main : ∀ m ∈ s, ∀ m' ∈ s, m < m' →
      (∫ x in (0 : ℝ)..π, (p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x) *
        (p (Kf m') x - 2 * ((Kf m' : ℝ))⁻¹ * c (Kf m') x)) = 0 := by
    intro m hm m' hm' h
    have hA := inner_p_p (hK2 m hm) (hsep m hm m' hm' h)
    have hB := inner_p_c' (hK2 m hm) (hsep m hm m' hm' h)
    have hC := inner_c_p (hK2 m hm) (hsep m hm m' hm' h)
    have hE := inner_c_c (hK2 m hm) (hsep m hm m' hm' h)
    have h0 := integral_pc_comb (Kf m) (Kf m') (2 * ((Kf m : ℝ))⁻¹) (2 * ((Kf m' : ℝ))⁻¹)
      0 0 0 0 hA hB hC hE
    simpa using h0
  have horth : ∀ m ∈ s, ∀ m' ∈ s, m ≠ m' →
      (∫ x in (0 : ℝ)..π, (p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x) *
        (p (Kf m') x - 2 * ((Kf m' : ℝ))⁻¹ * c (Kf m') x)) = 0 := by
    intro m hm m' hm' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact main m hm m' hm' h
    · have h2 := main m' hm' m hm h
      have hcomm : (fun x : ℝ => (p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x) *
            (p (Kf m') x - 2 * ((Kf m' : ℝ))⁻¹ * c (Kf m') x))
          = fun x : ℝ => (p (Kf m') x - 2 * ((Kf m' : ℝ))⁻¹ * c (Kf m') x) *
            (p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x) := by
        funext x; ring
      show (∫ x in (0 : ℝ)..π, (p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x) *
        (p (Kf m') x - 2 * ((Kf m' : ℝ))⁻¹ * c (Kf m') x)) = 0
      rw [hcomm]; exact h2
  have hdiag : ∀ m ∈ s, (∫ x in (0 : ℝ)..π, (p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x) *
      (p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x)) = π / 4 * (1 + 4 * ((Kf m : ℝ))⁻¹ ^ 2) := by
    intro m hm
    have hK' := hK2 m hm
    have hA : (∫ x in (0 : ℝ)..π, p (Kf m) x * p (Kf m) x) = π / 4 := by
      have h := normSq_p hK'; rw [normSq_eq_inner] at h; exact h
    have hB : (∫ x in (0 : ℝ)..π, p (Kf m) x * c (Kf m) x) = 0 := inner_p_c hK'
    have hC : (∫ x in (0 : ℝ)..π, c (Kf m) x * p (Kf m) x) = 0 :=
      (inner_comm (p (Kf m)) (c (Kf m))).symm.trans (inner_p_c hK')
    have hE : (∫ x in (0 : ℝ)..π, c (Kf m) x * c (Kf m) x) = π / 4 := by
      have h := normSq_c hK'; rw [normSq_eq_inner] at h; exact h
    have h0 := integral_pc_comb (Kf m) (Kf m) (2 * ((Kf m : ℝ))⁻¹) (2 * ((Kf m : ℝ))⁻¹)
      (π / 4) 0 0 (π / 4) hA hB hC hE
    rw [h0]; ring
  have hcont : ∀ (m m' : ℕ) (r : ℝ),
      IntervalIntegrable (fun x : ℝ => r * ((p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x) *
        (p (Kf m') x - 2 * ((Kf m' : ℝ))⁻¹ * c (Kf m') x))) MeasureTheory.volume 0 π := by
    intro m m' r
    apply Continuous.intervalIntegrable
    exact continuous_const.fun_mul
      (((continuous_p _).sub (continuous_const.fun_mul (continuous_c _))).fun_mul
        ((continuous_p _).sub (continuous_const.fun_mul (continuous_c _))))
  show (∫ x in (0 : ℝ)..π, (∑ m ∈ s, a m * (p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x)) ^ 2)
      = π / 4 * ∑ m ∈ s, (a m) ^ 2 * (1 + 4 * ((Kf m : ℝ))⁻¹ ^ 2)
  have key : ∀ x : ℝ, (∑ m ∈ s, a m * (p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x)) ^ 2
      = ∑ m ∈ s, ∑ m' ∈ s, (a m * a m') *
          ((p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x) *
            (p (Kf m') x - 2 * ((Kf m' : ℝ))⁻¹ * c (Kf m') x)) := by
    intro x
    rw [pow_two, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by ring
  simp_rw [key]
  have hsum_int : ∀ m ∈ s, IntervalIntegrable
      (fun x : ℝ => ∑ m' ∈ s, (a m * a m') *
        ((p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x) *
          (p (Kf m') x - 2 * ((Kf m' : ℝ))⁻¹ * c (Kf m') x))) MeasureTheory.volume 0 π := by
    intro m _
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum s fun m' _ =>
      continuous_const.fun_mul
        (((continuous_p _).sub (continuous_const.fun_mul (continuous_c _))).fun_mul
          ((continuous_p _).sub (continuous_const.fun_mul (continuous_c _))))
  rw [intervalIntegral.integral_finsetSum hsum_int]
  have hterm : ∀ m ∈ s, (∫ x in (0 : ℝ)..π, ∑ m' ∈ s, (a m * a m') *
        ((p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x) *
          (p (Kf m') x - 2 * ((Kf m' : ℝ))⁻¹ * c (Kf m') x)))
      = π / 4 * (a m) ^ 2 * (1 + 4 * ((Kf m : ℝ))⁻¹ ^ 2) := by
    intro m hm
    have hint : ∀ m' ∈ s, IntervalIntegrable
        (fun x : ℝ => (a m * a m') *
          ((p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x) *
            (p (Kf m') x - 2 * ((Kf m' : ℝ))⁻¹ * c (Kf m') x))) MeasureTheory.volume 0 π :=
      fun m' _ => hcont m m' (a m * a m')
    rw [intervalIntegral.integral_finsetSum hint]
    have hsingle : (∑ m' ∈ s, ∫ x in (0 : ℝ)..π, (a m * a m') *
          ((p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x) *
            (p (Kf m') x - 2 * ((Kf m' : ℝ))⁻¹ * c (Kf m') x)))
        = ∫ x in (0 : ℝ)..π, (a m * a m) *
            ((p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x) *
              (p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x)) := by
      refine Finset.sum_eq_single m ?_ ?_
      · intro m' hm' hne
        rw [intervalIntegral.integral_const_mul, horth m hm m' hm' (Ne.symm hne), mul_zero]
      · intro hns; exact absurd hm hns
    rw [hsingle, intervalIntegral.integral_const_mul, hdiag m hm]
    ring
  have hterm' : ∀ m ∈ s, (∫ x in (0 : ℝ)..π, ∑ m' ∈ s, (a m * a m') *
        ((p (Kf m) x - 2 * ((Kf m : ℝ))⁻¹ * c (Kf m) x) *
          (p (Kf m') x - 2 * ((Kf m' : ℝ))⁻¹ * c (Kf m') x)))
      = π / 4 * ((a m) ^ 2 * (1 + 4 * ((Kf m : ℝ))⁻¹ ^ 2)) := by
    intro m hm; rw [hterm m hm]; ring
  rw [Finset.sum_congr rfl hterm', ← Finset.mul_sum]

/-! ## Continuity of `t ↦ L_β(t) φ` -/

private lemma continuous_Lβφ (t : ℝ) : Continuous (Lβφ D t) := by
  by_cases hc : ∀ j, t ∉ I j
  · have heq : Lβφ D t = fun _ => (0 : ℝ) := funext fun x => Lβφ_eq_zero D hc x
    rw [heq]; exact continuous_const
  · simp only [not_forall, not_not] at hc
    obtain ⟨j, hj⟩ := hc
    have heq : Lβφ D t = fun x => ∑ m ∈ Finset.Icc 1 (M j),
        ηj D j t * sin (θ j m t) * (p (K j m) x - 2 * ((K j m : ℝ))⁻¹ * c (K j m) x) :=
      funext fun x => Lβφ_of_mem_I D hj x
    rw [heq]
    exact continuous_finsetSum _ fun m _ =>
      continuous_const.fun_mul ((continuous_p _).sub (continuous_const.fun_mul (continuous_c _)))

/-! ## Orthogonality of `L_β φ` and `φ''` -/

private lemma inner_pc_φ''_eq_zero {K : ℕ} (hK : 512 ≤ K) :
    (∫ x in (0 : ℝ)..π, (p K x - 2 * ((K : ℝ))⁻¹ * c K x) * φ'' x) = 0 := by
  have hφ'' : ∀ x : ℝ, φ'' x = 2 * cos (2 * x) := by intro x; simp [φ'']
  have key : ∀ x : ℝ, (p K x - 2 * ((K : ℝ))⁻¹ * c K x) * φ'' x
      = (1 - 2 * ((K : ℝ))⁻¹) * (cos (((K : ℝ) - 2) * x) * cos (2 * x))
        - (1 + 2 * ((K : ℝ))⁻¹) * (cos (((K : ℝ) + 2) * x) * cos (2 * x)) := by
    intro x; rw [hφ'', p_eq, c_eq]; ring
  simp_rw [key]
  have h2K : (2 : ℕ) ≤ K := by omega
  have hc1 : (K : ℝ) - 2 = ((K - 2 : ℕ) : ℝ) := by
    have h : ((K - 2 : ℕ) : ℝ) = ((K : ℕ) : ℝ) - ((2 : ℕ) : ℝ) := Nat.cast_sub h2K
    simpa using h.symm
  have hc2 : (K : ℝ) + 2 = ((K + 2 : ℕ) : ℝ) := by push_cast; ring
  have hcos2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [hc1, hc2, hcos2]
  have hne1 : (K - 2 : ℕ) ≠ 2 := by omega
  have hne2 : (K + 2 : ℕ) ≠ 2 := by omega
  have hi1 : (∫ x in (0 : ℝ)..π, cos (((K - 2 : ℕ) : ℝ) * x) * cos (((2 : ℕ) : ℝ) * x)) = 0 := by
    rw [integral_cos_mul_cos, ite_eq_right hne1]
  have hi2 : (∫ x in (0 : ℝ)..π, cos (((K + 2 : ℕ) : ℝ) * x) * cos (((2 : ℕ) : ℝ) * x)) = 0 := by
    rw [integral_cos_mul_cos, ite_eq_right hne2]
  have hcont1 : Continuous fun x : ℝ => cos (((K - 2 : ℕ) : ℝ) * x) * cos (((2 : ℕ) : ℝ) * x) :=
    (continuous_cos_mul _).fun_mul (continuous_cos_mul _)
  have hcont2 : Continuous fun x : ℝ => cos (((K + 2 : ℕ) : ℝ) * x) * cos (((2 : ℕ) : ℝ) * x) :=
    (continuous_cos_mul _).fun_mul (continuous_cos_mul _)
  rw [intervalIntegral.integral_sub
      ((hcont1.const_mul _).intervalIntegrable 0 π) ((hcont2.const_mul _).intervalIntegrable 0 π),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hi1, hi2]
  ring

theorem inner_Lβφ_φ'' (t : ℝ) : inner (Lβφ D t) φ'' = 0 := by
  by_cases hc : ∀ j, t ∉ I j
  · have heq : Lβφ D t = fun _ => (0 : ℝ) := funext fun x => Lβφ_eq_zero D hc x
    show (∫ x in (0 : ℝ)..π, Lβφ D t x * φ'' x) = 0
    rw [heq]; simp
  · simp only [not_forall, not_not] at hc
    obtain ⟨j, hj⟩ := hc
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · exact absurd hj (by rw [I_zero]; exact Set.notMem_empty _)
      · exact h
    have heq : Lβφ D t = fun x => ∑ m ∈ Finset.Icc 1 (M j),
        ηj D j t * sin (θ j m t) * (p (K j m) x - 2 * ((K j m : ℝ))⁻¹ * c (K j m) x) :=
      funext fun x => Lβφ_of_mem_I D hj x
    show (∫ x in (0 : ℝ)..π, Lβφ D t x * φ'' x) = 0
    have heq2 : (fun x => Lβφ D t x * φ'' x) = fun x => ∑ m ∈ Finset.Icc 1 (M j),
        (ηj D j t * sin (θ j m t)) *
          ((p (K j m) x - 2 * ((K j m : ℝ))⁻¹ * c (K j m) x) * φ'' x) := by
      funext x; rw [heq]; simp only; rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [heq2]
    have hint : ∀ m ∈ Finset.Icc 1 (M j), IntervalIntegrable
        (fun x => (ηj D j t * sin (θ j m t)) *
          ((p (K j m) x - 2 * ((K j m : ℝ))⁻¹ * c (K j m) x) * φ'' x))
        MeasureTheory.volume 0 π := by
      intro m _
      apply Continuous.intervalIntegrable
      apply continuous_const.fun_mul
      apply Continuous.fun_mul _ (by show Continuous fun x => 2 * cos (2 * x); fun_prop)
      exact (continuous_p _).sub (continuous_const.fun_mul (continuous_c _))
    rw [intervalIntegral.integral_finsetSum hint]
    apply Finset.sum_eq_zero
    intro m hm
    rw [intervalIntegral.integral_const_mul]
    have hK512 : 512 ≤ K j m := K_ge hj1 (Finset.mem_Icc.mp hm).1
    rw [inner_pc_φ''_eq_zero hK512, mul_zero]

/-! ## `normSq (Aφ)` decomposition -/

theorem normSq_Aφ (ε : ℝ) (t : ℝ) : normSq (Aφ D ε t) = ε ^ 2 * normSq (Lβφ D t) + normSq φ'' := by
  have hfun : Aφ D ε t = fun x => ε * Lβφ D t x - φ'' x := funext fun x => Aφ_eq D ε t x
  have hcontL : Continuous (Lβφ D t) := continuous_Lβφ D t
  have hcontφ'' : Continuous φ'' := by show Continuous fun x => 2 * cos (2 * x); fun_prop
  show (∫ x in (0 : ℝ)..π, Aφ D ε t x ^ 2) = ε ^ 2 * normSq (Lβφ D t) + normSq φ''
  rw [hfun]
  have key : ∀ x : ℝ, (ε * Lβφ D t x - φ'' x) ^ 2
      = ε ^ 2 * (Lβφ D t x) ^ 2 + (-(2 * ε)) * (Lβφ D t x * φ'' x) + (φ'' x) ^ 2 := by
    intro x; ring
  simp_rw [key]
  have hi1 : IntervalIntegrable (fun x => ε ^ 2 * (Lβφ D t x) ^ 2) MeasureTheory.volume 0 π :=
    (continuous_const.mul (hcontL.pow 2)).intervalIntegrable 0 π
  have hi2 : IntervalIntegrable (fun x => (-(2 * ε)) * (Lβφ D t x * φ'' x))
      MeasureTheory.volume 0 π :=
    (continuous_const.fun_mul (hcontL.fun_mul hcontφ'')).intervalIntegrable 0 π
  have hi3 : IntervalIntegrable (fun x => (φ'' x) ^ 2) MeasureTheory.volume 0 π :=
    (hcontφ''.pow 2).intervalIntegrable 0 π
  rw [intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have e1 : (∫ x in (0 : ℝ)..π, (Lβφ D t x) ^ 2) = normSq (Lβφ D t) := rfl
  have e2 : (∫ x in (0 : ℝ)..π, (φ'' x) ^ 2) = normSq φ'' := rfl
  have e3 : (∫ x in (0 : ℝ)..π, Lβφ D t x * φ'' x) = inner (Lβφ D t) φ'' := rfl
  rw [e1, e3, e2, inner_Lβφ_φ'' D t]
  ring

/-! ## Lower bound for `‖L_β φ‖²` on the middle third -/

theorem normSq_Lβφ_on_J {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ J j) :
    π / 4 * ∑ m ∈ Finset.Icc 1 (M j), sin (θ j m t) ^ 2 ≤ normSq (Lβφ D t) := by
  have htI : t ∈ I j := J_subset_I hj ht
  have hη : ηj D j t = 1 := ηj_eq_one_of_mem_J D hj ht
  have heq : Lβφ D t = fun x => ∑ m ∈ Finset.Icc 1 (M j),
      sin (θ j m t) * (p (K j m) x - 2 * ((K j m : ℝ))⁻¹ * c (K j m) x) := by
    funext x
    rw [Lβφ_of_mem_I D htI x]
    exact Finset.sum_congr rfl fun m _ => by rw [hη]; ring
  have hK4 : ∀ m ∈ Finset.Icc 1 (M j), 4 < K j m := fun m hm => by
    have := K_ge hj (Finset.mem_Icc.mp hm).1; omega
  have hsep : ∀ m ∈ Finset.Icc 1 (M j), ∀ m' ∈ Finset.Icc 1 (M j), m < m' → K j m + 4 < K j m' := by
    intro m hm m' _ hmm'
    have h1 : 16 * K j m ≤ K j m' := K_le_of_lt hmm'
    have h2 : 512 ≤ K j m := K_ge hj (Finset.mem_Icc.mp hm).1
    omega
  have hns := normSq_sum_pc (Finset.Icc 1 (M j)) (K j) (fun m => sin (θ j m t)) hK4 hsep
  calc π / 4 * ∑ m ∈ Finset.Icc 1 (M j), sin (θ j m t) ^ 2
      ≤ π / 4 * ∑ m ∈ Finset.Icc 1 (M j), sin (θ j m t) ^ 2 * (1 + 4 * ((K j m : ℝ))⁻¹ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro m _
        nlinarith [sq_nonneg (sin (θ j m t)), sq_nonneg ((K j m : ℝ))⁻¹,
          mul_nonneg (sq_nonneg (sin (θ j m t))) (sq_nonneg ((K j m : ℝ))⁻¹)]
    _ = normSq (Lβφ D t) := by rw [heq]; exact hns.symm

/-! ## Lower bound for `∫_{J_j} sin² θ_{j,m}` -/

theorem integral_sin_sq_J {j : ℕ} (hj : 1 ≤ j) {m : ℕ} (hm : 1 ≤ m) :
    ℓ j / 12 ≤ ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), sin (θ j m t) ^ 2 := by
  have hℓ : 0 < ℓ j := ℓ_pos hj
  have hKn : 0 < K j m := K_pos hj
  have hKpos : (0 : ℝ) < (K j m : ℝ) := by exact_mod_cast hKn
  obtain ⟨cc, hcdef⟩ : ∃ cc : ℝ, cc = 2 * (K j m : ℝ) ^ 2 := ⟨_, rfl⟩
  have hcpos : 0 < cc := by rw [hcdef]; positivity
  have hcne : cc ≠ 0 := ne_of_gt hcpos
  have hid : ∀ t : ℝ, sin (θ j m t) ^ 2 = 1 / 2 + (-(1 / 2)) * cos (cc * (t - τ j)) := by
    intro t
    have hθt : θ j m t = (K j m : ℝ) ^ 2 * (t - τ j) := rfl
    have h1 : cc * (t - τ j) = 2 * θ j m t := by rw [hcdef, hθt]; ring
    rw [h1]
    have h := Real.cos_two_mul (θ j m t)
    have hp := Real.sin_sq_add_cos_sq (θ j m t)
    nlinarith [h, hp]
  have hcont : Continuous fun t : ℝ => cos (cc * (t - τ j)) :=
    Real.continuous_cos.comp' (continuous_const.mul (continuous_id.sub continuous_const))
  have hF : ∀ t ∈ Set.uIcc (τ j + ℓ j / 3) (τ j + 2 * ℓ j / 3),
      HasDerivAt (fun s : ℝ => (1 / cc) * sin (cc * (s - τ j))) (cos (cc * (t - τ j))) t := by
    intro t _
    have h0 : HasDerivAt (fun s : ℝ => s - τ j) 1 t := (hasDerivAt_id t).sub_const (τ j)
    have h1 : HasDerivAt (fun s : ℝ => cc * (s - τ j)) cc t := by simpa using h0.const_mul cc
    have h2 : HasDerivAt (fun s : ℝ => (1 / cc) * sin (cc * (s - τ j)))
        ((1 / cc) * (cos (cc * (t - τ j)) * cc)) t := h1.sin.const_mul (1 / cc)
    have h3 : (1 / cc) * (cos (cc * (t - τ j)) * cc) = cos (cc * (t - τ j)) := by
      field_simp
    rwa [h3] at h2
  have hcos : ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), cos (cc * (t - τ j))
      = (1 / cc) * sin (cc * (τ j + 2 * ℓ j / 3 - τ j))
        - (1 / cc) * sin (cc * (τ j + ℓ j / 3 - τ j)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable _ _)
  have hval : ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), sin (θ j m t) ^ 2
      = (1 / 2) * ((τ j + 2 * ℓ j / 3) - (τ j + ℓ j / 3))
        + (-(1 / 2)) * ((1 / cc) * sin (cc * (τ j + 2 * ℓ j / 3 - τ j))
            - (1 / cc) * sin (cc * (τ j + ℓ j / 3 - τ j))) := by
    have h1 : ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), sin (θ j m t) ^ 2
        = ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3),
            ((1 : ℝ) / 2 + (-(1 / 2)) * cos (cc * (t - τ j))) :=
      intervalIntegral.integral_congr fun t _ => hid t
    rw [h1, intervalIntegral.integral_add intervalIntegrable_const
      ((hcont.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, hcos]
    simp only [smul_eq_mul]
    ring
  rw [hval]
  have h6 : (6 : ℝ) ≤ (K j m : ℝ) ^ 2 * ℓ j := six_le_K_sq_mul_ℓ hj hm
  have hcℓ : 12 ≤ cc * ℓ j := by
    have hx : cc * ℓ j = 2 * ((K j m : ℝ) ^ 2 * ℓ j) := by rw [hcdef]; ring
    rw [hx]; linarith
  have hu : 2 * (1 / cc) ≤ ℓ j / 6 := by
    rw [mul_one_div, div_le_div_iff₀ hcpos (by norm_num)]
    nlinarith
  have hu0 : (0 : ℝ) ≤ 1 / cc := le_of_lt (one_div_pos.mpr hcpos)
  have hbound : (1 / cc) * sin (cc * (τ j + 2 * ℓ j / 3 - τ j))
      - (1 / cc) * sin (cc * (τ j + ℓ j / 3 - τ j)) ≤ ℓ j / 6 := by
    nlinarith [mul_le_mul_of_nonneg_left (Real.sin_le_one (cc * (τ j + 2 * ℓ j / 3 - τ j))) hu0,
      mul_le_mul_of_nonneg_left (Real.neg_one_le_sin (cc * (τ j + ℓ j / 3 - τ j))) hu0]
  linarith

/-! ## Continuity of `t ↦ normSq (Lβφ D t)` on `J_j` -/

private lemma normSq_Lβφ_eq_on_J {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ J j) :
    normSq (Lβφ D t) = π / 4 * ∑ m ∈ Finset.Icc 1 (M j),
      sin (θ j m t) ^ 2 * (1 + 4 * ((K j m : ℝ))⁻¹ ^ 2) := by
  have htI : t ∈ I j := J_subset_I hj ht
  have hη : ηj D j t = 1 := ηj_eq_one_of_mem_J D hj ht
  have heq : Lβφ D t = fun x => ∑ m ∈ Finset.Icc 1 (M j),
      sin (θ j m t) * (p (K j m) x - 2 * ((K j m : ℝ))⁻¹ * c (K j m) x) := by
    funext x
    rw [Lβφ_of_mem_I D htI x]
    exact Finset.sum_congr rfl fun m _ => by rw [hη]; ring
  rw [heq]
  have hK4 : ∀ m ∈ Finset.Icc 1 (M j), 4 < K j m := fun m hm => by
    have := K_ge hj (Finset.mem_Icc.mp hm).1; omega
  have hsep : ∀ m ∈ Finset.Icc 1 (M j), ∀ m' ∈ Finset.Icc 1 (M j), m < m' → K j m + 4 < K j m' := by
    intro m hm m' _ hmm'
    have h1 : 16 * K j m ≤ K j m' := K_le_of_lt hmm'
    have h2 : 512 ≤ K j m := K_ge hj (Finset.mem_Icc.mp hm).1
    omega
  exact normSq_sum_pc (Finset.Icc 1 (M j)) (K j) (fun m => sin (θ j m t)) hK4 hsep

private lemma continuousOn_normSq_Lβφ_J {j : ℕ} (hj : 1 ≤ j) :
    ContinuousOn (fun t => normSq (Lβφ D t)) (J j) := by
  have hc : Continuous fun t : ℝ => π / 4 *
      ∑ m ∈ Finset.Icc 1 (M j), sin (θ j m t) ^ 2 * (1 + 4 * ((K j m : ℝ))⁻¹ ^ 2) :=
    continuous_const.mul (continuous_finsetSum _ fun m _ =>
      ((Real.continuous_sin.comp' (continuous_θ j m)).pow 2).fun_mul continuous_const)
  exact hc.continuousOn.congr fun t ht => normSq_Lβφ_eq_on_J D hj ht

/-! ## Averaging: a point of `J_j` where `‖L_β φ‖²` is large -/

theorem exists_mem_J_normSq_Lβφ_ge {j : ℕ} (hj : 1 ≤ j) :
    ∃ t ∈ J j, π / 16 * (M j : ℝ) ≤ normSq (Lβφ D t) := by
  have hℓ : 0 < ℓ j := ℓ_pos hj
  have hab : τ j + ℓ j / 3 ≤ τ j + 2 * ℓ j / 3 := by linarith
  have hne : (J j).Nonempty := Set.nonempty_Icc.mpr hab
  have hcompact : IsCompact (J j) := isCompact_Icc
  have hcont : ContinuousOn (fun t => normSq (Lβφ D t)) (J j) := continuousOn_normSq_Lβφ_J D hj
  obtain ⟨t0, ht0mem, ht0max⟩ := hcompact.exists_isMaxOn hne hcont
  refine ⟨t0, ht0mem, ?_⟩
  have hcont' : ContinuousOn (fun t => normSq (Lβφ D t))
      (Set.uIcc (τ j + ℓ j / 3) (τ j + 2 * ℓ j / 3)) := by
    rw [Set.uIcc_of_le hab]; exact hcont
  have hintegrable : IntervalIntegrable (fun t => normSq (Lβφ D t)) MeasureTheory.volume
      (τ j + ℓ j / 3) (τ j + 2 * ℓ j / 3) := hcont'.intervalIntegrable
  have hmaxb : ∀ t ∈ J j, normSq (Lβφ D t) ≤ normSq (Lβφ D t0) :=
    fun t ht => isMaxOn_iff.mp ht0max t ht
  have hintle : (∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), normSq (Lβφ D t))
      ≤ ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), normSq (Lβφ D t0) :=
    intervalIntegral.integral_mono_on hab hintegrable intervalIntegrable_const
      (fun t ht => hmaxb t ht)
  have hconst : (∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), normSq (Lβφ D t0))
      = (ℓ j / 3) * normSq (Lβφ D t0) := by
    rw [intervalIntegral.integral_const]
    have h1 : (τ j + 2 * ℓ j / 3) - (τ j + ℓ j / 3) = ℓ j / 3 := by ring
    rw [h1, smul_eq_mul]
  have hlow : ∀ t ∈ Set.Icc (τ j + ℓ j / 3) (τ j + 2 * ℓ j / 3),
      π / 4 * ∑ m ∈ Finset.Icc 1 (M j), sin (θ j m t) ^ 2 ≤ normSq (Lβφ D t) :=
    fun t ht => normSq_Lβφ_on_J D hj ht
  have hcontLHS : Continuous fun t : ℝ => π / 4 * ∑ m ∈ Finset.Icc 1 (M j), sin (θ j m t) ^ 2 :=
    continuous_const.mul (continuous_finsetSum _ fun m _ =>
      (Real.continuous_sin.comp' (continuous_θ j m)).pow 2)
  have hintlow : (∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3),
        π / 4 * ∑ m ∈ Finset.Icc 1 (M j), sin (θ j m t) ^ 2)
      ≤ ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), normSq (Lβφ D t) :=
    intervalIntegral.integral_mono_on hab (hcontLHS.intervalIntegrable _ _) hintegrable hlow
  have hintcompute : (∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3),
        π / 4 * ∑ m ∈ Finset.Icc 1 (M j), sin (θ j m t) ^ 2)
      = π / 4 * ∑ m ∈ Finset.Icc 1 (M j),
          ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), sin (θ j m t) ^ 2 := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral.integral_finsetSum fun m _ =>
      ((Real.continuous_sin.comp' (continuous_θ j m)).pow 2).intervalIntegrable _ _
  have hlow2 : (M j : ℝ) * (ℓ j / 12) ≤ ∑ m ∈ Finset.Icc 1 (M j),
      ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), sin (θ j m t) ^ 2 := by
    have hconst2 : ∑ _m ∈ Finset.Icc 1 (M j), ℓ j / 12 = (M j : ℝ) * (ℓ j / 12) := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; norm_num
    rw [← hconst2]
    exact Finset.sum_le_sum fun m hm => integral_sin_sq_J hj (Finset.mem_Icc.mp hm).1
  have hstep1 : π / 4 * ((M j : ℝ) * (ℓ j / 12)) ≤ π / 4 * ∑ m ∈ Finset.Icc 1 (M j),
      ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), sin (θ j m t) ^ 2 :=
    mul_le_mul_of_nonneg_left hlow2 (by positivity)
  have hfinal : π / 4 * ((M j : ℝ) * (ℓ j / 12)) ≤ (ℓ j / 3) * normSq (Lβφ D t0) := by
    rw [hintcompute] at hintlow
    exact hstep1.trans (hintlow.trans (hintle.trans_eq hconst))
  have h3 : (0 : ℝ) < ℓ j / 3 := by linarith
  have heq1 : π / 4 * ((M j : ℝ) * (ℓ j / 12)) = π / 16 * (M j : ℝ) * (ℓ j / 3) := by ring
  have heq2 : (ℓ j / 3) * normSq (Lβφ D t0) = normSq (Lβφ D t0) * (ℓ j / 3) := by ring
  rw [heq1, heq2] at hfinal
  exact le_of_mul_le_mul_right hfinal h3

/-! ## Proposition 3.4: the blow-up -/

theorem exists_normSq_Aφ_ge {ε : ℝ} (hε : ε ≠ 0) (C : ℝ) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, C ≤ normSq (Aφ D ε t) := by
  have hεsq : 0 < ε ^ 2 := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (16 * C / (π * ε ^ 2))
  set j := n + 1 with hjdef
  have hj1 : 1 ≤ j := by omega
  have hCbound : C < π * ε ^ 2 / 16 * (j : ℝ) := by
    have hπε2 : 0 < π * ε ^ 2 := by positivity
    have hnj : (n : ℝ) < (j : ℝ) := by
      rw [hjdef]; push_cast; linarith
    have hlt : 16 * C / (π * ε ^ 2) < (j : ℝ) := lt_trans hn hnj
    rw [div_lt_iff₀ hπε2] at hlt
    nlinarith [hlt]
  obtain ⟨t, htJ, htbound⟩ := exists_mem_J_normSq_Lβφ_ge D hj1
  have htI : t ∈ I j := J_subset_I hj1 htJ
  have htIcc : t ∈ Set.Icc (1 / 4 : ℝ) (5 / 16) := I_subset hj1 htI
  have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [htIcc.1], by linarith [htIcc.2]⟩
  refine ⟨t, ht01, ?_⟩
  have hMj : (M j : ℝ) = (j : ℝ) := rfl
  rw [hMj] at htbound
  have hC2 : C ≤ ε ^ 2 * (π / 16 * (j : ℝ)) := by nlinarith [hCbound]
  calc C ≤ ε ^ 2 * (π / 16 * (j : ℝ)) := hC2
    _ ≤ ε ^ 2 * normSq (Lβφ D t) := by
        apply mul_le_mul_of_nonneg_left htbound (sq_nonneg ε)
    _ ≤ ε ^ 2 * normSq (Lβφ D t) + normSq φ'' := by linarith [normSq_nonneg φ'']
    _ = normSq (Aφ D ε t) := (normSq_Aφ D ε t).symm

end LionsC12

end
