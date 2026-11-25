module

public import LionsC12.Endpoint.Coefficient
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# (i) Unbounded variation: failure of Dier's hypothesis

Corollary 7.1(i) of the paper: the coefficient path `t ↦ 𝔞(t) ∈ X = L^∞(0,π)` has infinite
total variation on `[0,1]` (`eVariationOn_aX_eq_top`), and the form family admits no
nondecreasing `g` with
`|𝔞(t)[v,w] − 𝔞(s)[v,w]| ≤ (g(t) − g(s)) ‖v‖_V ‖w‖_V` (`not_exists_dier_bound`), which is the
bounded-variation hypothesis of Dier [Theorem 4.1].

The paper derives both from the main theorem and Dier's sufficiency theorem.  Here they are
proved directly.  On the middle third `J_j` of block `j`, take the quarter-period points
`u_n = τ_j + n π/(2K²)` of the first mode `K = K_{j,1}`: the first mode changes by
`K⁻¹ |sin((n+1)π/2) − sin(nπ/2)| = K⁻¹` between consecutive points, while the other modes of
the block change by at most `(2/15)K⁻¹` (lacunarity), at `x = 0`.  Since `J_j` contains
`3K` consecutive steps, the variation on `J_j` is `≥ 3K · (13/15) ε K⁻¹ ≥ ε`, and there are
infinitely many blocks.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped ENNReal NNReal

variable (D : Cutoffs)

/-- Consecutive quarter periods: `|sin((n+1)π/2) − sin(nπ/2)| = 1`. -/
theorem abs_sin_quarter_succ_sub (n : ℕ) :
    |sin (((n + 1 : ℕ) : ℝ) * (π / 2)) - sin ((n : ℝ) * (π / 2))| = 1 := by
  set x : ℝ := (n : ℝ) * (π / 2) with hx
  have e1 : sin (((n + 1 : ℕ) : ℝ) * (π / 2)) = cos x := by
    rw [hx, ← sin_add_pi_div_two]; push_cast; ring_nf
  have e2 : sin (2 * x) = 0 := by
    rw [show 2 * x = (n : ℝ) * π by rw [hx]; ring, sin_nat_mul_pi]
  have hsq : (cos x - sin x) ^ 2 = 1 := by
    have := sin_sq_add_cos_sq x
    rw [sin_two_mul] at e2
    nlinarith
  rw [e1]
  have h0 := abs_nonneg (cos x - sin x)
  have h1 : |cos x - sin x| ^ 2 = 1 := by rw [sq_abs]; exact hsq
  nlinarith

/-- Monotone comparison of variations: if the increments of `f` are dominated by those of `g`
on `s`, then `Var(f; s) ≤ Var(g; s)`. -/
theorem eVariationOn_le_of_edist_le {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    {f : ℝ → E} {g : ℝ → F} {s : Set ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → edist (f y) (f x) ≤ edist (g y) (g x)) :
    eVariationOn f s ≤ eVariationOn g s :=
  iSup_mono fun p => Finset.sum_le_sum fun i _ =>
    h _ (p.2.2.2 i) _ (p.2.2.2 (i + 1)) (p.2.2.1 (Nat.le_succ i))

/-- **One block of variation**: `Var(𝔞; J_j) ≥ ε` in `L^∞(0,π)`. -/
theorem ofReal_le_eVariationOn_J {ε : ℝ} (hε : 0 ≤ ε) {j : ℕ} (hj : 1 ≤ j) :
    ENNReal.ofReal ε ≤ eVariationOn (aX D ε) (J j) := by
  have hπ := pi_pos
  have hπ3 := pi_lt_d2
  have hK512 : (512 : ℝ) ≤ (K j 1 : ℝ) := by exact_mod_cast K_ge hj le_rfl
  set κ : ℝ := (K j 1 : ℝ) with hκ
  have hκ0 : 0 < κ := by linarith
  have hκℓ : κ * ℓ j = 16 := by simpa using K_mul_ℓ (j := j) (m := 1) hj
  have hℓ0 : 0 < ℓ j := ℓ_pos hj
  -- the quarter-period points
  set n₀ : ℕ := ⌈2 * κ ^ 2 * ℓ j / (3 * π)⌉₊ with hn₀
  set N : ℕ := 3 * K j 1 with hN
  set u : ℕ → ℝ := fun i => τ j + ((n₀ + min i N : ℕ) : ℝ) * (π / 2) / κ ^ 2 with hu
  have hn₀1 : 2 * κ ^ 2 * ℓ j / (3 * π) ≤ n₀ := Nat.le_ceil _
  have hn₀2 : (n₀ : ℝ) < 2 * κ ^ 2 * ℓ j / (3 * π) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hu_mono : Monotone u := by
    intro i i' hii'
    simp only [hu]
    gcongr
  have hlow : ∀ i, τ j + ℓ j / 3 ≤ u i := by
    intro i
    simp only [hu]
    have : ℓ j / 3 ≤ (n₀ : ℝ) * (π / 2) / κ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hn₀1
      nlinarith
    have h' : (n₀ : ℝ) ≤ ((n₀ + min i N : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ _
    have : (n₀ : ℝ) * (π / 2) / κ ^ 2 ≤ ((n₀ + min i N : ℕ) : ℝ) * (π / 2) / κ ^ 2 := by
      gcongr
    linarith
  have hupp : ∀ i, u i ≤ τ j + 2 * ℓ j / 3 := by
    intro i
    simp only [hu]
    have hmin : ((min i N : ℕ) : ℝ) ≤ 3 * κ := by
      have : min i N ≤ N := min_le_right _ _
      have h' : ((min i N : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast this
      have hNκ : (N : ℝ) = 3 * κ := by rw [hN, hκ]; push_cast; ring
      exact h'.trans hNκ.le
    have key : ((n₀ + min i N : ℕ) : ℝ) * (π / 2) ≤ 2 * ℓ j / 3 * κ ^ 2 := by
      rw [Nat.cast_add]
      have e1 : (n₀ : ℝ) * (π / 2) < κ ^ 2 * ℓ j / 3 + π / 2 := by
        have h' : (n₀ : ℝ) * (π / 2) < (2 * κ ^ 2 * ℓ j / (3 * π) + 1) * (π / 2) :=
          mul_lt_mul_of_pos_right hn₀2 (by positivity)
        have e : (2 * κ ^ 2 * ℓ j / (3 * π) + 1) * (π / 2) = κ ^ 2 * ℓ j / 3 + π / 2 := by
          field_simp
        linarith
      -- `π/2 + 3κπ/2 ≤ κ²ℓ/3 = 16κ/3`
      have e2 : κ ^ 2 * ℓ j = 16 * κ := by rw [pow_two, mul_assoc, hκℓ]; ring
      have h3 : ((min i N : ℕ) : ℝ) * (π / 2) ≤ 3 * κ * (π / 2) := by gcongr
      have h4 : 3 * κ * (π / 2) ≤ 3 * κ * (3.15 / 2) := by gcongr
      have h5 : 2 * ℓ j / 3 * κ ^ 2 = 32 * κ / 3 := by
        rw [show 2 * ℓ j / 3 * κ ^ 2 = 2 / 3 * (κ ^ 2 * ℓ j) by ring, e2]; ring
      rw [h5, add_mul]
      rw [e2] at e1
      linarith
    have : ((n₀ + min i N : ℕ) : ℝ) * (π / 2) / κ ^ 2 ≤ 2 * ℓ j / 3 := by
      rw [div_le_iff₀ (by positivity)]; exact key
    linarith
  have huJ : ∀ i, u i ∈ J j := fun i => ⟨hlow i, hupp i⟩
  have hθ : ∀ i, θ j 1 (u i) = ((n₀ + min i N : ℕ) : ℝ) * (π / 2) := by
    intro i
    simp only [θ, hu]
    field_simp
    ring
  -- each step is at least `13 ε / (15 K)`
  have hstep : ∀ i < N,
      ENNReal.ofReal (13 / 15 * ε / κ) ≤ edist (aX D ε (u (i + 1))) (aX D ε (u i)) := by
    intro i hi
    rw [edist_aX]
    refine le_trans ?_ (ofReal_abs_a_sub_le D ε _ _ (x₀ := 0) ⟨le_rfl, hπ.le⟩)
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ (abs_a_sub_zero_ge D hε hj (huJ _) (huJ _)))
    have hmin1 : min (i + 1) N = i + 1 := min_eq_left (by omega)
    have hmin0 : min i N = i := min_eq_left (by omega)
    have h1 := abs_sin_quarter_succ_sub (n₀ + i)
    rw [hθ, hθ, hmin1, hmin0, show n₀ + (i + 1) = n₀ + i + 1 by ring, h1, ← hκ]
    have : 13 / 15 * ε / κ = ε * (κ⁻¹ * 1) - ε * (2 * (κ⁻¹ / 15)) := by field_simp; ring
    rw [this]
  calc ENNReal.ofReal ε ≤ ENNReal.ofReal (∑ _i ∈ Finset.range N, 13 / 15 * ε / κ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hNκ : (N : ℝ) = 3 * κ := by simp [hN, hκ]
        rw [hNκ]
        have : 3 * κ * (13 / 15 * ε / κ) = 13 / 5 * ε := by field_simp; ring
        rw [this]
        linarith
    _ = ∑ _i ∈ Finset.range N, ENNReal.ofReal (13 / 15 * ε / κ) :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity
    _ ≤ ∑ i ∈ Finset.range N, edist (aX D ε (u (i + 1))) (aX D ε (u i)) :=
        Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.1 hi)
    _ ≤ eVariationOn (aX D ε) (J j) := eVariationOn.sum_le hu_mono huJ

/-- The variations on the first `n` middle thirds add up below the variation on `[0, τ_{n+1}]`. -/
theorem sum_eVariationOn_J_le (ε : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, eVariationOn (aX D ε) (J (j + 1)) ≤
      eVariationOn (aX D ε) (Icc 0 (τ (n + 1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hj : 1 ≤ n + 1 := by omega
    have hsep : ∀ x ∈ Icc 0 (τ (n + 1)), ∀ y ∈ J (n + 1), x ≤ y := by
      intro x hx y hy
      linarith [hx.2, hy.1, ℓ_pos hj]
    have hsub : Icc 0 (τ (n + 1)) ∪ J (n + 1) ⊆ Icc 0 (τ (n + 1 + 1)) := by
      have h1 := τ_add_ℓ hj
      have h2 := ℓ_pos hj
      have h3 := τ_ge hj
      rintro y (hy | hy)
      · exact ⟨hy.1, by linarith [hy.2]⟩
      · have := J_subset_I hj hy
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
    calc _ ≤ eVariationOn (aX D ε) (Icc 0 (τ (n + 1))) + eVariationOn (aX D ε) (J (n + 1)) := by
          gcongr
      _ ≤ eVariationOn (aX D ε) (Icc 0 (τ (n + 1)) ∪ J (n + 1)) :=
          eVariationOn.add_le_union _ hsep
      _ ≤ _ := eVariationOn.mono _ hsub

/-- **(i) `𝔞 ∉ BV([0,1]; L^∞(0,π))`:** the coefficient path `t ↦ [𝔞(t)] ∈ L^∞(0,π)` has
infinite total variation on `[0,1]`. -/
theorem eVariationOn_aX_eq_top {ε : ℝ} (hε : 0 < ε) :
    eVariationOn (aX D ε) (Icc 0 1) = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt ((r : ℝ) / ε)
  calc (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ ENNReal.ofReal (∑ _j ∈ Finset.range n, ε) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [div_lt_iff₀ hε] at hn
        linarith
    _ = ∑ _j ∈ Finset.range n, ENNReal.ofReal ε :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => hε.le
    _ ≤ ∑ j ∈ Finset.range n, eVariationOn (aX D ε) (J (j + 1)) :=
        Finset.sum_le_sum fun j _ => ofReal_le_eVariationOn_J D hε.le (by omega)
    _ ≤ eVariationOn (aX D ε) (Icc 0 (τ (n + 1))) := sum_eVariationOn_J_le D ε n
    _ ≤ eVariationOn (aX D ε) (Icc 0 1) :=
        eVariationOn.mono _ (Icc_subset_Icc le_rfl (by linarith [τ_lt (j := n + 1) (by omega)]))

/-- **(i) Failure of Dier's bounded-variation hypothesis:** there is no nondecreasing
`g : [0,1] → ℝ` with `|𝔞(t)[v,w] − 𝔞(s)[v,w]| ≤ (g(t) − g(s)) ‖v‖_V ‖w‖_V` for all
`0 ≤ s ≤ t ≤ 1` and `v, w ∈ V = H¹₀(0,π)`. -/
theorem not_exists_dier_bound {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ g : ℝ → ℝ, MonotoneOn g (Icc 0 1) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → ∀ v w : H10 (Ioo 0 π),
        ‖form (Ioo 0 π) (a D ε) t v w -
            form (Ioo 0 π) (a D ε) s v w‖ ≤ (g t - g s) * ‖v‖ * ‖w‖ := by
  rintro ⟨g, hg, hb⟩
  have hcmp : eVariationOn (aX D ε) (Icc 0 1) ≤ eVariationOn g (Icc 0 1) := by
    refine eVariationOn_le_of_edist_le fun s hs t ht hst => ?_
    rw [← formOpDist_a_eq_edist, edist_dist, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.2 (hg hs ht hst))]
    exact formOpDist_le_ofReal (hb s t hs.1 hst ht.2)
  have hfin : eVariationOn g (Icc 0 1) ≠ ⊤ := by
    have := hg.eVariationOn_eq (a := 0) (b := 1) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
    rw [inter_self] at this
    rw [this]
    exact ENNReal.ofReal_ne_top
  rw [eVariationOn_aX_eq_top D hε] at hcmp
  exact hfin (top_le_iff.1 hcmp)

end LionsC12
