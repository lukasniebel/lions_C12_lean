module

public import LionsC12.Endpoint.Coefficient

/-!
# (ii) No Dini modulus: failure of the Haak–Ouhabaz hypothesis

Corollary 7.1(ii) of the paper: there is no nondecreasing `ω : [0,1] → [0,∞)` with

`|𝔞(t)[v,w] − 𝔞(s)[v,w]| ≤ ω(|t − s|) ‖v‖_V ‖w‖_V`  (`s, t ∈ [0,1]`, `v, w ∈ V`)

and `∫₀¹ ω(r) r^{−3/2} dr < ∞` (the hypothesis of Haak–Ouhabaz [Theorem 1.2]); likewise no
such modulus controls `‖𝔞(t) − 𝔞(s)‖_{L^∞(0,π)}`.

The paper derives this from the main theorem and the cited sufficiency theorem.  Here it is
proved directly: by Proposition 3.3 (`exists_pair_lower_bound`) the increment over the
sharpness step `h_j = π/(2K_{j,1}²)` is at least `(13/15) ε / K_{j,1}`, so
`ω(h_j) ≥ (13/15) ε K_{j,1}⁻¹ ≍ ε h_j^{1/2}`.  Monotonicity of `ω` then gives on
`(h_{j+1}, h_j]` the lower bound `ω(r) r^{−3/2} ≥ ω(h_{j+1}) h_j^{−3/2}`, and these pieces
contribute `≥ c ε / (j + 2)`, a divergent series.

The integral `∫₀¹ ω(r) r^{−3/2} dr` is formalised as the lower Lebesgue integral
`∫⁻ r in Ioo 0 1, ENNReal.ofReal (ω r / r ^ (3/2))`; it is finite whenever the Bochner integral
exists, so `= ⊤` is the stronger statement.  Nonnegativity of `ω` is not needed.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped ENNReal NNReal

variable (D : Cutoffs)

/-- The sharpness step `h_j = π / (2 K_{j,1}²)` of Proposition 3.3. -/
def hStep (j : ℕ) : ℝ := π / (2 * (K j 1 : ℝ) ^ 2)

theorem hStep_pos {j : ℕ} (hj : 1 ≤ j) : 0 < hStep j := by
  have : (0 : ℝ) < (K j 1 : ℝ) := by exact_mod_cast K_pos hj
  unfold hStep; positivity

theorem hStep_lt_one {j : ℕ} (hj : 1 ≤ j) : hStep j < 1 := by
  have hK : (512 : ℝ) ≤ (K j 1 : ℝ) := by exact_mod_cast K_ge hj le_rfl
  unfold hStep
  rw [div_lt_one (by positivity)]
  nlinarith [pi_le_four]

theorem hStep_le_one {j : ℕ} (hj : 1 ≤ j) : hStep j ≤ 1 := (hStep_lt_one hj).le

theorem hStep_anti {j j' : ℕ} (hj : 1 ≤ j) (h : j ≤ j') : hStep j' ≤ hStep j := by
  have h1 : (K j 1 : ℝ) ≤ (K j' 1 : ℝ) := by
    rw [K_one_cast, K_one_cast]
    have : (j : ℝ) ≤ j' := by exact_mod_cast h
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have h0 : (0 : ℝ) < (K j 1 : ℝ) := by exact_mod_cast K_pos hj
  unfold hStep
  gcongr

theorem rpow_three_halves {r : ℝ} (hr : 0 ≤ r) : r ^ ((3 : ℝ) / 2) = r * Real.sqrt r := by
  rcases hr.eq_or_lt with h | h
  · subst h; simp
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, rpow_add h, rpow_one, sqrt_eq_rpow]

/-- The contribution of one dyadic-type piece `(h_{j+1}, h_j]`. -/
theorem piece_ge {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 1 ≤ j) :
    c / (3 * ((j : ℝ) + 2)) ≤
      c / (K (j + 1) 1 : ℝ) / (hStep j * Real.sqrt (hStep j)) * (hStep j - hStep (j + 1)) := by
  have hπ := pi_pos
  set σ : ℝ := Real.sqrt (π / 2) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 (by positivity)
  have hσ2 : σ ^ 2 = π / 2 := Real.sq_sqrt (by positivity)
  have hσle : σ ≤ 2 := by
    rw [hσ, Real.sqrt_le_left (by norm_num)]
    linarith [pi_le_four]
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  set m : ℝ := 256 * ((j : ℝ) + 1) with hm
  have hm0 : 0 < m := by positivity
  have hx : (K j 1 : ℝ) = j * m := by rw [K_one_cast, hm]; ring
  have hy : (K (j + 1) 1 : ℝ) = ((j : ℝ) + 2) * m := by
    rw [K_one_cast, hm]; push_cast; ring
  have hjm : 0 < (j : ℝ) * m := by positivity
  have hhj : hStep j = σ ^ 2 / ((j : ℝ) * m) ^ 2 := by
    rw [hStep, hx, hσ2]; field_simp
  have hhj1 : hStep (j + 1) = σ ^ 2 / (((j : ℝ) + 2) * m) ^ 2 := by
    rw [hStep, hy, hσ2]; field_simp
  have hsq : Real.sqrt (hStep j) = σ / ((j : ℝ) * m) := by
    rw [hhj, show σ ^ 2 / ((j : ℝ) * m) ^ 2 = (σ / ((j : ℝ) * m)) ^ 2 by rw [div_pow]]
    exact Real.sqrt_sq (by positivity)
  rw [hsq, hhj, hhj1, hy]
  have e : c / (((j : ℝ) + 2) * m) / (σ ^ 2 / ((j : ℝ) * m) ^ 2 * (σ / ((j : ℝ) * m))) *
      (σ ^ 2 / ((j : ℝ) * m) ^ 2 - σ ^ 2 / (((j : ℝ) + 2) * m) ^ 2)
      = c * j * (4 * j + 4) / (σ * ((j : ℝ) + 2) ^ 3) := by
    field_simp
    ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have : σ * ((j : ℝ) + 2) ^ 2 ≤ 2 * ((j : ℝ) + 2) ^ 2 := by gcongr
  have h2 : 2 * ((j : ℝ) + 2) ^ 2 ≤ 3 * (j * (4 * j + 4)) := by nlinarith
  have h3 : c * (σ * ((j : ℝ) + 2) ^ 3) ≤ c * (3 * ((j : ℝ) + 2) * (j * (4 * j + 4))) := by
    have : σ * ((j : ℝ) + 2) ^ 3 ≤ 3 * ((j : ℝ) + 2) * (j * (4 * j + 4)) := by
      have e1 : σ * ((j : ℝ) + 2) ^ 3 = (σ * ((j : ℝ) + 2) ^ 2) * ((j : ℝ) + 2) := by ring
      have e2 : 3 * ((j : ℝ) + 2) * (j * (4 * j + 4)) =
          (3 * (j * (4 * j + 4))) * ((j : ℝ) + 2) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    gcongr
  nlinarith

/-- **The Dini integral diverges** for any nondecreasing `ω` on `[0,1]` with
`ω(h_j) ≥ c / K_{j,1}` at the sharpness steps, `c > 0`. -/
theorem lintegral_dini_eq_top_of_sharp {ω : ℝ → ℝ} (hω : MonotoneOn ω (Icc 0 1)) {c : ℝ}
    (hc : 0 < c) (hsharp : ∀ j, 1 ≤ j → c / (K j 1 : ℝ) ≤ ω (hStep j)) :
    ∫⁻ r in Ioo 0 1, ENNReal.ofReal (ω r / r ^ ((3 : ℝ) / 2)) = ⊤ := by
  set F : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (ω r / r ^ ((3 : ℝ) / 2)) with hF
  -- the pieces `(h_{j+1}, h_j]`
  have hpiece : ∀ j : ℕ, 1 ≤ j →
      ENNReal.ofReal (c / (3 * ((j : ℝ) + 2))) ≤ ∫⁻ r in Ioc (hStep (j + 1)) (hStep j), F r := by
    intro j hj
    have hj' : 1 ≤ j + 1 := by omega
    have hK0 : (0 : ℝ) < (K (j + 1) 1 : ℝ) := by exact_mod_cast K_pos hj'
    have hh0 := hStep_pos hj'
    have hhj := hStep_pos hj
    have hlow : ∀ r ∈ Ioc (hStep (j + 1)) (hStep j),
        ENNReal.ofReal (c / (K (j + 1) 1 : ℝ) / (hStep j * Real.sqrt (hStep j))) ≤ F r := by
      intro r hr
      refine ENNReal.ofReal_le_ofReal ?_
      have hr0 : 0 < r := hh0.trans hr.1
      have hωr : c / (K (j + 1) 1 : ℝ) ≤ ω r :=
        (hsharp (j + 1) hj').trans (hω ⟨hh0.le, hStep_le_one hj'⟩
          ⟨hr0.le, hr.2.trans (hStep_le_one hj)⟩ hr.1.le)
      rw [rpow_three_halves hr0.le]
      exact div_le_div₀ (le_trans (by positivity) hωr) hωr (by positivity)
        (mul_le_mul hr.2 (Real.sqrt_le_sqrt hr.2) (Real.sqrt_nonneg _) hhj.le)
    calc ENNReal.ofReal (c / (3 * ((j : ℝ) + 2)))
        ≤ ENNReal.ofReal (c / (K (j + 1) 1 : ℝ) / (hStep j * Real.sqrt (hStep j)) *
            (hStep j - hStep (j + 1))) := ENNReal.ofReal_le_ofReal (piece_ge hc hj)
      _ = ∫⁻ _ in Ioc (hStep (j + 1)) (hStep j),
            ENNReal.ofReal (c / (K (j + 1) 1 : ℝ) / (hStep j * Real.sqrt (hStep j))) := by
          rw [setLIntegral_const, Real.volume_Ioc, ENNReal.ofReal_mul (by positivity)]
      _ ≤ ∫⁻ r in Ioc (hStep (j + 1)) (hStep j), F r := setLIntegral_mono' measurableSet_Ioc hlow
  refine ENNReal.eq_top_of_forall_nnreal_le fun C => ?_
  obtain ⟨n, hn⟩ := exists_sum_inv_succ_gt (6 * C / c)
  -- disjointness and inclusion
  have hdisj : (↑(Finset.Icc 1 n) : Set ℕ).PairwiseDisjoint
      (fun j => Ioc (hStep (j + 1)) (hStep j)) := by
    intro i hi i' hi' hii'
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    have hi1' : 1 ≤ i' := (Finset.mem_Icc.1 hi').1
    rw [Function.onFun, Set.disjoint_left]
    intro r hr hr'
    rcases lt_or_gt_of_ne hii' with h | h
    · have := hStep_anti (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ i')
      linarith [hr.1, hr'.2]
    · have := hStep_anti (by omega : 1 ≤ i' + 1) (by omega : i' + 1 ≤ i)
      linarith [hr.2, hr'.1]
  have hsub : ⋃ j ∈ Finset.Icc 1 n, Ioc (hStep (j + 1)) (hStep j) ⊆ Ioo 0 1 := by
    refine iUnion₂_subset fun j hj => ?_
    have hj1 := (Finset.mem_Icc.1 hj).1
    intro r hr
    exact ⟨(hStep_pos (by omega)).trans hr.1, hr.2.trans_lt (hStep_lt_one hj1)⟩
  calc (C : ℝ≥0∞) = ENNReal.ofReal C := (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ ENNReal.ofReal (∑ j ∈ Finset.Icc 1 n, c / (3 * ((j : ℝ) + 2))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : ∀ j ∈ Finset.Icc 1 n,
            c / 6 * (1 / ((j : ℝ) + 1)) ≤ c / (3 * ((j : ℝ) + 2)) := by
          intro j _
          have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have h2 := Finset.sum_le_sum h1
        rw [← Finset.mul_sum] at h2
        rw [div_lt_iff₀ hc] at hn
        have h3 : c / 6 * ∑ j ∈ Finset.Icc 1 n, (1 : ℝ) / ((j : ℝ) + 1)
            = (∑ j ∈ Finset.Icc 1 n, (1 : ℝ) / ((j : ℝ) + 1)) * c / 6 := by ring
        linarith
    _ = ∑ j ∈ Finset.Icc 1 n, ENNReal.ofReal (c / (3 * ((j : ℝ) + 2))) :=
        ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity
    _ ≤ ∑ j ∈ Finset.Icc 1 n, ∫⁻ r in Ioc (hStep (j + 1)) (hStep j), F r :=
        Finset.sum_le_sum fun j hj => hpiece j (Finset.mem_Icc.1 hj).1
    _ = ∫⁻ r in ⋃ j ∈ Finset.Icc 1 n, Ioc (hStep (j + 1)) (hStep j), F r :=
        (lintegral_biUnion_finset hdisj (fun _ _ => measurableSet_Ioc) _).symm
    _ ≤ ∫⁻ r in Ioo 0 1, F r := lintegral_mono_set hsub

/-- The sharpness lower bound `ω(h_j) ≥ (13/15) ε / K_{j,1}` for any `ω` dominating the
`L^∞(0,π)` increments of the coefficient on `[0,1]` (Proposition 3.3). -/
theorem sharp_of_eLpNorm_le {ε : ℝ} (hε : 0 < ε) {ω : ℝ → ℝ}
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π)) ≤
        ENNReal.ofReal (ω |t - s|)) :
    ∀ j : ℕ, 1 ≤ j → 13 * ε / 15 / (K j 1 : ℝ) ≤ ω (hStep j) := by
  intro j hj
  obtain ⟨t, h, hh, ht, hth, hheq, hlb⟩ := exists_pair_lower_bound D hj
  have hK0 : (0 : ℝ) < (K j 1 : ℝ) := by exact_mod_cast K_pos hj
  have hpos : 0 < 13 * ε / 15 / (K j 1 : ℝ) := by positivity
  have hdiff : |a D ε (t + h) 0 - a D ε t 0| = ε * |β D (t + h) 0 - β D t 0| := by
    have e : a D ε (t + h) 0 - a D ε t 0 = ε * (β D (t + h) 0 - β D t 0) := by unfold a; ring
    rw [e, abs_mul, abs_of_pos hε]
  have h1 : 13 * ε / 15 / (K j 1 : ℝ) ≤ |a D ε (t + h) 0 - a D ε t 0| := by
    rw [hdiff]
    have : 13 * ε / 15 / (K j 1 : ℝ) = ε * (13 / (15 * (K j 1 : ℝ))) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hlb hε.le
  have h2 := (ofReal_abs_a_sub_le D ε (t + h) t (x₀ := 0) ⟨le_rfl, pi_pos.le⟩).trans
    (hb t (J_subset_Icc hj ht) (t + h) (J_subset_Icc hj hth))
  rw [show t + h - t = h by ring, abs_of_pos hh] at h2
  have h3 := (ENNReal.ofReal_le_ofReal h1).trans h2
  rw [hheq, ← hStep] at h3
  rcases ENNReal.ofReal_le_ofReal_iff'.1 h3 with h4 | h4
  · exact h4
  · exact absurd h4 (not_le.2 hpos)

/-- **(ii), coefficient form, with the integral `= ⊤`:** if a nondecreasing `ω` on `[0,1]`
dominates `‖𝔞(t) − 𝔞(s)‖_{L^∞(0,π)} ≤ ω(|t − s|)` on `[0,1]`, then
`∫₀¹ ω(r) r^{−3/2} dr = ∞`. -/
theorem dini_coeff_lintegral_eq_top {ε : ℝ} (hε : 0 < ε) {ω : ℝ → ℝ}
    (hω : MonotoneOn ω (Icc 0 1))
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖aX D ε t - aX D ε s‖ ≤ ω |t - s|) :
    ∫⁻ r in Ioo 0 1, ENNReal.ofReal (ω r / r ^ ((3 : ℝ) / 2)) = ⊤ := by
  refine lintegral_dini_eq_top_of_sharp hω (by positivity : (0 : ℝ) < 13 * ε / 15)
    (sharp_of_eLpNorm_le D hε fun s hs t ht => ?_)
  rw [← ENNReal.ofReal_toReal (eLpNorm_a_sub_ne_top D ε t s), ← norm_aX_sub]
  exact ENNReal.ofReal_le_ofReal (hb s hs t ht)

/-- **(ii), form version, with the integral `= ⊤`:** if a nondecreasing `ω` on `[0,1]` satisfies
`|𝔞(t)[v,w] − 𝔞(s)[v,w]| ≤ ω(|t − s|) ‖v‖_V ‖w‖_V` for `s, t ∈ [0,1]`, `v, w ∈ V`, then
`∫₀¹ ω(r) r^{−3/2} dr = ∞`. -/
theorem dini_form_lintegral_eq_top {ε : ℝ} (hε : 0 < ε) {ω : ℝ → ℝ}
    (hω : MonotoneOn ω (Icc 0 1))
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ v w : H10 (Ioo 0 π),
      ‖form (Ioo 0 π) (a D ε) t v w -
          form (Ioo 0 π) (a D ε) s v w‖ ≤ ω |t - s| * ‖v‖ * ‖w‖) :
    ∫⁻ r in Ioo 0 1, ENNReal.ofReal (ω r / r ^ ((3 : ℝ) / 2)) = ⊤ := by
  refine lintegral_dini_eq_top_of_sharp hω (by positivity : (0 : ℝ) < 13 * ε / 15)
    (sharp_of_eLpNorm_le D hε fun s hs t ht => ?_)
  rw [← formOpDist_a]
  exact formOpDist_le_ofReal (hb s hs t ht)

/-- **(ii) Failure of the Haak–Ouhabaz Dini hypothesis:** there is no nondecreasing
`ω : [0,1] → [0,∞)` with `|𝔞(t)[v,w] − 𝔞(s)[v,w]| ≤ ω(|t − s|) ‖v‖_V ‖w‖_V` for all
`s, t ∈ [0,1]`, `v, w ∈ V = H¹₀(0,π)`, and `∫₀¹ ω(r) r^{−3/2} dr < ∞`. -/
theorem not_exists_dini_form {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ ω : ℝ → ℝ, MonotoneOn ω (Icc 0 1) ∧ (∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ ω r) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ v w : H10 (Ioo 0 π),
        ‖form (Ioo 0 π) (a D ε) t v w -
            form (Ioo 0 π) (a D ε) s v w‖ ≤ ω |t - s| * ‖v‖ * ‖w‖) ∧
      ∫⁻ r in Ioo 0 1, ENNReal.ofReal (ω r / r ^ ((3 : ℝ) / 2)) < ⊤ := by
  rintro ⟨ω, hω, -, hb, hfin⟩
  rw [dini_form_lintegral_eq_top D hε hω hb] at hfin
  exact lt_irrefl _ hfin

/-- **(ii), coefficient form:** no Dini modulus controls `‖𝔞(t) − 𝔞(s)‖_{L^∞(0,π)}`. -/
theorem not_exists_dini_coeff {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ ω : ℝ → ℝ, MonotoneOn ω (Icc 0 1) ∧ (∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ ω r) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖aX D ε t - aX D ε s‖ ≤ ω |t - s|) ∧
      ∫⁻ r in Ioo 0 1, ENNReal.ofReal (ω r / r ^ ((3 : ℝ) / 2)) < ⊤ := by
  rintro ⟨ω, hω, -, hb, hfin⟩
  rw [dini_coeff_lintegral_eq_top D hε hω hb] at hfin
  exact lt_irrefl _ hfin

end LionsC12
