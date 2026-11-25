module

public import LionsC12.Endpoint.OpNorm
public import LionsC12.Interval.Theorem

/-!
# The coefficient path `t ↦ 𝔞(t) ∈ L^∞(0,π)` and its increments

Facts about the coefficient `𝔞 = a D ε` of `LionsC12.Construction.Defs` used for the failure
of the endpoint hypotheses (Section 7 of the paper):

* `aX` — the path `t ↦ [𝔞(t)] ∈ X = L^∞(0,π)` (the class in `Lp ℝ ∞`), with
  `edist (aX t) (aX s) = ‖𝔞(t) − 𝔞(s)‖_{L^∞(0,π)}` (`edist_aX`);
* `formOpDist_a` — `‖𝒜(t) − 𝒜(s)‖_{L(V,V')} = ‖𝔞(t) − 𝔞(s)‖_{L^∞(0,π)}` for the forms of
  `LionsC12.Paper.Statement` on `V = H¹₀(0,π)` (from `LionsC12.formOpDist_eq_eLpNorm`);
* `integral_a_sub_sq` — on the middle third `J_j` of a block, spatial orthogonality of the
  modes `cos(K_{j,m} x)` gives
  `∫₀^π |𝔞(t,x) − 𝔞(s,x)|² dx = (π/2) ε² ∑_m K_{j,m}⁻² (sin θ_{j,m}(t) − sin θ_{j,m}(s))²`,
  and `modeSq_le_eLpNorm_sq` the resulting lower bound of `‖𝔞(t) − 𝔞(s)‖²_{L^∞}`;
* `abs_a_sub_zero_ge` — the first mode dominates at `x = 0`:
  `|𝔞(t,0) − 𝔞(s,0)| ≥ ε K⁻¹ |sin θ_{j,1}(t) − sin θ_{j,1}(s)| − (2/15) ε K⁻¹`, `K = K_{j,1}`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped ENNReal NNReal

variable (D : Cutoffs)

/-! ### Boundedness and continuity -/

theorem abs_a_le_one_add (ε t x : ℝ) : |a D ε t x| ≤ 1 + |ε| := by
  have h := abs_β_le D t x
  unfold a
  calc |1 + ε * β D t x| ≤ |(1 : ℝ)| + |ε * β D t x| := abs_add_le _ _
    _ = 1 + |ε| * |β D t x| := by rw [abs_one, abs_mul]
    _ ≤ 1 + |ε| * 1 := by gcongr; linarith
    _ = 1 + |ε| := by ring

/-- `𝔞(t)` is a bounded measurable coefficient, for every `ε`. -/
theorem isBoundedCoeff_a_abs (ε t : ℝ) : IsBoundedCoeff (a D ε) t (1 + |ε|) :=
  ⟨(continuous_a_x D ε t).measurable, abs_a_le_one_add D ε t⟩

theorem continuous_a_sub (ε t s : ℝ) : Continuous fun x => a D ε t x - a D ε s x :=
  (continuous_a_x D ε t).sub (continuous_a_x D ε s)

/-! ### The path in `X = L^∞(0,π)` -/

theorem memLp_a (ε t : ℝ) : MemLp (a D ε t) ∞ (volume.restrict (Ioo 0 π)) :=
  memLp_top_of_bound (continuous_a_x D ε t).aestronglyMeasurable (1 + |ε|)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_a_le_one_add D ε t x)

/-- The coefficient path `t ↦ 𝔞(t)` in `X = L^∞(0,π)`: the class of `x ↦ 𝔞(t,x)` in
`Lp ℝ ∞ (volume.restrict (Ioo 0 π))`. -/
def aX (ε t : ℝ) : Lp ℝ ∞ (volume.restrict (Ioo 0 π)) := (memLp_a D ε t).toLp (a D ε t)

theorem edist_aX (ε t s : ℝ) :
    edist (aX D ε t) (aX D ε s) =
      eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π)) := by
  rw [aX, aX, Lp.edist_toLp_toLp]
  rfl

theorem eLpNorm_a_sub_ne_top (ε t s : ℝ) :
    eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π)) ≠ ⊤ :=
  eLpNorm_coeff_sub_ne_top (isBoundedCoeff_a_abs D ε t) (isBoundedCoeff_a_abs D ε s)

theorem norm_aX_sub (ε t s : ℝ) :
    ‖aX D ε t - aX D ε s‖ =
      (eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π))).toReal := by
  rw [← dist_eq_norm, dist_edist, edist_aX]

/-- **`‖𝒜(t) − 𝒜(s)‖_{L(V,V')} = ‖𝔞(t) − 𝔞(s)‖_{L^∞(0,π)}`** for the coefficient of the
construction, `V = H¹₀(0,π)` with its graph norm. -/
theorem formOpDist_a (ε t s : ℝ) :
    formOpDist (Ioo 0 π) (a D ε) t s =
      eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π)) :=
  formOpDist_eq_eLpNorm pi_pos (isBoundedCoeff_a_abs D ε t) (isBoundedCoeff_a_abs D ε s)
    (continuous_a_sub D ε t s)

theorem formOpDist_a_eq_edist (ε t s : ℝ) :
    formOpDist (Ioo 0 π) (a D ε) t s = edist (aX D ε t) (aX D ε s) := by
  rw [formOpDist_a, edist_aX]

/-- The pointwise lower bound `|𝔞(t,x₀) − 𝔞(s,x₀)| ≤ ‖𝔞(t) − 𝔞(s)‖_{L^∞(0,π)}`,
`x₀ ∈ [0,π]`. -/
theorem ofReal_abs_a_sub_le (ε t s : ℝ) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc 0 π) :
    ENNReal.ofReal |a D ε t x₀ - a D ε s x₀| ≤
      eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π)) :=
  ofReal_abs_le_eLpNorm_top (continuous_a_sub D ε t s) hx₀

/-! ### Spatial orthogonality on the middle thirds -/

/-- Pythagoras for cosines on `(0,π)`: for distinct nonzero integer frequencies,
`∫₀^π (∑ c_m cos(K_m x))² = (π/2) ∑ c_m²`. -/
theorem integral_sum_cos_sq (s : Finset ℕ) (Kf : ℕ → ℕ) (c : ℕ → ℝ) (hK : ∀ m ∈ s, Kf m ≠ 0)
    (hinj : ∀ m ∈ s, ∀ m' ∈ s, Kf m = Kf m' → m = m') :
    ∫ x in (0 : ℝ)..π, (∑ m ∈ s, c m * cos (Kf m * x)) ^ 2 = π / 2 * ∑ m ∈ s, c m ^ 2 := by
  have hcont : ∀ (m m' : ℕ) (r : ℝ),
      IntervalIntegrable (fun x : ℝ => r * (cos (Kf m * x) * cos (Kf m' * x))) volume 0 π :=
    fun m m' r => (continuous_const.mul ((continuous_cos_mul _).mul
      (continuous_cos_mul _))).intervalIntegrable _ _
  have key : ∀ x : ℝ, (∑ m ∈ s, c m * cos (Kf m * x)) ^ 2
      = ∑ m ∈ s, ∑ m' ∈ s, (c m * c m') * (cos (Kf m * x) * cos (Kf m' * x)) := by
    intro x
    rw [pow_two, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by ring
  simp_rw [key]
  have hsum_int : ∀ m ∈ s, IntervalIntegrable
      (fun x : ℝ => ∑ m' ∈ s, (c m * c m') * (cos (Kf m * x) * cos (Kf m' * x))) volume 0 π :=
    fun m _ => (continuous_finsetSum s fun m' _ => continuous_const.mul
      ((continuous_cos_mul _).mul (continuous_cos_mul _))).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hsum_int, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hint : ∀ m' ∈ s, IntervalIntegrable
      (fun x : ℝ => (c m * c m') * (cos (Kf m * x) * cos (Kf m' * x))) volume 0 π :=
    fun m' _ => hcont m m' _
  rw [intervalIntegral.integral_finsetSum hint, Finset.sum_eq_single m]
  · rw [intervalIntegral.integral_const_mul, integral_cos_mul_cos, ite_eq_left rfl,
      ite_eq_right (hK m hm)]
    ring
  · intro m' hm' hne
    rw [intervalIntegral.integral_const_mul, integral_cos_mul_cos,
      ite_eq_right fun h => hne (hinj m hm m' hm' h).symm, mul_zero]
  · intro h; exact absurd hm h

theorem K_injOn {j : ℕ} (hj : 1 ≤ j) {m m' : ℕ} (h : K j m = K j m') : m = m' := by
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · have := K_le_of_lt (j := j) hlt
    have := K_pos (j := j) (m := m) hj
    omega
  · exact heq
  · have := K_le_of_lt (j := j) hgt
    have := K_pos (j := j) (m := m') hj
    omega

/-- The weighted sum of the squared phase increments of block `j`:
`∑_{m=1}^{M_j} K_{j,m}⁻² (sin θ_{j,m}(t) − sin θ_{j,m}(s))²`. -/
def modeSq (j : ℕ) (t s : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (M j), (((K j m : ℝ))⁻¹ * (sin (θ j m t) - sin (θ j m s))) ^ 2

/-- On the middle third `J_j`, the coefficient is `1 + ε ∑_m K⁻¹ sin θ_m(t) cos(K_m x)`. -/
theorem a_eq_of_mem_J {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ J j) (ε x : ℝ) :
    a D ε t x = 1 + ε * ∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹ * sin (θ j m t) *
      cos (K j m * x) := by
  rw [a, β_eq_block D (J_subset_I hj ht) x]
  simp only [βblock, βmode, ηj_eq_one_of_mem_J D hj ht, one_mul]

theorem a_sub_eq_of_mem_J {j : ℕ} (hj : 1 ≤ j) {t s : ℝ} (ht : t ∈ J j) (hs : s ∈ J j)
    (ε x : ℝ) :
    a D ε t x - a D ε s x = ∑ m ∈ Finset.Icc 1 (M j),
      (ε * (((K j m : ℝ))⁻¹ * (sin (θ j m t) - sin (θ j m s)))) * cos (K j m * x) := by
  rw [a_eq_of_mem_J D hj ht, a_eq_of_mem_J D hj hs, add_sub_add_left_eq_sub, ← mul_sub,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- **Orthogonality on `J_j`:**
`∫₀^π |𝔞(t,x) − 𝔞(s,x)|² dx = (π/2) ε² ∑_m K_{j,m}⁻² (sin θ_{j,m}(t) − sin θ_{j,m}(s))²`. -/
theorem integral_a_sub_sq {j : ℕ} (hj : 1 ≤ j) {t s : ℝ} (ht : t ∈ J j) (hs : s ∈ J j)
    (ε : ℝ) :
    ∫ x in (0 : ℝ)..π, (a D ε t x - a D ε s x) ^ 2 = π / 2 * ε ^ 2 * modeSq j t s := by
  simp_rw [a_sub_eq_of_mem_J D hj ht hs ε]
  rw [integral_sum_cos_sq _ (K j) _ (fun m _ => (K_pos hj).ne')
    (fun m _ m' _ h => K_injOn hj h), modeSq, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- `∫₀^π g² ≤ π ‖g‖²_{L^∞(0,π)}` for a continuous `g`. -/
theorem integral_sq_le_pi_mul_eLpNorm_sq {g : ℝ → ℝ} (hg : Continuous g)
    (hfin : eLpNorm g ∞ (volume.restrict (Ioo 0 π)) ≠ ⊤) :
    ∫ x in (0 : ℝ)..π, g x ^ 2 ≤ π * (eLpNorm g ∞ (volume.restrict (Ioo 0 π))).toReal ^ 2 := by
  have hb : ∀ x ∈ Icc 0 π, g x ^ 2 ≤ (eLpNorm g ∞ (volume.restrict (Ioo 0 π))).toReal ^ 2 := by
    intro x hx
    have h1 := ENNReal.toReal_mono hfin (ofReal_abs_le_eLpNorm_top hg hx)
    rw [ENNReal.toReal_ofReal (abs_nonneg _)] at h1
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc ∫ x in (0 : ℝ)..π, g x ^ 2
      ≤ ∫ _ in (0 : ℝ)..π, (eLpNorm g ∞ (volume.restrict (Ioo 0 π))).toReal ^ 2 :=
        intervalIntegral.integral_mono_on pi_pos.le ((hg.pow 2).intervalIntegrable _ _)
          intervalIntegrable_const hb
    _ = π * (eLpNorm g ∞ (volume.restrict (Ioo 0 π))).toReal ^ 2 := by simp

/-- **`‖𝔞(t) − 𝔞(s)‖²_{L^∞(0,π)} ≥ (1/π) ∫₀^π |𝔞(t) − 𝔞(s)|² = (ε²/2) ∑_m K⁻² (sin θ_m(t) −
sin θ_m(s))²`** for `t, s ∈ J_j`. -/
theorem modeSq_le_eLpNorm_sq {j : ℕ} (hj : 1 ≤ j) {t s : ℝ} (ht : t ∈ J j) (hs : s ∈ J j)
    (ε : ℝ) :
    ε ^ 2 / 2 * modeSq j t s ≤
      (eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π))).toReal ^ 2 := by
  have h := integral_sq_le_pi_mul_eLpNorm_sq (continuous_a_sub D ε t s)
    (eLpNorm_a_sub_ne_top D ε t s)
  rw [integral_a_sub_sq D hj ht hs ε] at h
  have hπ := pi_pos
  have e : π / 2 * ε ^ 2 * modeSq j t s = π * (ε ^ 2 / 2 * modeSq j t s) := by ring
  rw [e] at h
  exact le_of_mul_le_mul_left h hπ

theorem ofReal_modeSq_le_eLpNorm_sq {j : ℕ} (hj : 1 ≤ j) {t s : ℝ} (ht : t ∈ J j)
    (hs : s ∈ J j) (ε : ℝ) :
    ENNReal.ofReal (ε ^ 2 / 2 * modeSq j t s) ≤
      eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π)) ^ 2 := by
  rw [← ENNReal.ofReal_toReal (eLpNorm_a_sub_ne_top D ε t s), ← ENNReal.ofReal_pow
    ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal (modeSq_le_eLpNorm_sq D hj ht hs ε)

/-! ### The first mode at `x = 0` -/

/-- At `x = 0`, the first mode `K = K_{j,1}` dominates the increment on `J_j`:
`|𝔞(t,0) − 𝔞(s,0)| ≥ ε K⁻¹ |sin θ_{j,1}(t) − sin θ_{j,1}(s)| − 2 ε K⁻¹/15`. -/
theorem abs_a_sub_zero_ge {ε : ℝ} (hε : 0 ≤ ε) {j : ℕ} (hj : 1 ≤ j) {t s : ℝ} (ht : t ∈ J j)
    (hs : s ∈ J j) :
    ε * (((K j 1 : ℝ))⁻¹ * |sin (θ j 1 t) - sin (θ j 1 s)|) - ε * (2 * (((K j 1 : ℝ))⁻¹ / 15))
      ≤ |a D ε t 0 - a D ε s 0| := by
  have hsum : β D t 0 - β D s 0 = ∑ m ∈ Finset.Icc 1 (M j),
      ((K j m : ℝ))⁻¹ * (sin (θ j m t) - sin (θ j m s)) := by
    rw [β_at_zero_of_mem_J D hj ht, β_at_zero_of_mem_J D hj hs, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 (M j) := Finset.mem_Icc.mpr ⟨le_rfl, hj⟩
  have hsplit := Finset.add_sum_erase _
    (fun m => ((K j m : ℝ))⁻¹ * (sin (θ j m t) - sin (θ j m s))) h1mem
  have htail : |∑ m ∈ (Finset.Icc 1 (M j)).erase 1,
      ((K j m : ℝ))⁻¹ * (sin (θ j m t) - sin (θ j m s))| ≤ 2 * (((K j 1 : ℝ))⁻¹ / 15) := by
    calc _ ≤ ∑ m ∈ (Finset.Icc 1 (M j)).erase 1,
            |((K j m : ℝ))⁻¹ * (sin (θ j m t) - sin (θ j m s))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ (Finset.Icc 1 (M j)).erase 1, 2 * ((K j m : ℝ))⁻¹ := by
          refine Finset.sum_le_sum fun m _ => ?_
          have hpos : (0 : ℝ) ≤ ((K j m : ℝ))⁻¹ := by positivity
          rw [abs_mul, abs_of_nonneg hpos]
          have hb : |sin (θ j m t) - sin (θ j m s)| ≤ 2 := by
            rw [abs_le]
            constructor <;> linarith [neg_one_le_sin (θ j m t), sin_le_one (θ j m s),
              sin_le_one (θ j m t), neg_one_le_sin (θ j m s)]
          nlinarith
      _ = 2 * ∑ m ∈ (Finset.Icc 1 (M j)).erase 1, ((K j m : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 2 * (((K j 1 : ℝ))⁻¹ / 15) := by linarith [sum_erase_K_inv_le hj]
  have hdiff : a D ε t 0 - a D ε s 0 = ε * (β D t 0 - β D s 0) := by unfold a; ring
  rw [hdiff, abs_mul, abs_of_nonneg hε, hsum, ← hsplit]
  have hfirst : |((K j 1 : ℝ))⁻¹ * (sin (θ j 1 t) - sin (θ j 1 s))|
      = ((K j 1 : ℝ))⁻¹ * |sin (θ j 1 t) - sin (θ j 1 s)| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((K j 1 : ℝ))⁻¹)]
  have habs := abs_sub_abs_le_abs_sub
    (((K j 1 : ℝ))⁻¹ * (sin (θ j 1 t) - sin (θ j 1 s)))
    (-∑ m ∈ (Finset.Icc 1 (M j)).erase 1, ((K j m : ℝ))⁻¹ * (sin (θ j m t) - sin (θ j m s)))
  rw [abs_neg, sub_neg_eq_add, hfirst] at habs
  rw [← mul_sub]
  exact mul_le_mul_of_nonneg_left (by linarith) hε

/-- The middle thirds lie in `[0,1]`. -/
theorem J_subset_Icc {j : ℕ} (hj : 1 ≤ j) : J j ⊆ Icc (0 : ℝ) 1 := by
  intro s hs
  have h := I_subset hj (J_subset_I hj hs)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end LionsC12
