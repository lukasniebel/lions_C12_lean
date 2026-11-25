module

public import LionsC12.Spaces.Line

/-!
# Time regularity of `L²`-valued functions with a fixed compact support

For a family `G : ℝ → X → F` of square integrable functions which all vanish outside a fixed
set `K` of finite measure, uniform estimates on `K` give the corresponding statements in
`L²(X;F)`:

* `norm_toLp_le_of_bound` — `‖h‖_{L²} ≤ C μ(K)^{1/2}` if `‖h‖ ≤ C` on `K` and `h = 0` off `K`;
* `continuousAt_toLp` — uniform convergence on `K` gives continuity into `L²`;
* `hasDerivAt_toLp` — a pointwise time derivative which is uniformly continuous on `K` is the
  derivative in `L²` (mean value theorem);
* `eventually_norm_sub_le_of_continuousOn` — joint continuity on `[t₀ - δ, t₀ + δ] × K`, `K`
  compact, gives the uniform estimate;
* `norm_toLp_sq` — `‖h‖²_{L²} = ∫ ‖h‖²`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]

theorem norm_toLp_sq {h : X → F} (hm : MemLp h 2 μ) :
    ‖hm.toLp h‖ ^ 2 = ∫ x, ‖h x‖ ^ 2 ∂μ := by
  have e := (Lp.memLp (hm.toLp h)).eLpNorm_eq_integral_rpow_norm two_ne_zero
    ENNReal.ofNat_ne_top
  rw [Lp.norm_def, e, ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  norm_num
  refine integral_congr_ae ?_
  filter_upwards [hm.coeFn_toLp] with x hx
  rw [hx]

/-- The constant `μ(K)^{1/2}`. -/
def sqrtMeas (μ : Measure X) (K : Set X) : ℝ := ((μ K) ^ (2 : ℝ≥0∞).toReal⁻¹).toReal

theorem sqrtMeas_nonneg (μ : Measure X) (K : Set X) : 0 ≤ sqrtMeas μ K := ENNReal.toReal_nonneg

theorem norm_toLp_le_of_bound {K : Set X} (hK : MeasurableSet K) (hKμ : μ K < ∞) {h : X → F}
    (hm : MemLp h 2 μ) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ K, ‖h x‖ ≤ C) (h0 : ∀ x ∉ K, h x = 0) :
    ‖hm.toLp h‖ ≤ C * sqrtMeas μ K := by
  rw [Lp.norm_toLp]
  have hsupp : Function.support h ⊆ K := fun x hx => by
    by_contra hK
    exact hx (h0 x hK)
  rw [← eLpNorm_restrict_eq_of_support_subset hm.aestronglyMeasurable hsupp]
  have hle : eLpNorm h 2 (μ.restrict K) ≤ (μ.restrict K) univ ^ (2 : ℝ≥0∞).toReal⁻¹
      * ENNReal.ofReal C := by
    refine eLpNorm_le_of_ae_bound hm.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem hK] with x hx
    exact hb x hx
  rw [Measure.restrict_apply_univ] at hle
  have hfin : (μ K) ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal C ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hKμ.ne)
      ENNReal.ofReal_ne_top
  calc (eLpNorm h 2 (μ.restrict K)).toReal
      ≤ ((μ K) ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal C).toReal := ENNReal.toReal_mono hfin hle
    _ = C * sqrtMeas μ K := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, mul_comm]
      rfl

/-- Uniform convergence on `K` gives continuity into `L²`. -/
theorem continuousAt_toLp {G : ℝ → X → F} (hm : ∀ t, MemLp (G t) 2 μ) {K : Set X}
    (hK : MeasurableSet K) (hKμ : μ K < ∞) (h0 : ∀ t, ∀ x ∉ K, G t x = 0) {t₀ : ℝ}
    (hu : ∀ η > 0, ∀ᶠ t in 𝓝 t₀, ∀ x ∈ K, ‖G t x - G t₀ x‖ ≤ η) :
    ContinuousAt (fun t => (hm t).toLp (G t)) t₀ := by
  set M := sqrtMeas μ K
  have hM : 0 ≤ M := sqrtMeas_nonneg μ K
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro η hη
  filter_upwards [hu (η / (2 * (M + 1))) (by positivity)] with t ht
  rw [dist_eq_norm, ← MemLp.toLp_sub]
  have hb := norm_toLp_le_of_bound hK hKμ ((hm t).sub (hm t₀)) (C := η / (2 * (M + 1)))
    (by positivity) (fun x hx => by simpa using ht x hx)
    (fun x hx => by simp [h0 t x hx, h0 t₀ x hx])
  calc _ ≤ η / (2 * (M + 1)) * M := hb
    _ < η := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith

/-- A pointwise time derivative which is uniformly continuous on `K` at `t₀` is the derivative
in `L²` at `t₀`. -/
theorem hasDerivAt_toLp [NormedSpace ℝ F] {G G' : ℝ → X → F} (hm : ∀ t, MemLp (G t) 2 μ)
    {t₀ : ℝ} (hm' : MemLp (G' t₀) 2 μ) {K : Set X} (hK : MeasurableSet K) (hKμ : μ K < ∞)
    (h0 : ∀ t, ∀ x ∉ K, G t x = 0) (h0' : ∀ x ∉ K, G' t₀ x = 0)
    (hd : ∀ t, ∀ x ∈ K, HasDerivAt (fun τ => G τ x) (G' t x) t)
    (hu : ∀ η > 0, ∀ᶠ t in 𝓝 t₀, ∀ x ∈ K, ‖G' t x - G' t₀ x‖ ≤ η) :
    HasDerivAt (fun t => (hm t).toLp (G t)) (hm'.toLp (G' t₀)) t₀ := by
  set M := sqrtMeas μ K
  have hM : 0 ≤ M := sqrtMeas_nonneg μ K
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hu (c / (M + 1)) (by positivity))
  filter_upwards [Metric.ball_mem_nhds t₀ hδ] with t ht
  have hmv : ∀ x ∈ K, ‖G t x - G t₀ x - (t - t₀) • G' t₀ x‖ ≤ c / (M + 1) * ‖t - t₀‖ := by
    intro x hx
    have hderiv : ∀ τ ∈ Metric.ball t₀ δ, HasDerivWithinAt (fun τ => G τ x - τ • G' t₀ x)
        (G' τ x - G' t₀ x) (Metric.ball t₀ δ) τ := by
      intro τ _
      have h1 := (hd τ x hx).sub ((hasDerivAt_id τ).smul_const (G' t₀ x))
      simp only [id, one_smul] at h1
      exact h1.hasDerivWithinAt
    have hbd : ∀ τ ∈ Metric.ball t₀ δ, ‖G' τ x - G' t₀ x‖ ≤ c / (M + 1) :=
      fun τ hτ => hball τ hτ x hx
    have := (convex_ball t₀ δ).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbd
      (Metric.mem_ball_self hδ) ht
    have e : G t x - t • G' t₀ x - (G t₀ x - t₀ • G' t₀ x)
        = G t x - G t₀ x - (t - t₀) • G' t₀ x := by
      rw [sub_smul]; abel
    rwa [e] at this
  have hH : MemLp (G t - G t₀ - (t - t₀) • G' t₀) 2 μ := ((hm t).sub (hm t₀)).sub (hm'.const_smul _)
  have heq : (hm t).toLp (G t) - (hm t₀).toLp (G t₀) - (t - t₀) • hm'.toLp (G' t₀)
      = hH.toLp _ := by
    rw [← MemLp.toLp_sub, ← MemLp.toLp_const_smul, ← MemLp.toLp_sub]
  rw [heq]
  have hb := norm_toLp_le_of_bound hK hKμ hH (C := c / (M + 1) * ‖t - t₀‖) (by positivity)
    (fun x hx => by simpa using hmv x hx)
    (fun x hx => by simp [h0 t x hx, h0 t₀ x hx, h0' x hx])
  calc _ ≤ c / (M + 1) * ‖t - t₀‖ * M := hb
    _ ≤ c * ‖t - t₀‖ := by
      rw [div_mul_eq_mul_div, mul_div_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg (t - t₀)]

/-- Joint continuity on `[t₀ - δ, t₀ + δ] × K`, `K` compact, gives uniform convergence on `K`. -/
theorem eventually_norm_sub_le_of_continuousOn {Y : Type*} [PseudoMetricSpace Y]
    {G : ℝ → Y → F} {K : Set Y} (hK : IsCompact K) {t₀ δ : ℝ} (hδ : 0 < δ)
    (hc : ContinuousOn (Function.uncurry G) (Icc (t₀ - δ) (t₀ + δ) ×ˢ K)) :
    ∀ η > 0, ∀ᶠ t in 𝓝 t₀, ∀ x ∈ K, ‖G t x - G t₀ x‖ ≤ η := by
  intro η hη
  have hS : IsCompact (Icc (t₀ - δ) (t₀ + δ) ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨δ', hδ', hu⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous hc) η hη
  filter_upwards [Metric.ball_mem_nhds t₀ (lt_min hδ hδ')] with t ht x hx
  rw [Metric.mem_ball, Real.dist_eq] at ht
  have ht1 : |t - t₀| < δ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht2 : |t - t₀| < δ' := lt_of_lt_of_le ht (min_le_right _ _)
  have hmem1 : (t, x) ∈ Icc (t₀ - δ) (t₀ + δ) ×ˢ K :=
    ⟨⟨by linarith [neg_abs_le (t - t₀)], by linarith [le_abs_self (t - t₀)]⟩, hx⟩
  have hmem2 : (t₀, x) ∈ Icc (t₀ - δ) (t₀ + δ) ×ˢ K :=
    ⟨⟨by linarith, by linarith⟩, hx⟩
  have hdist : dist (t, x) (t₀, x) < δ' := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq]
    simpa using ht2
  have := hu _ hmem1 _ hmem2 hdist
  rw [dist_eq_norm] at this
  exact this.le

end LionsC12
