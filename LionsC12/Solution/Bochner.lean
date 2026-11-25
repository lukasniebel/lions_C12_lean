module

public import LionsC12.Construction.Defs
public import LionsC12.Coefficient.Blocks
public import LionsC12.Coefficient.Support
public import LionsC12.Modes.Trig
public import LionsC12.Modes.Vprime
public import LionsC12.Coefficient.Holder
public import LionsC12.Solution.Basic
public import LionsC12.Forcing.Cancellation
public import LionsC12.Forcing.Continuity
public import LionsC12.Solution.L1
public import LionsC12.Forcing.Elliptic

/-!
# Lemma 4.1 / Proposition 5.1 in Bochner form

`u ∈ C([0,1];H) ∩ C([0,1];V) ∩ C¹([0,1];V')`, `f ∈ C([0,1];H)`, `𝔞 ∈ C([0,1];L^∞)`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ## Auxiliary: slices of jointly continuous functions -/

private lemma cont_slice {g : ℝ → ℝ → ℝ} (hg : Continuous fun q : ℝ × ℝ => g q.1 q.2) (t : ℝ) :
    Continuous (g t) :=
  Continuous.uncurry_left (f := g) t hg

/-! ## Joint continuity of `∂_x u` -/

theorem abs_vx_le_dist (ε : ℝ) (t x : ℝ) :
    |vx D ε t x| ≤ |ε| * (2 / 15) * |t - 5 / 16| := by
  by_cases hex : ∃ j, t ∈ I j
  · obtain ⟨j, htj⟩ := hex
    have hj1 : 1 ≤ j := one_le_of_mem_I htj
    have hℓ0 : 0 < ℓ j := ℓ_pos hj1
    have hd : ℓ j ≤ 5 / 16 - t := ℓ_le_dist_of_mem_I htj
    have hS : S j ≤ ℓ j / 15 := S_le hj1
    have habs : |t - 5 / 16| = 5 / 16 - t := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have hb := abs_vxblock_le' D ε hj1 t x
    have hε := abs_nonneg ε
    rw [vx_eq_block D ε htj, habs]
    nlinarith [hb, hS, hd, hε]
  · rw [not_exists] at hex
    rw [vx_eq_zero D ε hex, abs_zero]
    positivity

theorem continuous_vx (ε : ℝ) : Continuous (fun q : ℝ × ℝ => vx D ε q.1 q.2) := by
  refine continuous_of_blocks (D := D) (gb := fun j t x => vxblock D ε j t x)
    (h := fun t => |ε| * (2 / 15) * |t - 5 / 16|) (fun j => continuous_vxblock D ε j) ?_ ?_ ?_ ?_
  · intro j t hj x
    exact vx_eq_block' D ε (fun i hi => (hj i hi).1) x
  · fun_prop
  · norm_num
  · intro t x
    exact abs_vx_le_dist D ε t x

theorem continuous_ux (ε : ℝ) : Continuous (fun q : ℝ × ℝ => ux D ε q.1 q.2) := by
  have h1 : Continuous D.ρ := continuous_ρ D
  have h2 : Continuous φ' := continuous_φ'
  have h3 := continuous_vx D ε
  show Continuous fun q : ℝ × ℝ => D.ρ q.1 * φ' q.2 + vx D ε q.1 q.2
  fun_prop

/-! ## Continuity of `∂_t u` and `∂_x² u` away from `t = 5/16` -/

theorem vt_eq_block' (ε : ℝ) {j : ℕ} {t : ℝ}
    (h : ∀ i, i ≠ j → ηj D i t = 0 ∧ ηj' D i t = 0) (x : ℝ) :
    vt D ε t x = vtblock D ε j t x :=
  finsum_eq_single (fun i => vtblock D ε i t x) j fun _i hi =>
    vtblock_eq_zero_of_ηj D ε (h _ hi).1 (h _ hi).2 x

theorem continuousAt_vt (ε : ℝ) {t₀ : ℝ} (ht₀ : t₀ ≠ 5 / 16) (x₀ : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => vt D ε q.1 q.2) (t₀, x₀) :=
  continuousAt_of_blocks D (fun j => continuous_vtblock D ε j)
    (fun _j _t hj x => vt_eq_block' D ε hj x) ht₀ x₀

theorem continuousAt_ut (ε : ℝ) {t₀ : ℝ} (ht₀ : t₀ ≠ 5 / 16) (x₀ : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => ut D ε q.1 q.2) (t₀, x₀) := by
  have h1 : ContinuousAt (fun q : ℝ × ℝ => D.ρ' q.1 * φ q.2) (t₀, x₀) := by
    have hr := D.ρ'_continuous
    have hf := continuous_φ
    fun_prop
  have h2 := continuousAt_vt D ε ht₀ x₀
  show ContinuousAt (fun q : ℝ × ℝ => D.ρ' q.1 * φ q.2 + vt D ε q.1 q.2) (t₀, x₀)
  exact h1.add h2

/-! ## From joint continuity to continuity with values in `L²(0,π)` and `L^∞(0,π)` -/

/-- Tube-lemma style uniformity on the compact `[0,π]`. -/
private lemma eventually_forall_abs_sub_lt {g : ℝ → ℝ → ℝ} {t₀ : ℝ}
    (hg : ∀ x : ℝ, ContinuousAt (fun q : ℝ × ℝ => g q.1 q.2) (t₀, x))
    (hg₀ : Continuous (g t₀)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in nhds t₀, ∀ x ∈ Set.Icc (0 : ℝ) π, |g t x - g t₀ x| < η := by
  refine isCompact_Icc.eventually_forall_of_forall_eventually ?_
  intro x _
  have h2 : ContinuousAt (fun z : ℝ × ℝ => g t₀ z.2) (t₀, x) :=
    (hg₀.comp continuous_snd).continuousAt
  have hcont : ContinuousAt (fun z : ℝ × ℝ => |g z.1 z.2 - g t₀ z.2|) (t₀, x) :=
    ((hg x).sub h2).abs
  have h0 : |g (t₀, x).1 (t₀, x).2 - g t₀ (t₀, x).2| < η := by simpa using hη
  exact hcont (gt_mem_nhds h0)

/-- `‖·‖²_{L²(0,π)} ≤ π · sup²`. -/
theorem normSq_le_of_bound {d : ℝ → ℝ} (hd : Continuous d) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ x ∈ Set.Icc (0 : ℝ) π, |d x| ≤ δ) : normSq d ≤ π * δ ^ 2 := by
  have h1 : (∫ x in (0:ℝ)..π, d x ^ 2) ≤ ∫ _x in (0:ℝ)..π, δ ^ 2 := by
    refine intervalIntegral.integral_mono_on Real.pi_pos.le ?_ intervalIntegrable_const ?_
    · exact (by fun_prop : Continuous fun x : ℝ => d x ^ 2).intervalIntegrable 0 π
    · intro x hx
      have hb := h x hx
      nlinarith [abs_nonneg (d x), sq_abs (d x)]
  rw [intervalIntegral.integral_const] at h1
  simpa [normSq] using h1

private lemma eventually_normSq_sub_le {g : ℝ → ℝ → ℝ} {t₀ : ℝ}
    (hg : ∀ x : ℝ, ContinuousAt (fun q : ℝ × ℝ => g q.1 q.2) (t₀, x))
    (hslice : ∀ s : ℝ, Continuous (g s)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in nhds t₀, normSq (fun x => g t x - g t₀ x) ≤ η := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  have hδ0 : 0 < Real.sqrt (η / π) := Real.sqrt_pos.mpr (by positivity)
  have hδsq : Real.sqrt (η / π) ^ 2 = η / π := Real.sq_sqrt (by positivity)
  filter_upwards [eventually_forall_abs_sub_lt hg (hslice t₀) hδ0] with t ht
  have hc : Continuous fun x => g t x - g t₀ x := by
    have h1 := hslice t; have h2 := hslice t₀; fun_prop
  have hb := normSq_le_of_bound hc hδ0.le (fun x hx => (ht x hx).le)
  rw [hδsq] at hb
  calc normSq (fun x => g t x - g t₀ x) ≤ π * (η / π) := hb
    _ = η := by field_simp

/-- A jointly continuous function is continuous in time with values in `L²(0,π)`. -/
theorem tendsto_normSq_sub_of_continuous (g : ℝ → ℝ → ℝ)
    (hg : Continuous (fun q : ℝ × ℝ => g q.1 q.2)) (t₀ : ℝ) :
    Filter.Tendsto (fun t => normSq (fun x => g t x - g t₀ x)) (nhds t₀) (nhds 0) := by
  have hslice : ∀ s : ℝ, Continuous (g s) := fun s => cont_slice hg s
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [eventually_normSq_sub_le (fun _ => hg.continuousAt) hslice (half_pos hη)]
    with t ht
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (normSq_nonneg _)]
  linarith

/-- `u ∈ C([0,1];H)`. -/
theorem u_tendsto_H (ε t₀ : ℝ) :
    Filter.Tendsto (fun t => normSq (fun x => u D ε t x - u D ε t₀ x)) (nhds t₀) (nhds 0) :=
  tendsto_normSq_sub_of_continuous _ (continuous_u D ε) t₀

/-- `u ∈ C([0,1];V)` (`‖·‖_V = ‖∂_x ·‖_H`). -/
theorem u_tendsto_V (ε t₀ : ℝ) :
    Filter.Tendsto (fun t => normSq (fun x => ux D ε t x - ux D ε t₀ x)) (nhds t₀) (nhds 0) :=
  tendsto_normSq_sub_of_continuous _ (continuous_ux D ε) t₀

/-- `f ∈ C([0,1];H)` (Proposition 5.1). -/
theorem f_tendsto_H (ε t₀ : ℝ) :
    Filter.Tendsto (fun t => normSq (fun x => f D ε t x - f D ε t₀ x)) (nhds t₀) (nhds 0) :=
  tendsto_normSq_sub_of_continuous _ (continuous_f D ε) t₀

/-! ## Test functions and the Poincaré inequality -/

/-- Test functions in `V = H¹₀(0,π)`: `C¹` with zero boundary values; `‖w‖_V = √(normSq w')`. -/
structure IsTest (w w' : ℝ → ℝ) : Prop where
  hasDerivAt : ∀ x, HasDerivAt w (w' x) x
  cont' : Continuous w'
  zero_left : w 0 = 0
  zero_right : w π = 0

theorem IsTest.continuous {w w' : ℝ → ℝ} (hw : IsTest w w') : Continuous w :=
  continuous_iff_continuousAt.2 fun x => (hw.hasDerivAt x).continuousAt

/-- Cauchy–Schwarz against the constant `1` on `[0,b]`. -/
private lemma sq_integral_le_mul {b : ℝ} (hb : 0 ≤ b) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ x in (0:ℝ)..b, g x) ^ 2 ≤ b * ∫ x in (0:ℝ)..b, g x ^ 2 := by
  have iA : IntervalIntegrable (fun x : ℝ => g x ^ 2) MeasureTheory.volume 0 b :=
    (by fun_prop : Continuous fun x : ℝ => g x ^ 2).intervalIntegrable 0 b
  have iG : IntervalIntegrable g MeasureTheory.volume 0 b := hg.intervalIntegrable 0 b
  have expand : ∀ lam : ℝ, (∫ x in (0:ℝ)..b, (g x - lam) ^ 2)
      = (∫ x in (0:ℝ)..b, g x ^ 2) + (-(2 * lam)) * (∫ x in (0:ℝ)..b, g x) + (lam * lam) * b := by
    intro lam
    have iB : IntervalIntegrable (fun x : ℝ => (-(2 * lam)) * g x) MeasureTheory.volume 0 b :=
      (iG.const_mul _)
    have iC : IntervalIntegrable (fun _x : ℝ => lam * lam) MeasureTheory.volume 0 b :=
      intervalIntegrable_const
    have e : ∀ x : ℝ, (g x - lam) ^ 2 = g x ^ 2 + (-(2 * lam)) * g x + lam * lam := by
      intro x; ring
    simp_rw [e]
    rw [intervalIntegral.integral_add (iA.add iB) iC, intervalIntegral.integral_add iA iB,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have key : ∀ lam : ℝ,
      0 ≤ b * (lam * lam) + (-2 * (∫ x in (0:ℝ)..b, g x)) * lam + (∫ x in (0:ℝ)..b, g x ^ 2) := by
    intro lam
    have h0 : (0 : ℝ) ≤ ∫ x in (0:ℝ)..b, (g x - lam) ^ 2 :=
      intervalIntegral.integral_nonneg hb fun _ _ => sq_nonneg _
    rw [expand lam] at h0
    nlinarith [h0]
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

/-- Poincaré inequality on `(0,π)` with constant `π²`. -/
theorem normSq_le_of_isTest {w w' : ℝ → ℝ} (hw : IsTest w w') : normSq w ≤ π ^ 2 * normSq w' := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  have hwc := hw.continuous
  have hw'c : Continuous w' := hw.cont'
  have hFTC : ∀ x : ℝ, w x = ∫ y in (0:ℝ)..x, w' y := by
    intro x
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := w) (f' := w') (a := 0) (b := x) (fun y _ => hw.hasDerivAt y)
      (hw.cont'.intervalIntegrable 0 x)
    rw [this, hw.zero_left, sub_zero]
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun y : ℝ => w' y ^ 2) MeasureTheory.volume a b :=
    fun a b => (by fun_prop : Continuous fun y : ℝ => w' y ^ 2).intervalIntegrable a b
  have hkey : ∀ x ∈ Set.Icc (0:ℝ) π, w x ^ 2 ≤ π * normSq w' := by
    intro x hx
    have hx0 : (0:ℝ) ≤ x := hx.1
    have hxπ : x ≤ π := hx.2
    have h1 : (∫ y in (0:ℝ)..x, w' y) ^ 2 ≤ x * ∫ y in (0:ℝ)..x, w' y ^ 2 :=
      sq_integral_le_mul hx0 hw.cont'
    have h2 : (∫ y in (0:ℝ)..x, w' y ^ 2) + (∫ y in x..π, w' y ^ 2) = normSq w' := by
      have := intervalIntegral.integral_add_adjacent_intervals
        (f := fun y : ℝ => w' y ^ 2) (a := 0) (b := x) (c := π)
        (hii 0 x) (hii x π)
      simpa [normSq] using this
    have h3 : (0:ℝ) ≤ ∫ y in x..π, w' y ^ 2 :=
      intervalIntegral.integral_nonneg hxπ fun _ _ => sq_nonneg _
    have h4 : (∫ y in (0:ℝ)..x, w' y ^ 2) ≤ normSq w' := by linarith
    have h5 : (0:ℝ) ≤ ∫ y in (0:ℝ)..x, w' y ^ 2 :=
      intervalIntegral.integral_nonneg hx0 fun _ _ => sq_nonneg _
    rw [hFTC x]
    nlinarith [h1, h4, h5]
  have h6 : normSq w ≤ ∫ _x in (0:ℝ)..π, π * normSq w' := by
    refine intervalIntegral.integral_mono_on hπ.le ?_ intervalIntegrable_const hkey
    exact (by fun_prop : Continuous fun x : ℝ => w x ^ 2).intervalIntegrable 0 π
  rw [intervalIntegral.integral_const] at h6
  simp only [sub_zero, smul_eq_mul] at h6
  calc normSq w ≤ π * (π * normSq w') := h6
    _ = π ^ 2 * normSq w' := by ring

theorem sqrt_normSq_le_of_isTest {w w' : ℝ → ℝ} (hw : IsTest w w') :
    Real.sqrt (normSq w) ≤ π * Real.sqrt (normSq w') := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  calc Real.sqrt (normSq w) ≤ Real.sqrt (π ^ 2 * normSq w') :=
        Real.sqrt_le_sqrt (normSq_le_of_isTest hw)
    _ = π * Real.sqrt (normSq w') := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hπ.le]

/-! ## Elementary algebra of the `L²(0,π)` pairing -/

theorem inner_add_left' {g h w : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h)
    (hw : Continuous w) : inner (fun x => g x + h x) w = inner g w + inner h w := by
  simp only [inner]
  have e : ∀ x : ℝ, (g x + h x) * w x = g x * w x + h x * w x := fun x => by ring
  simp_rw [e]
  exact intervalIntegral.integral_add
    ((by fun_prop : Continuous fun x : ℝ => g x * w x).intervalIntegrable 0 π)
    ((by fun_prop : Continuous fun x : ℝ => h x * w x).intervalIntegrable 0 π)

theorem inner_sub_left' {g h w : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h)
    (hw : Continuous w) : inner (fun x => g x - h x) w = inner g w - inner h w := by
  simp only [inner]
  have e : ∀ x : ℝ, (g x - h x) * w x = g x * w x - h x * w x := fun x => by ring
  simp_rw [e]
  exact intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun x : ℝ => g x * w x).intervalIntegrable 0 π)
    ((by fun_prop : Continuous fun x : ℝ => h x * w x).intervalIntegrable 0 π)

theorem inner_smul_left' (c : ℝ) (g w : ℝ → ℝ) :
    inner (fun x => c * g x) w = c * inner g w := by
  simp only [inner]
  have e : ∀ x : ℝ, c * g x * w x = c * (g x * w x) := fun x => by ring
  simp_rw [e]
  exact intervalIntegral.integral_const_mul _ _

theorem inner_zero_left (w : ℝ → ℝ) : inner (fun _ : ℝ => (0:ℝ)) w = 0 := by
  simp [inner]

theorem inner_sum_p (s : Finset ℕ) (Kf : ℕ → ℕ) (cf : ℕ → ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    inner (fun x => ∑ m ∈ s, cf m * p (Kf m) x) w = ∑ m ∈ s, cf m * inner (p (Kf m)) w := by
  have e : ∀ x : ℝ, (∑ m ∈ s, cf m * p (Kf m) x) * w x
      = ∑ m ∈ s, cf m * (p (Kf m) x * w x) := by
    intro x
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  simp only [inner]
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl fun m _ => intervalIntegral.integral_const_mul _ _
  · intro m _
    refine Continuous.intervalIntegrable ?_ 0 π
    have hp : Continuous (p (Kf m)) := continuous_p _
    fun_prop

theorem inner_vblock_eq (ε : ℝ) (j : ℕ) (t : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    inner (vblock D ε j t) w
      = ∑ m ∈ Finset.Icc 1 (M j), y D ε j m t * inner (p (K j m)) w :=
  inner_sum_p (Finset.Icc 1 (M j)) (K j) (fun m => y D ε j m t) hw

theorem inner_vtblock_eq (ε : ℝ) (j : ℕ) (t : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    inner (vtblock D ε j t) w
      = ∑ m ∈ Finset.Icc 1 (M j), y' D ε j m t * inner (p (K j m)) w :=
  inner_sum_p (Finset.Icc 1 (M j)) (K j) (fun m => y' D ε j m t) hw

/-! ## The `V'`-bound for `∂_t v` -/

/-- `|⟨∂_t v_j(t), w⟩| ≤ 3 ε (Cη+1) S_j ‖w'‖_H`. -/
theorem abs_inner_vtblock_le {ε : ℝ} (hε0 : 0 ≤ ε) {j : ℕ} (hj : 1 ≤ j) (t : ℝ)
    {w w' : ℝ → ℝ} (hw : IsTest w w') :
    |inner (vtblock D ε j t) w| ≤ 3 * ε * (D.Cη + 1) * S j * Real.sqrt (normSq w') := by
  have hwc := hw.continuous
  have hN : (0:ℝ) ≤ Real.sqrt (normSq w') := Real.sqrt_nonneg _
  have hc : (0:ℝ) ≤ ε * (D.Cη + 1) := mul_nonneg hε0 (by linarith [D.Cη_nonneg])
  rw [inner_vtblock_eq D ε j t hwc]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hbound : ∀ m ∈ Finset.Icc 1 (M j),
      |y' D ε j m t * inner (p (K j m)) w|
        ≤ ε * (D.Cη + 1) * (3 / (K j m : ℝ) * Real.sqrt (normSq w')) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hK : 2 < K j m := two_lt_K hj hm1
    rw [abs_mul]
    exact mul_le_mul (abs_y'_le D hε0 hj m t)
      (abs_inner_p_le hK w w' hw.hasDerivAt hw.cont' hw.zero_left hw.zero_right)
      (abs_nonneg _) hc
  refine (Finset.sum_le_sum hbound).trans ?_
  have hsum : ∑ m ∈ Finset.Icc 1 (M j),
      ε * (D.Cη + 1) * (3 / (K j m : ℝ) * Real.sqrt (normSq w'))
      = (3 * ε * (D.Cη + 1) * Real.sqrt (normSq w'))
          * ∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [div_eq_mul_inv]
    ring
  rw [hsum]
  simp only [S]
  exact le_of_eq (by ring)

/-! ## Values at the endpoint `t = 5/16` -/

theorem ρ'_at_top : D.ρ' (5/16 : ℝ) = 0 := D.ρ'_zero _ (by norm_num)

theorem vt_at_top (ε : ℝ) : vt D ε (5/16 : ℝ) = fun _ => (0:ℝ) :=
  funext fun x => vt_eq_zero D ε (fun j => five_sixteenths_notMem_I j) x

theorem ut_at_top (ε : ℝ) : ut D ε (5/16 : ℝ) = fun _ => (0:ℝ) := by
  funext x
  show D.ρ' (5/16 : ℝ) * φ x + vt D ε (5/16 : ℝ) x = 0
  rw [ρ'_at_top D, congrFun (vt_at_top D ε) x]
  ring

/-! ## Splitting the pairing -/

theorem inner_u_eq (ε t : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    inner (u D ε t) w = D.ρ t * inner φ w + inner (v D ε t) w := by
  have hφ := continuous_φ
  have h1 : inner (u D ε t) w = inner (fun x => D.ρ t * φ x + v D ε t x) w := rfl
  rw [h1, inner_add_left' (by fun_prop) (cont_slice (continuous_v D ε) t) hw, inner_smul_left']

theorem inner_ut_eq (ε t : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    inner (ut D ε t) w = D.ρ' t * inner φ w + inner (vt D ε t) w := by
  have hφ := continuous_φ
  have h1 : inner (ut D ε t) w = inner (fun x => D.ρ' t * φ x + vt D ε t x) w := rfl
  rw [h1, inner_add_left' (by fun_prop) (continuous_vt_x D ε t) hw, inner_smul_left']

/-- The global `V'`-bound for `∂_t v`, decaying like `|t - 5/16|`. -/
theorem abs_inner_vt_le {ε : ℝ} (hε0 : 0 ≤ ε) (t : ℝ) {w w' : ℝ → ℝ} (hw : IsTest w w') :
    |inner (vt D ε t) w| ≤ ε * (D.Cη + 1) / 5 * |t - 5 / 16| * Real.sqrt (normSq w') := by
  have hN : (0:ℝ) ≤ Real.sqrt (normSq w') := Real.sqrt_nonneg _
  have hc : (0:ℝ) ≤ ε * (D.Cη + 1) := mul_nonneg hε0 (by linarith [D.Cη_nonneg])
  rcases mem_block_or_not t with ⟨j, htj⟩ | hno
  · have hj1 : 1 ≤ j := one_le_of_mem_I htj
    have hℓ0 : 0 < ℓ j := ℓ_pos hj1
    have hd : ℓ j ≤ 5 / 16 - t := ℓ_le_dist_of_mem_I htj
    have hS : S j ≤ ℓ j / 15 := S_le hj1
    have habs : |t - 5 / 16| = 5 / 16 - t := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have heq : vt D ε t = vtblock D ε j t := funext fun x => vt_eq_block D ε htj x
    rw [heq, habs]
    refine (abs_inner_vtblock_le D hε0 hj1 t hw).trans ?_
    have key : 3 * S j ≤ (5/16 - t) / 5 := by linarith
    calc 3 * ε * (D.Cη + 1) * S j * Real.sqrt (normSq w')
        = (ε * (D.Cη + 1) * Real.sqrt (normSq w')) * (3 * S j) := by ring
      _ ≤ (ε * (D.Cη + 1) * Real.sqrt (normSq w')) * ((5/16 - t) / 5) :=
          mul_le_mul_of_nonneg_left key (mul_nonneg hc hN)
      _ = ε * (D.Cη + 1) / 5 * (5/16 - t) * Real.sqrt (normSq w') := by ring
  · have heq : vt D ε t = fun _ => (0:ℝ) := funext fun x => vt_eq_zero D ε hno x
    rw [heq, inner_zero_left, abs_zero]
    have h1 : (0:ℝ) ≤ ε * (D.Cη + 1) / 5 := by linarith
    exact mul_nonneg (mul_nonneg h1 (abs_nonneg _)) hN

/-! ## `∂_t u ∈ C([0,1];V')` -/

theorem ut_tendsto_V' {ε : ℝ} (hε0 : 0 ≤ ε) (t₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in nhds t₀, ∀ w w' : ℝ → ℝ, IsTest w w' →
      |inner (fun x => ut D ε t x - ut D ε t₀ x) w| ≤ η * Real.sqrt (normSq w') := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  by_cases ht₀ : t₀ = 5 / 16
  · subst ht₀
    have hut0 : ∀ x, ut D ε (5/16 : ℝ) x = 0 := fun x => congrFun (ut_at_top D ε) x
    have hC₀ : (0:ℝ) ≤ π * Real.sqrt (normSq φ) := by positivity
    have h1 : ∀ᶠ t in nhds (5/16 : ℝ), |D.ρ' t| * (π * Real.sqrt (normSq φ)) < η/2 := by
      have hcont : ContinuousAt (fun t => |D.ρ' t| * (π * Real.sqrt (normSq φ))) (5/16 : ℝ) := by
        have := D.ρ'_continuous
        fun_prop
      have hval : |D.ρ' (5/16 : ℝ)| * (π * Real.sqrt (normSq φ)) < η/2 := by
        rw [ρ'_at_top D]
        simpa using (by linarith : (0:ℝ) < η/2)
      exact hcont (gt_mem_nhds hval)
    have h2 : ∀ᶠ t in nhds (5/16 : ℝ), ε * (D.Cη + 1) / 5 * |t - 5/16| < η/2 := by
      have hcont : ContinuousAt (fun t : ℝ => ε * (D.Cη + 1) / 5 * |t - 5/16|) (5/16 : ℝ) := by
        fun_prop
      have hval : ε * (D.Cη + 1) / 5 * |(5/16 : ℝ) - 5/16| < η/2 := by
        simpa using (by linarith : (0:ℝ) < η/2)
      exact hcont (gt_mem_nhds hval)
    filter_upwards [h1, h2] with t ha hb w w' hw
    have hwc := hw.continuous
    have hN : (0:ℝ) ≤ Real.sqrt (normSq w') := Real.sqrt_nonneg _
    have heq : (fun x => ut D ε t x - ut D ε (5/16 : ℝ) x) = ut D ε t := by
      funext x; rw [hut0 x]; ring
    rw [heq, inner_ut_eq D ε t hwc]
    refine (abs_add_le _ _).trans ?_
    have hA : |D.ρ' t * inner φ w|
        ≤ |D.ρ' t| * (π * Real.sqrt (normSq φ)) * Real.sqrt (normSq w') := by
      rw [abs_mul]
      have hcs : |inner φ w| ≤ Real.sqrt (normSq φ) * Real.sqrt (normSq w) :=
        abs_inner_le φ w continuous_φ hwc
      have hp : Real.sqrt (normSq w) ≤ π * Real.sqrt (normSq w') := sqrt_normSq_le_of_isTest hw
      have hkey : |inner φ w| ≤ (π * Real.sqrt (normSq φ)) * Real.sqrt (normSq w') := by
        calc |inner φ w| ≤ Real.sqrt (normSq φ) * Real.sqrt (normSq w) := hcs
          _ ≤ Real.sqrt (normSq φ) * (π * Real.sqrt (normSq w')) :=
              mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)
          _ = (π * Real.sqrt (normSq φ)) * Real.sqrt (normSq w') := by ring
      calc |D.ρ' t| * |inner φ w|
          ≤ |D.ρ' t| * ((π * Real.sqrt (normSq φ)) * Real.sqrt (normSq w')) :=
            mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
        _ = |D.ρ' t| * (π * Real.sqrt (normSq φ)) * Real.sqrt (normSq w') := by ring
    have hB := abs_inner_vt_le D hε0 t hw
    have hsum : (|D.ρ' t| * (π * Real.sqrt (normSq φ)) + ε * (D.Cη + 1) / 5 * |t - 5/16|)
        * Real.sqrt (normSq w') ≤ η * Real.sqrt (normSq w') :=
      mul_le_mul_of_nonneg_right (by linarith) hN
    have hexp : (|D.ρ' t| * (π * Real.sqrt (normSq φ)) + ε * (D.Cη + 1) / 5 * |t - 5/16|)
        * Real.sqrt (normSq w')
        = |D.ρ' t| * (π * Real.sqrt (normSq φ)) * Real.sqrt (normSq w')
          + ε * (D.Cη + 1) / 5 * |t - 5/16| * Real.sqrt (normSq w') := by ring
    linarith
  · have hgoal : ∀ᶠ t in nhds t₀, normSq (fun x => ut D ε t x - ut D ε t₀ x) ≤ (η/π)^2 := by
      refine eventually_normSq_sub_le (g := fun t x => ut D ε t x) ?_ ?_ (by positivity)
      · intro x; exact continuousAt_ut D ε ht₀ x
      · intro s; exact continuous_ut_x D ε s
    filter_upwards [hgoal] with t ht w w' hw
    have hwc := hw.continuous
    have hdc : Continuous fun x => ut D ε t x - ut D ε t₀ x := by
      have h1 := continuous_ut_x D ε t
      have h2 := continuous_ut_x D ε t₀
      fun_prop
    have hcs : |inner (fun x => ut D ε t x - ut D ε t₀ x) w|
        ≤ Real.sqrt (normSq (fun x => ut D ε t x - ut D ε t₀ x)) * Real.sqrt (normSq w) :=
      abs_inner_le _ w hdc hwc
    have h1 : Real.sqrt (normSq (fun x => ut D ε t x - ut D ε t₀ x)) ≤ η/π := by
      have hs := Real.sqrt_le_sqrt ht
      rwa [Real.sqrt_sq (by positivity)] at hs
    have h2 : Real.sqrt (normSq w) ≤ π * Real.sqrt (normSq w') := sqrt_normSq_le_of_isTest hw
    have h3 : Real.sqrt (normSq (fun x => ut D ε t x - ut D ε t₀ x)) * Real.sqrt (normSq w)
        ≤ (η/π) * (π * Real.sqrt (normSq w')) :=
      mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    have h4 : (η/π) * (π * Real.sqrt (normSq w')) = η * Real.sqrt (normSq w') := by
      field_simp
    linarith

/-! ## `t ↦ ⟨u(t), w⟩` is differentiable with derivative `⟨∂_t u(t), w⟩` -/

private lemma hasDerivAt_inner_u_block (ε : ℝ) {j : ℕ} {t : ℝ} (ht : t ∈ I j)
    {w : ℝ → ℝ} (hw : Continuous w) :
    HasDerivAt (fun s => inner (u D ε s) w) (inner (ut D ε t) w) t := by
  have heq : (fun s => inner (u D ε s) w) =ᶠ[nhds t]
      fun s => D.ρ s * inner φ w
        + ∑ m ∈ Finset.Icc 1 (M j), y D ε j m s * inner (p (K j m)) w := by
    filter_upwards [(isOpen_I j).mem_nhds ht] with s hs
    rw [inner_u_eq D ε s hw]
    have hv : v D ε s = vblock D ε j s := funext fun x => v_eq_block D ε hs x
    rw [hv, inner_vblock_eq D ε j s hw]
  have hd : HasDerivAt (fun s => D.ρ s * inner φ w
      + ∑ m ∈ Finset.Icc 1 (M j), y D ε j m s * inner (p (K j m)) w)
      (D.ρ' t * inner φ w + ∑ m ∈ Finset.Icc 1 (M j), y' D ε j m t * inner (p (K j m)) w) t :=
    ((D.ρ_hasDerivAt t).mul_const _).add
      (HasDerivAt.fun_sum fun m _ => (hasDerivAt_y D ε j m t).mul_const _)
  have hval : inner (ut D ε t) w
      = D.ρ' t * inner φ w + ∑ m ∈ Finset.Icc 1 (M j), y' D ε j m t * inner (p (K j m)) w := by
    rw [inner_ut_eq D ε t hw]
    have hvt : vt D ε t = vtblock D ε j t := funext fun x => vt_eq_block D ε ht x
    rw [hvt, inner_vtblock_eq D ε j t hw]
  rw [hval]
  exact hd.congr_of_eventuallyEq heq

private lemma hasDerivAt_inner_u_free (ε : ℝ) {t : ℝ}
    (hev : ∀ᶠ s in nhds t, ∀ i, ηj D i s = 0 ∧ ηj' D i s = 0)
    {w : ℝ → ℝ} (hw : Continuous w) :
    HasDerivAt (fun s => inner (u D ε s) w) (inner (ut D ε t) w) t := by
  have heq : (fun s => inner (u D ε s) w) =ᶠ[nhds t] fun s => D.ρ s * inner φ w := by
    filter_upwards [hev] with s hs
    rw [inner_u_eq D ε s hw]
    have hv : v D ε s = fun _ => (0:ℝ) := by
      funext x
      exact finsum_eq_zero_of_forall_eq_zero fun i => vblock_eq_zero_of_ηj D ε (hs i).1 x
    rw [hv, inner_zero_left, add_zero]
  have hval : inner (ut D ε t) w = D.ρ' t * inner φ w := by
    rw [inner_ut_eq D ε t hw]
    have hvt : vt D ε t = fun _ => (0:ℝ) := by
      funext x
      exact finsum_eq_zero_of_forall_eq_zero fun i =>
        vtblock_eq_zero_of_ηj D ε (hev.self_of_nhds i).1 (hev.self_of_nhds i).2 x
    rw [hvt, inner_zero_left, add_zero]
  rw [hval]
  exact ((D.ρ_hasDerivAt t).mul_const _).congr_of_eventuallyEq heq

private lemma hasDerivAt_inner_u_top {ε : ℝ} (hε0 : 0 ≤ ε) {w w' : ℝ → ℝ} (hw : IsTest w w') :
    HasDerivAt (fun s => inner (u D ε s) w) (inner (ut D ε (5/16 : ℝ)) w) (5/16 : ℝ) := by
  have hwc := hw.continuous
  have hut : inner (ut D ε (5/16 : ℝ)) w = 0 := by
    rw [show ut D ε (5/16 : ℝ) = fun _ => (0:ℝ) from ut_at_top D ε, inner_zero_left]
  rw [hut]
  have hF1 : HasDerivAt (fun s => D.ρ s * inner φ w) 0 (5/16 : ℝ) := by
    have h := (D.ρ_hasDerivAt (5/16 : ℝ)).mul_const (inner φ w)
    rwa [ρ'_at_top D, zero_mul] at h
  have hv0 : inner (v D ε (5/16 : ℝ)) w = 0 := by
    have h : v D ε (5/16 : ℝ) = fun _ => (0:ℝ) := funext fun x =>
      v_eq_zero D ε (fun j => five_sixteenths_notMem_I j) x
    rw [h, inner_zero_left]
  have hC : ∀ s : ℝ, |inner (v D ε s) w|
      ≤ (Real.sqrt π * ε * Real.sqrt (normSq w)) * |s - 5/16| ^ 2 := by
    intro s
    have hvc : Continuous (v D ε s) := cont_slice (continuous_v D ε) s
    have h1 : |inner (v D ε s) w| ≤ Real.sqrt (normSq (v D ε s)) * Real.sqrt (normSq w) :=
      abs_inner_le _ w hvc hwc
    have h2 : normSq (v D ε s) ≤ π * (ε * |s - 5/16| ^ 2) ^ 2 := by
      refine normSq_le_of_bound hvc (mul_nonneg hε0 (sq_nonneg _)) ?_
      intro x _
      exact abs_v_le_dist D hε0 s x
    have h3 : Real.sqrt (normSq (v D ε s)) ≤ Real.sqrt π * (ε * |s - 5/16| ^ 2) := by
      have h := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq (mul_nonneg hε0 (sq_nonneg _))] at h
    calc |inner (v D ε s) w| ≤ Real.sqrt (normSq (v D ε s)) * Real.sqrt (normSq w) := h1
      _ ≤ (Real.sqrt π * (ε * |s - 5/16| ^ 2)) * Real.sqrt (normSq w) :=
          mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
      _ = (Real.sqrt π * ε * Real.sqrt (normSq w)) * |s - 5/16| ^ 2 := by ring
  have hF2 : HasDerivAt (fun s => inner (v D ε s) w) 0 (5/16 : ℝ) := by
    rw [hasDerivAt_iff_isLittleO]
    simp only [hv0, smul_zero, sub_zero]
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hC0 : (0:ℝ) ≤ Real.sqrt π * ε * Real.sqrt (normSq w) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hε0) (Real.sqrt_nonneg _)
    have hpos : (0:ℝ) < c / (Real.sqrt π * ε * Real.sqrt (normSq w) + 1) := by positivity
    filter_upwards [Metric.ball_mem_nhds (5/16 : ℝ) hpos] with s hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := hC s
    have h2 : |s - 5/16| < c / (Real.sqrt π * ε * Real.sqrt (normSq w) + 1) := by
      have h := Metric.mem_ball.mp hs
      rwa [Real.dist_eq] at h
    have hd := abs_nonneg (s - 5/16)
    have hB : (Real.sqrt π * ε * Real.sqrt (normSq w))
        * (c / (Real.sqrt π * ε * Real.sqrt (normSq w) + 1)) ≤ c := by
      rw [mul_div_assoc',
        div_le_iff₀ (by linarith : (0:ℝ) < Real.sqrt π * ε * Real.sqrt (normSq w) + 1)]
      nlinarith
    have hstep1 : (Real.sqrt π * ε * Real.sqrt (normSq w)) * |s - 5/16|
        ≤ (Real.sqrt π * ε * Real.sqrt (normSq w))
          * (c / (Real.sqrt π * ε * Real.sqrt (normSq w) + 1)) :=
      mul_le_mul_of_nonneg_left h2.le hC0
    have hstep2 : ((Real.sqrt π * ε * Real.sqrt (normSq w)) * |s - 5/16|) * |s - 5/16|
        ≤ ((Real.sqrt π * ε * Real.sqrt (normSq w))
          * (c / (Real.sqrt π * ε * Real.sqrt (normSq w) + 1))) * |s - 5/16| :=
      mul_le_mul_of_nonneg_right hstep1 hd
    have hstep3 : ((Real.sqrt π * ε * Real.sqrt (normSq w))
        * (c / (Real.sqrt π * ε * Real.sqrt (normSq w) + 1))) * |s - 5/16| ≤ c * |s - 5/16| :=
      mul_le_mul_of_nonneg_right hB hd
    have hexp : (Real.sqrt π * ε * Real.sqrt (normSq w)) * |s - 5/16| ^ 2
        = ((Real.sqrt π * ε * Real.sqrt (normSq w)) * |s - 5/16|) * |s - 5/16| := by ring
    linarith [h1, hstep2, hstep3, hexp]
  have hsum := hF1.add hF2
  rw [add_zero] at hsum
  exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => inner_u_eq D ε s hwc)

/-- `t ↦ ⟨u(t), w⟩` is differentiable with derivative `⟨∂_t u(t), w⟩`, for every `t`. -/
theorem hasDerivAt_inner_u {ε : ℝ} (hε0 : 0 ≤ ε) (t : ℝ) {w w' : ℝ → ℝ} (hw : IsTest w w') :
    HasDerivAt (fun t => inner (u D ε t) w) (inner (ut D ε t) w) t := by
  have hwc := hw.continuous
  rcases mem_block_or_not t with ⟨j, htj⟩ | hno
  · exact hasDerivAt_inner_u_block D ε htj hwc
  · by_cases hIcc : t ∈ Set.Icc (1/4 : ℝ) (5/16)
    · by_cases htop : t = 5/16
      · subst htop; exact hasDerivAt_inner_u_top D hε0 hw
      · obtain ⟨j, hj1, hjt⟩ := exists_eq_τ hIcc.1 (lt_of_le_of_ne hIcc.2 htop) hno
        subst hjt
        exact hasDerivAt_inner_u_free D ε (eventually_ηj_zero_at_τ D hj1) hwc
    · exact hasDerivAt_inner_u_free D ε (eventually_ηj_zero_outside D hIcc) hwc

/-- `s ↦ ⟨∂_t u(s), w⟩` is continuous. -/
theorem continuous_inner_ut {ε : ℝ} (hε0 : 0 ≤ ε) {w w' : ℝ → ℝ} (hw : IsTest w w') :
    Continuous (fun s => inner (ut D ε s) w) := by
  have hwc := hw.continuous
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro θ hθ
  have hN : (0:ℝ) ≤ Real.sqrt (normSq w') := Real.sqrt_nonneg _
  filter_upwards [ut_tendsto_V' D hε0 t₀
    (show (0:ℝ) < θ / (Real.sqrt (normSq w') + 1) by positivity)] with t ht
  have h1 := ht w w' hw
  have h2 : inner (fun x => ut D ε t x - ut D ε t₀ x) w
      = inner (ut D ε t) w - inner (ut D ε t₀) w :=
    inner_sub_left' (continuous_ut_x D ε t) (continuous_ut_x D ε t₀) hwc
  rw [h2] at h1
  rw [Real.dist_eq]
  have h3 : θ / (Real.sqrt (normSq w') + 1) * Real.sqrt (normSq w') < θ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0:ℝ) < Real.sqrt (normSq w') + 1)]
    nlinarith
  linarith

/-- `u ∈ C¹([0,1];V')`. -/
theorem u_hasDerivAt_V' {ε : ℝ} (hε0 : 0 ≤ ε) (t₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in nhds t₀, ∀ w w' : ℝ → ℝ, IsTest w w' →
      |inner (fun x => u D ε t x - u D ε t₀ x - (t - t₀) * ut D ε t₀ x) w|
        ≤ η * |t - t₀| * Real.sqrt (normSq w') := by
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp (ut_tendsto_V' D hε0 t₀ hη)
  filter_upwards [Metric.ball_mem_nhds t₀ hδ0] with t hts
  intro w w' hw
  have hwc := hw.continuous
  have hN : (0:ℝ) ≤ Real.sqrt (normSq w') := Real.sqrt_nonneg _
  have hcont := continuous_inner_ut D hε0 hw
  -- linearity of the pairing
  have hlin : inner (fun x => u D ε t x - u D ε t₀ x - (t - t₀) * ut D ε t₀ x) w
      = (inner (u D ε t) w - inner (u D ε t₀) w) - (t - t₀) * inner (ut D ε t₀) w := by
    have hA : Continuous fun x => u D ε t x - u D ε t₀ x := by
      have h1 := cont_slice (continuous_u D ε) t
      have h2 := cont_slice (continuous_u D ε) t₀
      fun_prop
    have hB : Continuous fun x => (t - t₀) * ut D ε t₀ x := by
      have h2 := continuous_ut_x D ε t₀
      fun_prop
    rw [inner_sub_left' hA hB hwc,
      inner_sub_left' (cont_slice (continuous_u D ε) t) (cont_slice (continuous_u D ε) t₀) hwc,
      inner_smul_left']
  -- fundamental theorem of calculus
  have hii : IntervalIntegrable (fun s => inner (ut D ε s) w) MeasureTheory.volume t₀ t :=
    hcont.intervalIntegrable t₀ t
  have hFTC : ∫ s in t₀..t, inner (ut D ε s) w = inner (u D ε t) w - inner (u D ε t₀) w :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_inner_u D hε0 s hw) hii
  have hFTC2 : ∫ s in t₀..t, (inner (ut D ε s) w - inner (ut D ε t₀) w)
      = (inner (u D ε t) w - inner (u D ε t₀) w) - (t - t₀) * inner (ut D ε t₀) w := by
    rw [intervalIntegral.integral_sub hii intervalIntegrable_const, hFTC,
      intervalIntegral.integral_const, smul_eq_mul]
  -- uniform bound on the integrand
  have hbound : ∀ s ∈ Set.uIoc t₀ t, ‖inner (ut D ε s) w - inner (ut D ε t₀) w‖
      ≤ η * Real.sqrt (normSq w') := by
    intro s hs
    have hmem : s ∈ Set.uIcc t₀ t := Set.uIoc_subset_uIcc hs
    have hts' : |t - t₀| < δ := by
      have h := Metric.mem_ball.mp hts
      rwa [Real.dist_eq] at h
    have key : |s - t₀| ≤ |t - t₀| := by
      rcases Set.mem_uIcc.mp hmem with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
    have hsd : dist s t₀ < δ := by rw [Real.dist_eq]; linarith
    have h1 := hδ hsd w w' hw
    have h2 : inner (fun x => ut D ε s x - ut D ε t₀ x) w
        = inner (ut D ε s) w - inner (ut D ε t₀) w :=
      inner_sub_left' (continuous_ut_x D ε s) (continuous_ut_x D ε t₀) hwc
    rw [h2] at h1
    rwa [Real.norm_eq_abs]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [hFTC2, Real.norm_eq_abs] at hnorm
  rw [hlin]
  calc |inner (u D ε t) w - inner (u D ε t₀) w - (t - t₀) * inner (ut D ε t₀) w|
      ≤ η * Real.sqrt (normSq w') * |t - t₀| := hnorm
    _ = η * |t - t₀| * Real.sqrt (normSq w') := by ring

end LionsC12

end
