module

public import LionsC12.Interval.Dual

/-!
# Lemma 4.1 in the paper's spaces: `u ∈ C([0,1];V) ∩ C¹([0,1];V') ∩ W^{1,1}(0,1;H)`

The candidate solution `u` of `LionsC12.Construction.Defs` as a curve in
`V = H¹₀((0,π);ℂ)` (`uV`), with

* `continuous_uV` — `u ∈ C(ℝ;V)`;
* `hasDerivAt_ofH10_uV`, `continuous_uV'` — `t ↦ u(t) ∈ V'` is differentiable at every `t` with
  derivative `u'(t) = ∂ₜu(t) ∈ H ⊂ V'`, and `u'` is continuous: `u ∈ C¹(ℝ;V')`;
* `hasDerivAt_val_uV` — `t ↦ u(t) ∈ H` is differentiable at every `t ≠ 5/16` with derivative
  `∂ₜu(t)`, and `hasWeakDeriv_val_uV` — `∂ₜu ∈ L¹(0,1;H)` is the distributional derivative of
  `u` in `H`: `u ∈ W^{1,1}(0,1;H)`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped InnerProductSpace ComplexConjugate

variable (D : Cutoffs)

/-! ### `L²(0,π)`-linear algebra -/

theorem ofL2_sub' (h₁ h₂ : L2 Iπ) : ofL2 Iπ (h₁ - h₂) = ofL2 Iπ h₁ - ofL2 Iπ h₂ :=
  (ofHL (val Iπ)).map_sub h₁ h₂

theorem ofL2_add' (h₁ h₂ : L2 Iπ) : ofL2 Iπ (h₁ + h₂) = ofL2 Iπ h₁ + ofL2 Iπ h₂ :=
  (ofHL (val Iπ)).map_add h₁ h₂

theorem ofL2_real_smul (r : ℝ) (h : L2 Iπ) : ofL2 Iπ (r • h) = r • ofL2 Iπ h := by
  ext z
  simp only [ofL2, ContinuousLinearMap.coe_comp, Function.comp_apply, innerSLFlip_apply_apply,
    smul_apply]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r h, inner_smul_right, RCLike.real_smul_eq_coe_smul
    (K := ℂ), smul_eq_mul]

theorem toL2c_real_smul (c : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    toL2c (fun x => c * g x) (continuous_const.mul hg) = c • toL2c g hg := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c (toL2c g hg)]
  exact toL2c_smul c hg

theorem toL2c_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) {g : ι → ℝ → ℝ}
    (hg : ∀ i, Continuous (g i)) :
    toL2c (fun x => ∑ i ∈ s, c i * g i x)
        (continuous_finsetSum _ fun i _ => continuous_const.mul (hg i))
      = ∑ i ∈ s, c i • toL2c (g i) (hg i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using toL2c_zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have := toL2c_add (g := fun x => c i * g i x) (h := fun x => ∑ i ∈ s, c i * g i x)
      (continuous_const.mul (hg i))
      (continuous_finsetSum s fun i _ => continuous_const.mul (hg i))
    rw [this, toL2c_real_smul, ih]

/-! ### The solution in `V` -/

theorem isC1Vanish_u (ε t : ℝ) : IsC1Vanish (u D ε t) (ux D ε t) where
  hasDerivAt x := hasDerivAt_u_x D ε t x
  cont' := continuous_ux_x D ε t
  zero_left := u_zero_left D ε t
  zero_right := u_zero_right D ε t
  zero_left' := ux_zero_left D ε t
  zero_right' := ux_zero_right D ε t

/-- The candidate solution `u(t) ∈ V = H¹₀((0,π);ℂ)`. -/
def uV (ε t : ℝ) : H10 Iπ := ofC1Z (isC1Vanish_u D ε t)

theorem val_uV (ε t : ℝ) : val Iπ (uV D ε t) = toL2c (u D ε t) (continuous_u_x D ε t) :=
  val_ofC1Z _

theorem dx_uV (ε t : ℝ) : dx Iπ (uV D ε t) = toL2c (ux D ε t) (continuous_ux_x D ε t) :=
  dx_ofC1Z _

theorem uV_zero (ε : ℝ) : uV D ε 0 = 0 := by
  apply H10.ext
  have h1 : val Iπ (uV D ε 0) = 0 := by
    rw [val_uV, toL2c_congr _ continuous_const fun x _ => u_initial D ε x, toL2c_zero]
  have h2 : dx Iπ (uV D ε 0) = 0 := by
    rw [dx_uV, toL2c_congr _ continuous_const fun x _ => ?_, toL2c_zero]
    have : (fun x => u D ε 0 x) = fun _ => 0 := funext fun x => u_initial D ε x
    have hd := hasDerivAt_u_x D ε 0 x
    rw [this] at hd
    exact hd.unique (hasDerivAt_const x 0)
  have e : H10.pair (uV D ε 0) = WithLp.toLp 2 (val Iπ (uV D ε 0), dx Iπ (uV D ε 0)) := rfl
  rw [e, h1, h2]
  rfl

theorem norm_uV_sub_sq (ε s t : ℝ) :
    ‖uV D ε s - uV D ε t‖ ^ 2
      = normSq (fun x => u D ε s x - u D ε t x) + normSq (fun x => ux D ε s x - ux D ε t x) := by
  rw [norm_sq_H10, map_sub, map_sub, val_uV, val_uV, dx_uV, dx_uV, ← toL2c_sub, ← toL2c_sub,
    norm_toL2c_sq, norm_toL2c_sq]

/-- `u ∈ C(ℝ;V)`. -/
theorem continuous_uV (ε : ℝ) : Continuous (uV D ε) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h := ((u_tendsto_H D ε t).add (u_tendsto_V D ε t)).sqrt
  simp only [add_zero, Real.sqrt_zero] at h
  refine h.congr fun s => ?_
  rw [← norm_uV_sub_sq, Real.sqrt_sq (norm_nonneg _)]

/-! ### `u ∈ C¹(ℝ;V')` -/

/-- The derivative `u'(t) = ∂ₜu(t) ∈ H ⊂ V'`. -/
def uV' (ε t : ℝ) : Hm1 Iπ := ofL2 Iπ (toL2c (ut D ε t) (continuous_ut_x D ε t))

theorem ofH10_uV (ε t : ℝ) :
    ofH10 Iπ (uV D ε t) = ofL2 Iπ (toL2c (u D ε t) (continuous_u_x D ε t)) := by
  rw [ofH10, val_uV]

/-- `t ↦ u(t) ∈ V'` is differentiable with derivative `∂ₜu(t)`. -/
theorem hasDerivAt_ofH10_uV {ε : ℝ} (hε0 : 0 ≤ ε) (t : ℝ) :
    HasDerivAt (fun s => ofH10 Iπ (uV D ε s)) (uV' D ε t) t := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hev := u_hasDerivAt_V' D hε0 t (η := c / 2) (by positivity)
  filter_upwards [hev] with s hs
  have hcs : Continuous fun x => u D ε s x - u D ε t x - (s - t) * ut D ε t x :=
    ((continuous_u_x D ε s).sub (continuous_u_x D ε t)).sub
      (continuous_const.mul (continuous_ut_x D ε t))
  have key : ofH10 Iπ (uV D ε s) - ofH10 Iπ (uV D ε t) - (s - t) • uV' D ε t
      = ofL2 Iπ (toL2c _ hcs) := by
    rw [ofH10_uV, ofH10_uV, uV', ← ofL2_real_smul, ← ofL2_sub', ← ofL2_sub', ← toL2c_sub,
      ← toL2c_real_smul, ← toL2c_sub]
  rw [key, Real.norm_eq_abs]
  have := norm_ofL2_toL2c_le hcs (C := c / 2 * |s - t|) (by positivity) (fun w w' hw => by
    have := hs w w' hw
    simpa [mul_comm, mul_left_comm, mul_assoc] using this)
  calc _ ≤ 2 * (c / 2 * |s - t|) := this
    _ = c * |s - t| := by ring

theorem continuous_uV' {ε : ℝ} (hε0 : 0 ≤ ε) : Continuous (uV' D ε) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro c hc
  have hev := ut_tendsto_V' D hε0 t (η := c / 4) (by positivity)
  filter_upwards [hev] with s hs
  have hcs : Continuous fun x => ut D ε s x - ut D ε t x :=
    (continuous_ut_x D ε s).sub (continuous_ut_x D ε t)
  rw [dist_eq_norm, uV', uV', ← ofL2_sub', ← toL2c_sub]
  have := norm_ofL2_toL2c_le hcs (C := c / 4) (by positivity) hs
  linarith

/-! ### `u ∈ W^{1,1}(0,1;H)` -/

/-- The derivative `∂ₜu(t) ∈ H`. -/
def utH (ε t : ℝ) : L2 Iπ := toL2c (ut D ε t) (continuous_ut_x D ε t)

theorem norm_utH (ε t : ℝ) : ‖utH D ε t‖ = Real.sqrt (utNormSq D ε t) := norm_toL2c _

theorem v_eq_block_of_cutoffs (ε : ℝ) {j : ℕ} {t : ℝ}
    (h : ∀ i, i ≠ j → ηj D i t = 0 ∧ ηj' D i t = 0) (x : ℝ) : v D ε t x = vblock D ε j t x :=
  v_eq_block' D ε (fun i hi => (h i hi).1) x

/-- Away from the accumulation time `5/16`, `u` is locally a finite combination of fixed modes:
`u(t) = ρ(t) φ + ∑_m y_{j,m}(t) p_{K_{j,m}}` in `H`. -/
theorem val_uV_local (ε : ℝ) {j : ℕ} {t : ℝ} (h : ∀ i, i ≠ j → ηj D i t = 0 ∧ ηj' D i t = 0) :
    val Iπ (uV D ε t) = D.ρ t • toL2c φ continuous_φ
      + ∑ m ∈ Finset.Icc 1 (M j), y D ε j m t • toL2c (p (K j m)) (continuous_p _) := by
  rw [val_uV, ← toL2c_real_smul, ← toL2c_sum, ← toL2c_add]
  refine toL2c_congr _ _ fun x _ => ?_
  simp only [u, v_eq_block_of_cutoffs D ε h x, vblock]

theorem utH_local (ε : ℝ) {j : ℕ} {t : ℝ} (h : ∀ i, i ≠ j → ηj D i t = 0 ∧ ηj' D i t = 0) :
    utH D ε t = D.ρ' t • toL2c φ continuous_φ
      + ∑ m ∈ Finset.Icc 1 (M j), y' D ε j m t • toL2c (p (K j m)) (continuous_p _) := by
  rw [utH, ← toL2c_real_smul, ← toL2c_sum, ← toL2c_add]
  refine toL2c_congr _ _ fun x _ => ?_
  simp only [ut, vt_eq_block' D ε h x, vtblock]

/-- `t ↦ u(t) ∈ H` is differentiable at every `t ≠ 5/16`, with derivative `∂ₜu(t)`. -/
theorem hasDerivAt_val_uV (ε : ℝ) {t : ℝ} (ht : t ≠ 5 / 16) :
    HasDerivAt (fun s => val Iπ (uV D ε s)) (utH D ε t) t := by
  obtain ⟨j, hj⟩ := exists_eventually_single_block D t ht
  have hG : HasDerivAt (fun s => D.ρ s • toL2c φ continuous_φ
      + ∑ m ∈ Finset.Icc 1 (M j), y D ε j m s • toL2c (p (K j m)) (continuous_p _))
      (D.ρ' t • toL2c φ continuous_φ
        + ∑ m ∈ Finset.Icc 1 (M j), y' D ε j m t • toL2c (p (K j m)) (continuous_p _)) t := by
    refine ((D.ρ_hasDerivAt t).smul_const _).add (HasDerivAt.fun_sum fun m _ => ?_)
    exact (hasDerivAt_y D ε j m t).smul_const _
  rw [← utH_local D ε hj.self_of_nhds] at hG
  exact hG.congr_of_eventuallyEq (hj.mono fun s hs => val_uV_local D ε hs)

theorem continuousAt_utH (ε : ℝ) {t : ℝ} (ht : t ≠ 5 / 16) : ContinuousAt (utH D ε) t := by
  obtain ⟨j, hj⟩ := exists_eventually_single_block D t ht
  have hG : Continuous fun s => D.ρ' s • toL2c φ continuous_φ
      + ∑ m ∈ Finset.Icc 1 (M j), y' D ε j m s • toL2c (p (K j m)) (continuous_p _) :=
    (D.ρ'_continuous.smul continuous_const).add
      (continuous_finsetSum _ fun m _ => (continuous_y' D ε j m).smul continuous_const)
  exact (hG.continuousAt).congr (hj.mono fun s hs => (utH_local D ε hs).symm)

theorem aestronglyMeasurable_utH (ε : ℝ) :
    AEStronglyMeasurable (utH D ε) (volume.restrict (Ioo 0 1)) := by
  have hcont : ContinuousOn (utH D ε) {(5 / 16 : ℝ)}ᶜ := fun t ht =>
    (continuousAt_utH D ε ht).continuousWithinAt
  have h1 : AEStronglyMeasurable (utH D ε) (volume.restrict {(5 / 16 : ℝ)}ᶜ) :=
    hcont.aestronglyMeasurable (measurableSet_singleton _).compl
  rw [restrict_compl_singleton] at h1
  exact h1.restrict

/-- `∂ₜu ∈ L¹(0,1;H)`. -/
theorem integrableOn_utH {ε : ℝ} (hε0 : 0 ≤ ε) : IntegrableOn (utH D ε) (Ioo 0 1) := by
  have hint := (integrableOn_sqrt_utNormSq D hε0).mono_set Ioo_subset_Icc_self
  refine Integrable.mono' hint (aestronglyMeasurable_utH D ε) (Eventually.of_forall fun t => ?_)
  rw [norm_utH]

/-- `u ∈ W^{1,1}(0,1;H)`: the distributional derivative of `t ↦ u(t) ∈ H` on `(0,1)` is
`∂ₜu ∈ L¹(0,1;H)`. -/
theorem hasWeakDeriv_val_uV {ε : ℝ} (hε0 : 0 ≤ ε) :
    HasWeakDeriv (fun t => val Iπ (uV D ε t)) (utH D ε) :=
  hasWeakDeriv_of_hasDerivAt_off_countable (Set.countable_singleton (5 / 16 : ℝ))
    ((val Iπ).continuous.comp (continuous_uV D ε)).continuousOn
    (fun _ ht => hasDerivAt_val_uV D ε ht.2) (integrableOn_utH D hε0)

end LionsC12
