module

public import LionsC12.Interval.Theorem

/-!
# The remark on the growth of the maximal-regularity constant, in the paper's spaces

The remark after the proof of Theorem 1.1: truncate the construction after `N` blocks,
`𝔞_N = 1 + ε ∑_{j ≤ N} β_j`, `u_N = ρφ + ∑_{j ≤ N} v_j`, `f_N = ∂ₜu_N + 𝒜_N(t)u_N`
(`LionsC12.Forcing.Truncation`).  In `H = L²((0,π);ℂ)`, `V = H¹₀((0,π);ℂ)`:

* `isLionsSolution_uNV` — `u_N` is the (unique) Lions solution of `w' + 𝒜_N(t)w = f_N`,
  `w(0) = 0`, and it has maximal regularity: `∂ₜu_N, A_{N,H}u_N ∈ C([0,1];H) ⊂ L²(0,1;H)`;
* the bounds uniform in `N`: `‖𝔞_N - 1‖_{C^{0,1/2}([0,1];L^∞)} ≤ ε/480 + 2εC_β` and
  `‖f_N‖²_{L²(0,1;H)} ≤ π C_f²`, while `‖∂ₜu_N‖²_{L²(0,1;H)} ≥ (πε²/1536)(log(N+2) - 1)`;
* `IsMaxRegConstant 𝔞 C` — `C` is a maximal-regularity constant for `𝔞`:
  `‖∂ₜw‖_{L²(H)} + ‖A_H w‖_{L²(H)} ≤ C ‖g‖_{L²(H)}` for every Lions solution `w` with zero
  initial value, forcing `g ∈ L²(0,1;H)` and `∂ₜw, A_H w ∈ L²(0,1;H)`;
* `maxRegConstant_growth` — every such constant for `𝔞_N` satisfies
  `C √π C_f ≥ √((πε²/1536)(log(N+2) - 1))`, i.e. `C_N ≳ ε √(log N)`.

That the truncated problems do have a finite maximal-regularity constant (Lions' theorem for
`C¹` families, invoked in the paper) is `LionsC12.truncation_maximal_regularity`, and the
combined statement (existence and the lower bound) is `LionsC12.truncation_maxReg_growth`, both
in `LionsC12.Interval.MaxReg`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped InnerProductSpace ComplexConjugate ENNReal

variable (D : Cutoffs)

/-! ### The truncated solution in `V` -/

theorem uxN_zero_left (N : ℕ) (ε t : ℝ) : uxN D N ε t 0 = 0 := by
  simp [uxN, vxblock, p'_zero, φ'_zero]

theorem uxN_zero_right (N : ℕ) (ε t : ℝ) : uxN D N ε t π = 0 := by
  simp [uxN, vxblock, p'_pi, φ'_pi]

theorem continuous_uxN_x (N : ℕ) (ε t : ℝ) : Continuous fun x => uxN D N ε t x :=
  Continuous.uncurry_left (f := uxN D N ε) t (continuous_uxN D N ε)

theorem continuous_uN (N : ℕ) (ε : ℝ) : Continuous (fun q : ℝ × ℝ => uN D N ε q.1 q.2) := by
  have h1 : Continuous D.ρ := continuous_iff_continuousAt.2 fun t => (D.ρ_hasDerivAt t).continuousAt
  have h2 : Continuous fun q : ℝ × ℝ => ∑ j ∈ Finset.range (N + 1), vblock D ε j q.1 q.2 :=
    continuous_finsetSum _ fun j _ => continuous_vblock D ε j
  exact (h1.comp continuous_fst).mul (continuous_φ.comp continuous_snd) |>.add h2

theorem continuous_uN_x (N : ℕ) (ε t : ℝ) : Continuous fun x => uN D N ε t x :=
  Continuous.uncurry_left (f := uN D N ε) t (continuous_uN D N ε)

theorem isC1Vanish_uN (N : ℕ) (ε t : ℝ) : IsC1Vanish (uN D N ε t) (uxN D N ε t) where
  hasDerivAt x := hasDerivAt_uN_x D N ε t x
  cont' := continuous_uxN_x D N ε t
  zero_left := uN_zero_left D N ε t
  zero_right := uN_zero_right D N ε t
  zero_left' := uxN_zero_left D N ε t
  zero_right' := uxN_zero_right D N ε t

/-- The truncated solution `u_N(t) ∈ V`. -/
def uNV (N : ℕ) (ε t : ℝ) : H10 Iπ := ofC1Z (isC1Vanish_uN D N ε t)

theorem val_uNV (N : ℕ) (ε t : ℝ) :
    val Iπ (uNV D N ε t) = toL2c (uN D N ε t) (continuous_uN_x D N ε t) := val_ofC1Z _

theorem dx_uNV (N : ℕ) (ε t : ℝ) :
    dx Iπ (uNV D N ε t) = toL2c (uxN D N ε t) (continuous_uxN_x D N ε t) := dx_ofC1Z _

theorem continuous_uNV (N : ℕ) (ε : ℝ) : Continuous (uNV D N ε) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h := ((tendsto_normSq_sub_of_continuous _ (continuous_uN D N ε) t).add
    (tendsto_normSq_sub_of_continuous _ (continuous_uxN D N ε) t)).sqrt
  simp only [add_zero, Real.sqrt_zero] at h
  refine h.congr fun s => ?_
  rw [← Real.sqrt_sq (norm_nonneg (uNV D N ε s - uNV D N ε t)), norm_sq_H10, map_sub, map_sub,
    val_uNV, val_uNV, dx_uNV, dx_uNV, ← toL2c_sub, ← toL2c_sub, norm_toL2c_sq, norm_toL2c_sq]

theorem uNV_zero (N : ℕ) (ε : ℝ) : uNV D N ε 0 = 0 := by
  apply H10.ext
  have h1 : val Iπ (uNV D N ε 0) = 0 := by
    rw [val_uNV, toL2c_congr _ continuous_const fun x _ => uN_initial D N ε x, toL2c_zero]
  have h2 : dx Iπ (uNV D N ε 0) = 0 := by
    rw [dx_uNV, toL2c_congr _ continuous_const fun x _ => ?_, toL2c_zero]
    have : (fun x => uN D N ε 0 x) = fun _ => 0 := funext fun x => uN_initial D N ε x
    have hd := hasDerivAt_uN_x D N ε 0 x
    rw [this] at hd
    exact hd.unique (hasDerivAt_const x 0)
  have e : H10.pair (uNV D N ε 0) = WithLp.toLp 2 (val Iπ (uNV D N ε 0), dx Iπ (uNV D N ε 0)) :=
    rfl
  rw [e, h1, h2]
  rfl

/-! ### Time derivative: `u_N ∈ C¹([0,1];H)` -/

/-- `∂ₜu_N(t) ∈ H`. -/
def utNH (N : ℕ) (ε t : ℝ) : L2 Iπ := toL2c (utN D N ε t) (continuous_utN_x D N ε t)

theorem toL2c_finsetSum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ} (hF : ∀ i, Continuous (F i)) :
    toL2c (fun x => ∑ i ∈ s, F i x) (continuous_finsetSum _ fun i _ => hF i)
      = ∑ i ∈ s, toL2c (F i) (hF i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using toL2c_zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have := toL2c_add (g := F i) (h := fun x => ∑ i ∈ s, F i x) (hF i)
      (continuous_finsetSum s fun i _ => hF i)
    rw [this, ih]

theorem continuous_vblock_x (ε : ℝ) (j : ℕ) (t : ℝ) : Continuous fun x => vblock D ε j t x :=
  Continuous.uncurry_left (f := vblock D ε j) t (continuous_vblock D ε j)

theorem toL2c_vblock (ε : ℝ) (j : ℕ) (t : ℝ) :
    toL2c (vblock D ε j t) (continuous_vblock_x D ε j t)
      = ∑ m ∈ Finset.Icc 1 (M j), y D ε j m t • toL2c (p (K j m)) (continuous_p _) := by
  rw [← toL2c_sum]
  rfl

theorem toL2c_vtblock (ε : ℝ) (j : ℕ) (t : ℝ) :
    toL2c (vtblock D ε j t) (continuous_vtblock_x D ε j t)
      = ∑ m ∈ Finset.Icc 1 (M j), y' D ε j m t • toL2c (p (K j m)) (continuous_p _) := by
  rw [← toL2c_sum]
  rfl

theorem val_uNV_eq (N : ℕ) (ε t : ℝ) :
    val Iπ (uNV D N ε t) = D.ρ t • toL2c φ continuous_φ
      + ∑ j ∈ Finset.range (N + 1), ∑ m ∈ Finset.Icc 1 (M j),
          y D ε j m t • toL2c (p (K j m)) (continuous_p _) := by
  rw [val_uNV, ← toL2c_real_smul]
  simp_rw [← toL2c_vblock]
  rw [← toL2c_finsetSum, ← toL2c_add]
  rfl

theorem utNH_eq (N : ℕ) (ε t : ℝ) :
    utNH D N ε t = D.ρ' t • toL2c φ continuous_φ
      + ∑ j ∈ Finset.range (N + 1), ∑ m ∈ Finset.Icc 1 (M j),
          y' D ε j m t • toL2c (p (K j m)) (continuous_p _) := by
  rw [utNH, ← toL2c_real_smul]
  simp_rw [← toL2c_vtblock]
  rw [← toL2c_finsetSum, ← toL2c_add]
  rfl

theorem hasDerivAt_val_uNV (N : ℕ) (ε t : ℝ) :
    HasDerivAt (fun s => val Iπ (uNV D N ε s)) (utNH D N ε t) t := by
  have hG : HasDerivAt (fun s => D.ρ s • toL2c φ continuous_φ
      + ∑ j ∈ Finset.range (N + 1), ∑ m ∈ Finset.Icc 1 (M j),
          y D ε j m s • toL2c (p (K j m)) (continuous_p _))
      (D.ρ' t • toL2c φ continuous_φ
      + ∑ j ∈ Finset.range (N + 1), ∑ m ∈ Finset.Icc 1 (M j),
          y' D ε j m t • toL2c (p (K j m)) (continuous_p _)) t := by
    refine ((D.ρ_hasDerivAt t).smul_const _).add (HasDerivAt.fun_sum fun j _ =>
      HasDerivAt.fun_sum fun m _ => ?_)
    exact (hasDerivAt_y D ε j m t).smul_const _
  rw [← utNH_eq] at hG
  exact hG.congr_of_eventuallyEq (Eventually.of_forall fun s => val_uNV_eq D N ε s)

theorem continuous_utNH (N : ℕ) (ε : ℝ) : Continuous (utNH D N ε) := by
  have h : Continuous fun s => D.ρ' s • toL2c φ continuous_φ
      + ∑ j ∈ Finset.range (N + 1), ∑ m ∈ Finset.Icc 1 (M j),
          y' D ε j m s • toL2c (p (K j m)) (continuous_p _) :=
    (D.ρ'_continuous.smul continuous_const).add (continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun m _ => (continuous_y' D ε j m).smul continuous_const)
  exact h.congr fun s => (utNH_eq D N ε s).symm

/-- `u_N' = ∂ₜu_N ∈ H ⊂ V'`. -/
def uNV' (N : ℕ) (ε t : ℝ) : Hm1 Iπ := ofL2 Iπ (utNH D N ε t)

theorem norm_ofL2_le (h : L2 Iπ) : ‖ofL2 Iπ h‖ ≤ ‖h‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
  calc ‖ofL2 Iπ h z‖ = ‖⟪val Iπ z, h⟫_ℂ‖ := rfl
    _ ≤ ‖val Iπ z‖ * ‖h‖ := norm_inner_le_norm _ _
    _ ≤ ‖z‖ * ‖h‖ := by gcongr; exact norm_val_le z
    _ = ‖h‖ * ‖z‖ := mul_comm _ _

/-- Differentiability in `H` implies differentiability in `V'`. -/
theorem hasDerivAt_ofL2_comp {F : ℝ → L2 Iπ} {F' : L2 Iπ} {t : ℝ} (h : HasDerivAt F F' t) :
    HasDerivAt (fun s => ofL2 Iπ (F s)) (ofL2 Iπ F') t := by
  rw [hasDerivAt_iff_isLittleO] at h ⊢
  refine Asymptotics.IsBigO.trans_isLittleO ?_ h
  refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun s => ?_)
  rw [one_mul, ← ofL2_real_smul, ← ofL2_sub', ← ofL2_sub']
  exact norm_ofL2_le _

theorem hasDerivAt_ofH10_uNV (N : ℕ) (ε t : ℝ) :
    HasDerivAt (fun s => ofH10 Iπ (uNV D N ε s)) (uNV' D N ε t) t :=
  hasDerivAt_ofL2_comp (hasDerivAt_val_uNV D N ε t)

theorem continuous_uNV' (N : ℕ) (ε : ℝ) : Continuous (uNV' D N ε) :=
  (ofHL (val Iπ)).continuous.comp (continuous_utNH D N ε)

/-! ### The equation -/

theorem hasDerivAt_fluxN (N : ℕ) (ε t x : ℝ) :
    HasDerivAt (fun x => aN D N ε t x * uxN D N ε t x) (-(AuN D N ε t x)) x := by
  have h := HasDerivAt.fun_mul (hasDerivAt_aN_x D N ε t x) (hasDerivAt_uxN_x D N ε t x)
  refine h.congr_deriv ?_
  simp only [AuN]
  ring

theorem continuous_AuN_x (N : ℕ) (ε t : ℝ) : Continuous fun x => AuN D N ε t x :=
  Continuous.uncurry_left (f := AuN D N ε) t (continuous_AuN D N ε)

theorem continuous_aN_x (N : ℕ) (ε t : ℝ) : Continuous fun x => aN D N ε t x :=
  Continuous.uncurry_left (f := aN D N ε) t (continuous_aN D N ε)

/-- `A_{N,H}(t)u_N(t) ∈ H`. -/
def AuNH (N : ℕ) (ε t : ℝ) : L2 Iπ := toL2c (AuN D N ε t) (continuous_AuN_x D N ε t)

/-- `f_N(t) ∈ H`. -/
def fNH (N : ℕ) (ε t : ℝ) : L2 Iπ := toL2c (fN D N ε t) (continuous_fN_x D N ε t)

theorem form_uNV (N : ℕ) (ε t : ℝ) (w : H10 Iπ) :
    form Iπ (aN D N ε) t (uNV D N ε t) w = ofL2 Iπ (AuNH D N ε t) w := by
  set G : ℝ → ℂ := fun x => ((aN D N ε t x * uxN D N ε t x : ℝ) : ℂ) with hGdef
  set g : ℝ → ℂ := fun x => ((-(AuN D N ε t x) : ℝ) : ℂ) with hgdef
  have hG : ∀ x, HasDerivAt G (g x) x := fun x => (hasDerivAt_fluxN D N ε t x).ofReal_comp
  have hgc : Continuous g := continuous_cplx (continuous_AuN_x D N ε t).neg
  have hGc : Continuous G :=
    continuous_cplx ((continuous_aN_x D N ε t).mul (continuous_uxN_x D N ε t))
  have hG2 := memLp_Ioo_of_continuous (a := 0) (b := π) hGc
  have hg2 := memLp_Ioo_of_continuous (a := 0) (b := π) hgc
  have key := inner_dx_eq hG hgc hG2 hg2 w
  have e1 : form Iπ (aN D N ε) t (uNV D N ε t) w
      = ⟪dx Iπ w, toL2 Iπ G hG2⟫_ℂ := by
    rw [inner_L2_eq, form]
    refine integral_congr_ae ?_
    have hdx := dx_uNV D N ε t
    filter_upwards [coe_toL2c (continuous_uxN_x D N ε t), coe_toL2 G hG2] with x h1 h2
    rw [hdx, h1, h2, hGdef]
    simp only [Complex.ofReal_mul]
    ring
  have e2 : toL2 Iπ g hg2 = -AuNH D N ε t := by
    apply Lp.ext
    filter_upwards [coe_toL2 g hg2, coe_toL2c (continuous_AuN_x D N ε t),
      Lp.coeFn_neg (AuNH D N ε t)] with x h1 h2 h3
    rw [h1, h3, Pi.neg_apply, AuNH, h2]
    simp only [hgdef, Complex.ofReal_neg]
  rw [e1, key, e2, inner_neg_right, neg_neg]
  rfl

theorem equation_uNV (N : ℕ) (ε t : ℝ) (w : H10 Iπ) :
    uNV' D N ε t w + form Iπ (aN D N ε) t (uNV D N ε t) w
      = ofL2 Iπ (fNH D N ε t) w := by
  have e : utNH D N ε t + AuNH D N ε t = fNH D N ε t := by
    rw [utNH, AuNH, fNH, ← toL2c_add]
    exact toL2c_congr _ _ fun x _ => rfl
  rw [form_uNV, uNV', ← e, ofL2_add']
  rfl

/-- `u_N` is a Lions variational solution of the truncated problem. -/
theorem isLionsSolution_uNV (N : ℕ) (ε : ℝ) :
    IsLionsSolution Iπ (aN D N ε) (fNH D N ε) (uNV D N ε) :=
  ⟨memLp_of_continuousOn_Icc (continuous_uNV D N ε).continuousOn, uNV' D N ε,
    memLp_of_continuousOn_Icc (continuous_uNV' D N ε).continuousOn,
    hasWeakDeriv_of_hasDerivAt_off_countable Set.countable_empty
      (fun t _ => (hasDerivAt_ofH10_uNV D N ε t).continuousAt.continuousWithinAt)
      (fun t _ => hasDerivAt_ofH10_uNV D N ε t)
      (integrableOn_of_continuousOn_Icc (continuous_uNV' D N ε).continuousOn),
    Eventually.of_forall fun t w => equation_uNV D N ε t w,
    ⟨fun t => ofH10 Iπ (uNV D N ε t),
      fun t _ => (hasDerivAt_ofH10_uNV D N ε t).continuousAt.continuousWithinAt,
      Eventually.of_forall fun _ => rfl, by
        show ofH10 Iπ (uNV D N ε 0) = 0
        rw [uNV_zero, ofH10_zero]⟩⟩

/-- A jointly continuous real function of `(t,x)` is continuous as a curve in `H`. -/
theorem continuous_toL2c_of_joint {g : ℝ → ℝ → ℝ} (hg : Continuous fun q : ℝ × ℝ => g q.1 q.2) :
    Continuous fun t => toL2c (g t) (hg.comp (Continuous.prodMk_right t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h := (tendsto_normSq_sub_of_continuous _ hg t).sqrt
  rw [Real.sqrt_zero] at h
  refine h.congr fun s => ?_
  rw [← toL2c_sub, norm_toL2c]

theorem continuous_AuNH (N : ℕ) (ε : ℝ) : Continuous (AuNH D N ε) :=
  continuous_toL2c_of_joint (continuous_AuN D N ε)

theorem continuous_fNH (N : ℕ) (ε : ℝ) : Continuous (fNH D N ε) :=
  continuous_toL2c_of_joint (continuous_fN D N ε)

/-! ### Maximal-regularity constants -/

/-- `C` is a **maximal-regularity constant** for the coefficient `𝔞` on `(0,π)`: for every
Lions solution `w` of `w' + 𝒜(t)w = g`, `w(0) = 0`, with `g ∈ L²(0,1;H)`, whose distributional
`V'`-derivative is represented by `G ∈ L²(0,1;H)` and whose elliptic part `𝒜(t)w(t)` is
represented by `Aw ∈ L²(0,1;H)`,
`‖G‖_{L²(0,1;H)} + ‖Aw‖_{L²(0,1;H)} ≤ C ‖g‖_{L²(0,1;H)}`. -/
def IsMaxRegConstant (𝔞 : ℝ → ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ (g : ℝ → L2 Iπ) (w : ℝ → H10 Iπ) (G Aw : ℝ → L2 Iπ),
    MemLp g 2 μ01 → IsLionsSolution Iπ 𝔞 g w →
    MemLp G 2 μ01 → HasWeakDeriv (fun t => ofH10 Iπ (w t)) (fun t => ofL2 Iπ (G t)) →
    MemLp Aw 2 μ01 →
    (∀ᵐ t ∂μ01, ∀ z : H10 Iπ, form Iπ 𝔞 t (w t) z = ofL2 Iπ (Aw t) z) →
    (eLpNorm G 2 μ01).toReal + (eLpNorm Aw 2 μ01).toReal ≤ C * (eLpNorm g 2 μ01).toReal

theorem eLpNorm_toReal_eq_sqrt {F : ℝ → L2 Iπ} (hF : MemLp F 2 μ01) :
    (eLpNorm F 2 μ01).toReal = Real.sqrt (∫ t in (0 : ℝ)..1, ‖F t‖ ^ 2) := by
  rw [hF.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow, ← setIntegral_Ioo_eq_intervalIntegral]
  norm_num

/-- **The remark on the growth of the maximal-regularity constant.**  For `0 < ε ≤ 1` and every
`N`: the truncated coefficient satisfies the `C^{0,1/2}` bounds uniformly in `N`; `u_N` is a Lions
solution with `∂ₜu_N, A_{N,H}u_N ∈ C([0,1];H)`; `‖f_N‖²_{L²(0,1;H)} ≤ π C_f²`;
`‖∂ₜu_N‖²_{L²(0,1;H)} ≥ (πε²/1536)(log(N+2) - 1)`; and every maximal-regularity constant
`C ≥ 0` of `𝔞_N` satisfies `√((πε²/1536)(log(N+2) - 1)) ≤ C √π C_f`. -/
theorem maxRegConstant_growth {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (N : ℕ) :
    (∀ t x, |aN D N ε t x - 1| ≤ ε / 480) ∧
    (∀ s t x, |aN D N ε t x - aN D N ε s x| ≤ 2 * |ε| * Cβ D * Real.sqrt |t - s|) ∧
    IsLionsSolution Iπ (aN D N ε) (fNH D N ε) (uNV D N ε) ∧
    Continuous (utNH D N ε) ∧ Continuous (AuNH D N ε) ∧
    (∀ t, ∀ z : H10 Iπ, uNV' D N ε t z = ofL2 Iπ (utNH D N ε t) z) ∧
    (∀ t, ∀ z : H10 Iπ,
      form Iπ (aN D N ε) t (uNV D N ε t) z = ofL2 Iπ (AuNH D N ε t) z) ∧
    ∫ t in (0 : ℝ)..1, ‖fNH D N ε t‖ ^ 2 ≤ π * Cf D ^ 2 ∧
    π * ε ^ 2 / 1536 * (Real.log ((N : ℝ) + 2) - 1) ≤ ∫ t in (0 : ℝ)..1, ‖utNH D N ε t‖ ^ 2 ∧
    ∀ C : ℝ, 0 ≤ C → IsMaxRegConstant (aN D N ε) C →
      Real.sqrt (π * ε ^ 2 / 1536 * (Real.log ((N : ℝ) + 2) - 1)) ≤ C * (Real.sqrt π * Cf D) := by
  have hf2 : ∫ t in (0 : ℝ)..1, ‖fNH D N ε t‖ ^ 2 ≤ π * Cf D ^ 2 := by
    refine le_trans (le_of_eq ?_) (integral_normSq_fN_le D hε0 hε1 N)
    congr 1; ext t; rw [fNH, norm_toL2c_sq]
  have hu2 : π * ε ^ 2 / 1536 * (Real.log ((N : ℝ) + 2) - 1)
      ≤ ∫ t in (0 : ℝ)..1, ‖utNH D N ε t‖ ^ 2 := by
    refine le_trans (maximal_regularity_constant_growth D ε N) (le_of_eq ?_)
    congr 1; ext t; rw [utNH, norm_toL2c_sq]
  refine ⟨fun t x => abs_aN_sub_one_le D hε0 N t x, fun s t x => abs_aN_sub_le D N ε s t x,
    isLionsSolution_uNV D N ε, continuous_utNH D N ε, continuous_AuNH D N ε,
    fun _ _ => rfl, fun t z => form_uNV D N ε t z, hf2, hu2, fun C hC hmax => ?_⟩
  have hfm : MemLp (fNH D N ε) 2 μ01 :=
    memLp_of_continuousOn_Icc (continuous_fNH D N ε).continuousOn
  have hGm : MemLp (utNH D N ε) 2 μ01 :=
    memLp_of_continuousOn_Icc (continuous_utNH D N ε).continuousOn
  have hAm : MemLp (AuNH D N ε) 2 μ01 :=
    memLp_of_continuousOn_Icc (continuous_AuNH D N ε).continuousOn
  have hw : HasWeakDeriv (fun t => ofH10 Iπ (uNV D N ε t)) (fun t => ofL2 Iπ (utNH D N ε t)) :=
    hasWeakDeriv_of_hasDerivAt_off_countable Set.countable_empty
      (fun t _ => (hasDerivAt_ofH10_uNV D N ε t).continuousAt.continuousWithinAt)
      (fun t _ => hasDerivAt_ofH10_uNV D N ε t)
      (integrableOn_of_continuousOn_Icc (continuous_uNV' D N ε).continuousOn)
  have hineq := hmax (fNH D N ε) (uNV D N ε) (utNH D N ε) (AuNH D N ε) hfm
    (isLionsSolution_uNV D N ε) hGm hw hAm
    (Eventually.of_forall fun t z => form_uNV D N ε t z)
  rw [eLpNorm_toReal_eq_sqrt hGm, eLpNorm_toReal_eq_sqrt hAm, eLpNorm_toReal_eq_sqrt hfm] at hineq
  have h1 : Real.sqrt (π * ε ^ 2 / 1536 * (Real.log ((N : ℝ) + 2) - 1))
      ≤ Real.sqrt (∫ t in (0 : ℝ)..1, ‖utNH D N ε t‖ ^ 2) := Real.sqrt_le_sqrt hu2
  have h2 : Real.sqrt (∫ t in (0 : ℝ)..1, ‖fNH D N ε t‖ ^ 2) ≤ Real.sqrt π * Cf D := by
    have hCf : 0 ≤ Cf D := by
      unfold Cf
      have := D.Cρ_nonneg
      have := D.Cη_nonneg
      positivity
    calc Real.sqrt (∫ t in (0 : ℝ)..1, ‖fNH D N ε t‖ ^ 2) ≤ Real.sqrt (π * Cf D ^ 2) :=
          Real.sqrt_le_sqrt hf2
      _ = Real.sqrt π * Cf D := by
          rw [Real.sqrt_mul pi_pos.le, Real.sqrt_sq hCf]
  have h3 := Real.sqrt_nonneg (∫ t in (0 : ℝ)..1, ‖AuNH D N ε t‖ ^ 2)
  calc _ ≤ Real.sqrt (∫ t in (0 : ℝ)..1, ‖utNH D N ε t‖ ^ 2) := h1
    _ ≤ C * Real.sqrt (∫ t in (0 : ℝ)..1, ‖fNH D N ε t‖ ^ 2) := by linarith
    _ ≤ C * (Real.sqrt π * Cf D) := by gcongr

end LionsC12
