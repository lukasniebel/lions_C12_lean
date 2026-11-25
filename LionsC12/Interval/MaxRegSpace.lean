module

public import LionsC12.Interval.FrozenDomain

/-!
# The domain `D₀` of the Dirichlet Laplacian as a Hilbert space, and `C¹` coefficients

The space in which the truncated problems of the remark *Growth of the maximal-regularity
constant* are solved.  In `H = L²((0,π);ℂ)`, `V = H¹₀((0,π);ℂ)`:

* `mulCLM` — multiplication by a continuous real function as a bounded operator on `H`, with
  `‖mulCLM c‖ ≤ sup_{[0,π]} |c|` (`norm_mulCLM_le`), and norm-continuous in `t` for a jointly
  continuous function of `(t,x)` (`continuous_mulCLM`);
* `D₀` — the domain `D(A_{0,H}) = {v ∈ V | ∃ h ∈ H, ⟨∂ₓv, ∂ₓw⟩ = ⟨h, w⟩ ∀ w ∈ V}` of the
  Dirichlet Laplacian, realised as its graph `{(v, A_{0,H}v)}`, a closed subspace of `V × H`; it
  is a complex Hilbert space with `‖v‖²_{D₀} = ‖v‖²_V + ‖A_{0,H}v‖²_H`;
* `D₀.incl : D₀ → V`, `D₀.lap = A_{0,H} : D₀ → H` and `D₀.shift = I + A_{0,H} : D₀ → H`, with
  `(w, v)_V = ⟨w, (I + A_{0,H})v⟩_H` for `w ∈ V`, `v ∈ D₀` (`inner_incl`);
* `D₀.exists_shift_eq` — `I + A_{0,H} : D₀ → H` is onto (Riesz representation in `V`), and
  `D₀.denseRange_incl` — `D₀` is dense in `V`: `(D₀, V)` is a Gelfand pair;
* `IsC1Coeff` — a coefficient `c(t,x)`, `C¹` in `x`, with `c, ∂ₓc` jointly continuous,
  `0 < m ≤ c ≤ Λ` and `|∂ₓc| ≤ L`;
* `opA` — for such a coefficient, `A(t) = c(t) A_{0,H} - ∂ₓc(t) ∂ₓ ∈ L(D₀, H)` is the
  `H`-realisation of the form `c(t)[·,·]` on `D₀` (`isRealisation_opA`), norm-continuous in `t`
  (`continuous_opA`), and satisfies the Gårding inequality
  `(m/2) ‖v‖²_{D₀} ≤ Re ⟨A(t)v, (I + A_{0,H})v⟩_H + (L²/(2m) + m/2) ‖v‖²_V` (`garding_opA`).
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped InnerProductSpace ComplexConjugate

/-! ### Multiplication operators -/

theorem mulL2_add {c : ℝ → ℝ} (hc : Continuous c) (F G : L2 Iπ) :
    mulL2 c hc (F + G) = mulL2 c hc F + mulL2 c hc G := by
  apply Lp.ext
  filter_upwards [coe_mulL2 hc (F + G), coe_mulL2 hc F, coe_mulL2 hc G, Lp.coeFn_add F G,
    Lp.coeFn_add (mulL2 c hc F) (mulL2 c hc G)] with x h1 h2 h3 h4 h5
  rw [h5, Pi.add_apply, h1, h2, h3, h4, Pi.add_apply, mul_add]

theorem mulL2_smul {c : ℝ → ℝ} (hc : Continuous c) (z : ℂ) (F : L2 Iπ) :
    mulL2 c hc (z • F) = z • mulL2 c hc F := by
  apply Lp.ext
  filter_upwards [coe_mulL2 hc (z • F), coe_mulL2 hc F, Lp.coeFn_smul z F,
    Lp.coeFn_smul z (mulL2 c hc F)] with x h1 h2 h3 h4
  rw [h4, Pi.smul_apply, h1, h2, h3, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- Multiplication by a continuous real function, as a bounded operator on `L²((0,π);ℂ)`. -/
def mulCLM (c : ℝ → ℝ) (hc : Continuous c) : L2 Iπ →L[ℂ] L2 Iπ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := mulL2 c hc
      map_add' := mulL2_add hc
      map_smul' := mulL2_smul hc } (by
    obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc 0 π)).exists_bound_of_continuousOn
      hc.continuousOn
    exact ⟨M, fun F => norm_mulL2_le hc (fun x hx => by
      rw [← Real.norm_eq_abs]; exact hM x hx) F⟩)

theorem mulCLM_apply {c : ℝ → ℝ} (hc : Continuous c) (F : L2 Iπ) :
    mulCLM c hc F = mulL2 c hc F := rfl

theorem norm_mulCLM_le {c : ℝ → ℝ} (hc : Continuous c) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Icc 0 π, |c x| ≤ M) : ‖mulCLM c hc‖ ≤ M :=
  ContinuousLinearMap.opNorm_le_bound _ hM0 fun F => norm_mulL2_le hc hM F

theorem mulCLM_sub {c d : ℝ → ℝ} (hc : Continuous c) (hd : Continuous d) :
    mulCLM c hc - mulCLM d hd = mulCLM (fun x => c x - d x) (hc.sub hd) := by
  ext1 F
  rw [sub_apply, mulCLM_apply, mulCLM_apply, mulCLM_apply]
  apply Lp.ext
  filter_upwards [coe_mulL2 hc F, coe_mulL2 hd F, coe_mulL2 (c := fun x => c x - d x) (hc.sub hd) F,
    Lp.coeFn_sub (mulL2 c hc F) (mulL2 d hd F)] with x h1 h2 h3 h4
  rw [h4, Pi.sub_apply, h1, h2, h3, Complex.ofReal_sub]
  ring

/-- For a jointly continuous `F(t,x)`, `t ↦ (multiplication by F(t,·))` is norm-continuous. -/
theorem continuous_mulCLM {F : ℝ → ℝ → ℝ} (hF : Continuous fun q : ℝ × ℝ => F q.1 q.2) :
    Continuous fun t => mulCLM (F t) (hF.comp (Continuous.prodMk_right t)) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro δ hδ
  have hu := Continuous.tendstoUniformly (fun t (x : Icc 0 π) => F t x)
    (hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) t₀
  rw [Metric.tendstoUniformly_iff] at hu
  filter_upwards [hu (δ / 2) (half_pos hδ)] with t ht
  rw [dist_eq_norm, mulCLM_sub]
  refine lt_of_le_of_lt (norm_mulCLM_le _ (half_pos hδ).le fun x hx => ?_) (half_lt_self hδ)
  have := ht ⟨x, hx⟩
  rw [Real.dist_eq, abs_sub_comm] at this
  exact this.le

/-- `Re ⟨c F, F⟩ ≥ m ‖F‖²` for `c ≥ m` on `(0,π)`. -/
theorem re_inner_mulL2_self_ge {c : ℝ → ℝ} (hc : Continuous c) {m : ℝ}
    (hm : ∀ x ∈ Iπ, m ≤ c x) (F : L2 Iπ) : m * ‖F‖ ^ 2 ≤ (⟪mulL2 c hc F, F⟫_ℂ).re := by
  have hint : Integrable (fun x => conj (mulL2 c hc F x) * F x) (volume.restrict Iπ) := by
    have := L2.integrable_inner (𝕜 := ℂ) (mulL2 c hc F) F
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [RCLike.inner_apply, mul_comm]
  have hsq : ‖F‖ ^ 2 = ∫ x in Iπ, ‖F x‖ ^ 2 := by
    have := (Lp.memLp F).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
    rw [Lp.norm_def, this, ENNReal.toReal_ofReal (by positivity)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hre : (⟪mulL2 c hc F, F⟫_ℂ).re = ∫ x in Iπ, c x * ‖F x‖ ^ 2 := by
    rw [inner_L2_eq]
    have h1 := integral_re hint
    simp only [RCLike.re_to_complex] at h1
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [coe_mulL2 hc F] with x hx
    rw [hx, map_mul, Complex.conj_ofReal, mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hFint : Integrable (fun x => ‖F x‖ ^ 2) (volume.restrict Iπ) :=
    (L2.integrable_inner (𝕜 := ℂ) F F).norm.congr (Eventually.of_forall fun x => by
      simp only [RCLike.inner_apply, norm_mul, RCLike.norm_conj, ← sq])
  have hcint : Integrable (fun x => c x * ‖F x‖ ^ 2) (volume.restrict Iπ) := by
    refine hint.re.congr ?_
    filter_upwards [coe_mulL2 hc F] with x hx
    simp only [RCLike.re_to_complex]
    rw [hx, map_mul, Complex.conj_ofReal, mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre, hsq, ← integral_const_mul]
  refine integral_mono_ae (hFint.const_mul m) hcint ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hxI
  gcongr
  exact hm x hxI

/-! ### The domain `D₀` of the Dirichlet Laplacian -/

theorem isRealisation_one_iff_inner (v : H10 Iπ) (h : L2 Iπ) :
    IsRealisation one 0 v h ↔ ∀ w : H10 Iπ, ⟪dx Iπ w, dx Iπ v⟫_ℂ = ⟪val Iπ w, h⟫_ℂ := by
  simp only [IsRealisation, formH_one_eq]
  rfl

/-- The inner product of `H¹₀`: `(v, w)_V = ⟨v, w⟩_H + ⟨∂ₓv, ∂ₓw⟩_H`. -/
theorem inner_H10 (v w : H10 Iπ) :
    ⟪v, w⟫_ℂ = ⟪val Iπ v, val Iπ w⟫_ℂ + ⟪dx Iπ v, dx Iπ w⟫_ℂ := rfl

/-- The graph `{(v, A_{0,H}v) | v ∈ D₀}` of the Dirichlet Laplacian in `V × H`. -/
def D₀Graph : Submodule ℂ (WithLp 2 (H10 Iπ × L2 Iπ)) where
  carrier := {p | IsRealisation one 0 (WithLp.ofLp p).1 (WithLp.ofLp p).2}
  add_mem' := by
    intro p q hp hq
    simp only [Set.mem_ofPred_eq, isRealisation_one_iff_inner] at *
    intro w
    simp only [WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, map_add, inner_add_right, hp w,
      hq w]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, isRealisation_one_iff_inner]
    intro w
    simp
  smul_mem' := by
    intro z p hp
    simp only [Set.mem_ofPred_eq, isRealisation_one_iff_inner] at *
    intro w
    simp only [WithLp.ofLp_smul, Prod.smul_fst, Prod.smul_snd, map_smul, inner_smul_right, hp w]

theorem isClosed_D₀Graph : IsClosed (D₀Graph : Set (WithLp 2 (H10 Iπ × L2 Iπ))) := by
  have e : (D₀Graph : Set (WithLp 2 (H10 Iπ × L2 Iπ))) = ⋂ w : H10 Iπ,
      {p | ⟪dx Iπ w, dx Iπ (WithLp.fstL 2 ℂ (H10 Iπ) (L2 Iπ) p)⟫_ℂ
        = ⟪val Iπ w, WithLp.sndL 2 ℂ (H10 Iπ) (L2 Iπ) p⟫_ℂ} := by
    ext p
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, WithLp.fstL_apply,
      WithLp.sndL_apply]
    exact isRealisation_one_iff_inner _ _
  rw [e]
  exact isClosed_iInter fun w => isClosed_eq
    (continuous_const.inner ((dx Iπ).continuous.comp (WithLp.fstL 2 ℂ _ _).continuous))
    (continuous_const.inner (WithLp.sndL 2 ℂ _ _).continuous)

instance : CompleteSpace D₀Graph := isClosed_D₀Graph.completeSpace_coe

/-- The domain `D₀ = D(A_{0,H})` of the Dirichlet Laplacian, as the Hilbert space of the pairs
`(v, A_{0,H}v)`, with `‖v‖²_{D₀} = ‖v‖²_V + ‖A_{0,H}v‖²_H`. -/
def D₀ : Type := D₀Graph

instance : NormedAddCommGroup D₀ := inferInstanceAs (NormedAddCommGroup D₀Graph)

instance : InnerProductSpace ℂ D₀ := inferInstanceAs (InnerProductSpace ℂ D₀Graph)

instance : CompleteSpace D₀ := inferInstanceAs (CompleteSpace D₀Graph)

namespace D₀

/-- The pair `(v, A_{0,H}v)`. -/
def pair (v : D₀) : WithLp 2 (H10 Iπ × L2 Iπ) := @Subtype.val _ (fun x => x ∈ D₀Graph) v

theorem pair_mem (v : D₀) : pair v ∈ D₀Graph := @Subtype.property _ (fun x => x ∈ D₀Graph) v

/-- The inclusion `D₀ ↪ V`. -/
def incl : D₀ →L[ℂ] H10 Iπ := (WithLp.fstL 2 ℂ (H10 Iπ) (L2 Iπ)).comp D₀Graph.subtypeL

/-- The Dirichlet Laplacian `A_{0,H} : D₀ → H`. -/
def lap : D₀ →L[ℂ] L2 Iπ := (WithLp.sndL 2 ℂ (H10 Iπ) (L2 Iπ)).comp D₀Graph.subtypeL

/-- `I + A_{0,H} : D₀ → H`. -/
def shift : D₀ →L[ℂ] L2 Iπ := (val Iπ).comp incl + lap

theorem incl_apply (v : D₀) : incl v = (WithLp.ofLp (pair v)).1 := rfl

theorem lap_apply (v : D₀) : lap v = (WithLp.ofLp (pair v)).2 := rfl

theorem shift_apply (v : D₀) : shift v = val Iπ (incl v) + lap v := rfl

theorem isRealisation (v : D₀) : IsRealisation one 0 (incl v) (lap v) := pair_mem v

/-- The element of `D₀` with `v ∈ V` and `A_{0,H}v = h`. -/
def mk (v : H10 Iπ) (h : L2 Iπ) (hv : IsRealisation one 0 v h) : D₀ :=
  (⟨WithLp.toLp 2 (v, h), hv⟩ : {x // x ∈ D₀Graph})

@[simp] theorem incl_mk (v : H10 Iπ) (h : L2 Iπ) (hv : IsRealisation one 0 v h) :
    incl (mk v h hv) = v := rfl

@[simp] theorem lap_mk (v : H10 Iπ) (h : L2 Iπ) (hv : IsRealisation one 0 v h) :
    lap (mk v h hv) = h := rfl

theorem norm_sq (v : D₀) : ‖v‖ ^ 2 = ‖incl v‖ ^ 2 + ‖lap v‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (pair v)

theorem norm_incl_le (v : D₀) : ‖incl v‖ ≤ ‖v‖ := by
  have h := norm_sq v
  nlinarith [norm_nonneg (incl v), norm_nonneg (lap v), norm_nonneg v, sq_nonneg ‖lap v‖]

theorem norm_lap_le (v : D₀) : ‖lap v‖ ≤ ‖v‖ := by
  have h := norm_sq v
  nlinarith [norm_nonneg (incl v), norm_nonneg (lap v), norm_nonneg v, sq_nonneg ‖incl v‖]

theorem norm_shift_le (v : D₀) : ‖shift v‖ ≤ 2 * ‖v‖ := by
  rw [shift_apply]
  calc _ ≤ ‖val Iπ (incl v)‖ + ‖lap v‖ := norm_add_le _ _
    _ ≤ ‖v‖ + ‖v‖ := add_le_add ((norm_val_le _).trans (norm_incl_le v)) (norm_lap_le v)
    _ = 2 * ‖v‖ := by ring

theorem ext {v w : D₀} (h1 : incl v = incl w) (h2 : lap v = lap w) : v = w := by
  have h : pair v = pair w := by
    rw [← WithLp.toLp_ofLp (p := 2) (pair v), ← WithLp.toLp_ofLp (p := 2) (pair w)]
    exact congrArg (WithLp.toLp 2) (Prod.ext h1 h2)
  exact Subtype.ext (p := fun x => x ∈ D₀Graph) h

theorem incl_injective : Function.Injective incl := fun v w h =>
  ext h (isRealisation_unique (isRealisation v) (h ▸ isRealisation w))

/-- `(w, v)_V = ⟨w, (I + A_{0,H})v⟩_H` for `w ∈ V`, `v ∈ D₀`. -/
theorem inner_incl (w : H10 Iπ) (v : D₀) : ⟪w, incl v⟫_ℂ = ⟪val Iπ w, shift v⟫_ℂ := by
  rw [inner_H10, shift_apply, inner_add_right,
    (isRealisation_one_iff_inner _ _).1 (isRealisation v) w]

/-- `I + A_{0,H} : D₀ → H` is onto: for `z ∈ H` the Riesz representative `v ∈ V` of
`w ↦ ⟨w, z⟩_H` lies in `D₀`, with `A_{0,H}v = z - v`. -/
theorem exists_shift_eq (z : L2 Iπ) : ∃ v : D₀, shift v = z := by
  set ℓ : StrongDual ℂ (H10 Iπ) := (innerSL ℂ z).comp (val Iπ) with hℓ
  set v' : H10 Iπ := (InnerProductSpace.toDual ℂ (H10 Iπ)).symm ℓ with hv'
  have key : ∀ w : H10 Iπ, ⟪w, v'⟫_ℂ = ⟪val Iπ w, z⟫_ℂ := by
    intro w
    have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := H10 Iπ) (x := w) (y := ℓ)
    rw [← hv'] at h
    rw [← inner_conj_symm, h, hℓ, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      inner_conj_symm]
  have hv : IsRealisation one 0 v' (z - val Iπ v') := by
    rw [isRealisation_one_iff_inner]
    intro w
    have h := key w
    rw [inner_H10] at h
    rw [inner_sub_right, ← h]
    ring
  refine ⟨mk v' (z - val Iπ v') hv, ?_⟩
  rw [shift_apply, incl_mk, lap_mk, add_sub_cancel]

/-- `D₀` is dense in `V`. -/
theorem denseRange_incl : DenseRange incl := by
  have : (LinearMap.range (incl : D₀ →ₗ[ℂ] H10 Iπ)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro u hu
    rw [Submodule.mem_orthogonal'] at hu
    obtain ⟨v, hv⟩ := exists_shift_eq (val Iπ u)
    have h := hu (incl v) ⟨v, rfl⟩
    rw [inner_incl, hv, inner_self_eq_zero] at h
    exact val_injective isOpen_Ioo (by rw [h, map_zero])
  exact (Submodule.dense_iff_topologicalClosure_eq_top).2 this

end D₀

/-! ### `C¹` coefficients and the operators `A(t) ∈ L(D₀, H)` -/

/-- A coefficient `c(t,x)`, continuously differentiable in `x` with derivative `c'(t,x)`, such
that `c` and `c'` are jointly continuous, `0 < m ≤ c ≤ Λ` and `|c'| ≤ L`. -/
structure IsC1Coeff (c c' : ℝ → ℝ → ℝ) (m Λ L : ℝ) : Prop where
  hasDerivAt : ∀ t x, HasDerivAt (c t) (c' t x) x
  continuous : Continuous fun q : ℝ × ℝ => c q.1 q.2
  continuous_deriv : Continuous fun q : ℝ × ℝ => c' q.1 q.2
  pos : 0 < m
  ge : ∀ t x, m ≤ c t x
  le : ∀ t x, c t x ≤ Λ
  abs_deriv_le : ∀ t x, |c' t x| ≤ L

namespace IsC1Coeff

variable {c c' : ℝ → ℝ → ℝ} {m Λ L : ℝ} (hc : IsC1Coeff c c' m Λ L)
include hc

theorem continuous_x (t : ℝ) : Continuous (c t) :=
  hc.continuous.comp (Continuous.prodMk_right t)

theorem continuous_deriv_x (t : ℝ) : Continuous (c' t) :=
  hc.continuous_deriv.comp (Continuous.prodMk_right t)

theorem abs_le (t x : ℝ) : |c t x| ≤ Λ := by
  rw [abs_of_pos (hc.pos.trans_le (hc.ge t x))]
  exact hc.le t x

theorem L_nonneg : 0 ≤ L := (abs_nonneg _).trans (hc.abs_deriv_le 0 0)

theorem Λ_pos : 0 < Λ := hc.pos.trans_le ((hc.ge 0 0).trans (hc.le 0 0))

theorem nonneg (t x : ℝ) : 0 ≤ c t x := hc.pos.le.trans (hc.ge t x)

theorem isBoundedCoeff (t : ℝ) : IsBoundedCoeff c t Λ :=
  ⟨(hc.continuous_x t).measurable, hc.abs_le t⟩

end IsC1Coeff

variable {c c' : ℝ → ℝ → ℝ} {m Λ L : ℝ}

/-- The operator `A(t) = c(t) A_{0,H} - c'(t) ∂ₓ ∈ L(D₀, H)`, the `H`-realisation of the form
`c(t)[·,·]` on `D₀`. -/
def opA (hc : IsC1Coeff c c' m Λ L) (t : ℝ) : D₀ →L[ℂ] L2 Iπ :=
  (mulCLM (c t) (hc.continuous_x t)).comp D₀.lap
    - (mulCLM (c' t) (hc.continuous_deriv_x t)).comp ((dx Iπ).comp D₀.incl)

variable (hc : IsC1Coeff c c' m Λ L)

theorem opA_apply (t : ℝ) (v : D₀) :
    opA hc t v = mulL2 (c t) (hc.continuous_x t) (D₀.lap v)
      - mulL2 (c' t) (hc.continuous_deriv_x t) (dx Iπ (D₀.incl v)) := rfl

/-- `A(t)v` is the `H`-realisation of the form `c(t)[·,·]` at `v ∈ D₀`. -/
theorem isRealisation_opA (t : ℝ) (v : D₀) : IsRealisation c t (D₀.incl v) (opA hc t v) :=
  isRealisation_of_one (hc.hasDerivAt t) (hc.continuous_deriv_x t) (hc.continuous_x t)
    (D₀.isRealisation v)

theorem norm_opA_apply_le (t : ℝ) (v : D₀) : ‖opA hc t v‖ ≤ (Λ + L) * ‖v‖ := by
  rw [opA_apply]
  have h1 : ‖mulL2 (c t) (hc.continuous_x t) (D₀.lap v)‖ ≤ Λ * ‖v‖ :=
    (norm_mulL2_le _ (fun x _ => hc.abs_le t x) _).trans
      (mul_le_mul_of_nonneg_left (D₀.norm_lap_le v) hc.Λ_pos.le)
  have h2 : ‖mulL2 (c' t) (hc.continuous_deriv_x t) (dx Iπ (D₀.incl v))‖ ≤ L * ‖v‖ :=
    (norm_mulL2_le _ (fun x _ => hc.abs_deriv_le t x) _).trans
      (mul_le_mul_of_nonneg_left ((norm_dx_le _).trans (D₀.norm_incl_le v)) hc.L_nonneg)
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ Λ * ‖v‖ + L * ‖v‖ := add_le_add h1 h2
    _ = (Λ + L) * ‖v‖ := by ring

theorem norm_opA_le (t : ℝ) : ‖opA hc t‖ ≤ Λ + L :=
  ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hc.Λ_pos.le hc.L_nonneg)
    (norm_opA_apply_le hc t)

/-- `t ↦ A(t) ∈ L(D₀, H)` is norm-continuous. -/
theorem continuous_opA : Continuous (opA hc) :=
  ((continuous_mulCLM hc.continuous).clm_comp continuous_const).sub
    ((continuous_mulCLM hc.continuous_deriv).clm_comp continuous_const)

/-- **The Gårding inequality on `D₀`**:
`(m/2) ‖v‖²_{D₀} ≤ Re ⟨A(t)v, (I + A_{0,H})v⟩_H + (L²/(2m) + m/2) ‖v‖²_V`.  The term
`Re ⟨A(t)v, v⟩_H = Re c(t)[v,v]` is nonnegative, and
`Re ⟨A(t)v, A_{0,H}v⟩_H ≥ m ‖A_{0,H}v‖² - L ‖∂ₓv‖ ‖A_{0,H}v‖`. -/
theorem garding_opA (t : ℝ) (v : D₀) :
    m / 2 * ‖v‖ ^ 2
      ≤ (⟪opA hc t v, D₀.shift v⟫_ℂ).re + (L ^ 2 / (2 * m) + m / 2) * ‖D₀.incl v‖ ^ 2 := by
  have hm := hc.pos
  set a := ‖val Iπ (D₀.incl v)‖
  set b := ‖dx Iπ (D₀.incl v)‖
  set d := ‖D₀.lap v‖
  have hb0 : 0 ≤ b := norm_nonneg _
  have hd0 : 0 ≤ d := norm_nonneg _
  have hv : ‖v‖ ^ 2 = a ^ 2 + b ^ 2 + d ^ 2 := by rw [D₀.norm_sq, norm_sq_H10]
  have hi : ‖D₀.incl v‖ ^ 2 = a ^ 2 + b ^ 2 := norm_sq_H10 _
  -- `Re ⟨A(t)v, v⟩_H = Re c(t)[v,v] ≥ 0`
  have h1 : 0 ≤ (⟪opA hc t v, val Iπ (D₀.incl v)⟫_ℂ).re := by
    have e := isRealisation_opA hc t v (D₀.incl v)
    have h := form_self_re_nonneg (hc.isBoundedCoeff t) (hc.nonneg t) (D₀.incl v)
    rw [e] at h
    change 0 ≤ (⟪val Iπ (D₀.incl v), opA hc t v⟫_ℂ).re at h
    rwa [← inner_conj_symm, Complex.conj_re] at h
  -- `Re ⟨c A₀v, A₀v⟩_H ≥ m ‖A₀v‖²`
  have h2 : m * d ^ 2
      ≤ (⟪mulL2 (c t) (hc.continuous_x t) (D₀.lap v), D₀.lap v⟫_ℂ).re :=
    re_inner_mulL2_self_ge _ (fun x _ => hc.ge t x) _
  -- `|⟨c' ∂ₓv, A₀v⟩_H| ≤ L ‖∂ₓv‖ ‖A₀v‖`
  have h3 : (⟪mulL2 (c' t) (hc.continuous_deriv_x t) (dx Iπ (D₀.incl v)), D₀.lap v⟫_ℂ).re
      ≤ L * b * d := by
    refine (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    exact mul_le_mul_of_nonneg_right
      (norm_mulL2_le _ (fun x _ => hc.abs_deriv_le t x) _) hd0
  have hre : (⟪opA hc t v, D₀.shift v⟫_ℂ).re
      = (⟪opA hc t v, val Iπ (D₀.incl v)⟫_ℂ).re
        + ((⟪mulL2 (c t) (hc.continuous_x t) (D₀.lap v), D₀.lap v⟫_ℂ).re
          - (⟪mulL2 (c' t) (hc.continuous_deriv_x t) (dx Iπ (D₀.incl v)), D₀.lap v⟫_ℂ).re) := by
    rw [D₀.shift_apply, inner_add_right, Complex.add_re]
    congr 1
    rw [opA_apply, inner_sub_left, Complex.sub_re]
  -- `L b d ≤ (m/2) d² + (L²/(2m)) b²`
  have hamgm : L * b * d ≤ m / 2 * d ^ 2 + L ^ 2 / (2 * m) * b ^ 2 := by
    have e : m / 2 * d ^ 2 + L ^ 2 / (2 * m) * b ^ 2 - L * b * d
        = (m * d - L * b) ^ 2 / (2 * m) := by
      field_simp
      ring
    have : 0 ≤ (m * d - L * b) ^ 2 / (2 * m) := by positivity
    linarith
  have hL2 : 0 ≤ L ^ 2 / (2 * m) := by positivity
  rw [hv, hi, hre]
  nlinarith [sq_nonneg a]

end LionsC12
