module

public import LionsC12.Interval.Theorem

/-!
# Proposition 3.4 in the paper's spaces: common operator domain without uniform graph control

For `t ∈ ℝ` let `A_H(t)` be the realisation in `H = L²((0,π);ℂ)` of `𝒜(t) = -∂ₓ(𝔞(t,·)∂ₓ)`:
its domain is `D(A_H(t)) = {v ∈ V : ∃ h ∈ H, 𝔞(t)[v,w] = ⟨h, w⟩ for all w ∈ V}` and
`A_H(t)v = h`.  For the constant coefficient `1` this is the Dirichlet Laplacian `A_{0,H}`, with
domain `D₀ = D(A_{0,H})`, which is `H²(0,π) ∩ H¹₀(0,π)` (`domain_one_eq_H2` and
`domain_eq_H2` in `LionsC12.Interval.DomainH2`).  Proposition 3.4:

* `isRealisation_of_one` — `D₀ ⊆ D(A_H)` for every coefficient `c ∈ C¹`, with
  `A_H v = c A_{0,H}v - c' ∂ₓv`;
* `domain_eq` — `D(A_H(t)) = D₀` for every `t`;
* `exists_bound_on_D₀` — for each `t`, `A_H(t) ∈ L(D₀, H)` for the graph norm
  `‖v‖_V + ‖A_{0,H} v‖_H` of `D₀`;
* `not_uniform_bound_on_D₀` — `sup_{t ∈ [0,1]} ‖A_H(t)‖_{L(D₀,H)} = ∞`: no constant bounds
  `‖A_H(t)v‖` by the graph norm for all `t ∈ [0,1]`, witnessed by the fixed profile
  `φ = sin² ∈ D₀`.

(The norm of `V` here is the graph norm `(‖v‖² + ‖∂ₓv‖²)^{1/2}`; the paper uses `‖∂ₓv‖`, an
equivalent norm, which does not affect either statement.)
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped InnerProductSpace ComplexConjugate ENNReal

variable (D : Cutoffs)

/-- `v ∈ D(A_H(t))` with `A_H(t)v = h`, for the coefficient `𝔞`. -/
def IsRealisation (𝔞 : ℝ → ℝ → ℝ) (t : ℝ) (v : H10 Iπ) (h : L2 Iπ) : Prop :=
  ∀ w : H10 Iπ, form Iπ 𝔞 t v w = ofL2 Iπ h w

/-- The constant coefficient `1` (the Dirichlet Laplacian `A_{0,H}`). -/
def one : ℝ → ℝ → ℝ := fun _ _ => 1

/-! ### Multiplication by bounded continuous functions -/

theorem memLp_mul_L2 {c : ℝ → ℝ} (hc : Continuous c) (F : L2 Iπ) :
    MemLp (fun x => (c x : ℂ) * F x) 2 (volume.restrict Iπ) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc 0 π)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ((Lp.memLp F).const_mul (M : ℂ)).of_le ?_ ?_
  · exact ((continuous_cplx hc).aestronglyMeasurable).mul (Lp.memLp F).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [norm_mul, norm_mul, Complex.norm_real]
    have hMx := hM x (Ioo_subset_Icc_self hx)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hMx
    rw [Complex.norm_real, Real.norm_of_nonneg hM0]
    gcongr

/-- The product `c F ∈ L²` of a bounded continuous real function and `F ∈ L²`. -/
def mulL2 (c : ℝ → ℝ) (hc : Continuous c) (F : L2 Iπ) : L2 Iπ :=
  toL2 Iπ _ (memLp_mul_L2 hc F)

theorem coe_mulL2 {c : ℝ → ℝ} (hc : Continuous c) (F : L2 Iπ) :
    ⇑(mulL2 c hc F) =ᵐ[volume.restrict Iπ] fun x => (c x : ℂ) * F x := coe_toL2 _ _

theorem norm_mulL2_le {c : ℝ → ℝ} (hc : Continuous c) {M : ℝ} (hM : ∀ x ∈ Icc 0 π, |c x| ≤ M)
    (F : L2 Iπ) : ‖mulL2 c hc F‖ ≤ M * ‖F‖ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, pi_pos.le⟩)
  have h := Lp.norm_le_mul_norm_of_ae_le_mul (c := M) (f := mulL2 c hc F) (g := F) ?_
  · exact h
  · filter_upwards [coe_mulL2 hc F, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact hM x (Ioo_subset_Icc_self hxI)

theorem inner_mulL2_left {c : ℝ → ℝ} (hc : Continuous c) (F G : L2 Iπ) :
    ⟪mulL2 c hc F, G⟫_ℂ = ⟪F, mulL2 c hc G⟫_ℂ := by
  rw [inner_L2_eq, inner_L2_eq]
  refine integral_congr_ae ?_
  filter_upwards [coe_mulL2 hc F, coe_mulL2 hc G] with x h1 h2
  rw [h1, h2, map_mul, Complex.conj_ofReal]
  ring

/-! ### Test functions times `C¹` coefficients -/

theorem IsTestFun.mul_left {φ : ℝ → ℂ} (hφ : IsTestFun Iπ φ) {c c' : ℝ → ℝ}
    (hc : ∀ x, HasDerivAt c (c' x) x) (hc' : Continuous c') :
    IsTestFun Iπ (fun x => (c x : ℂ) * φ x) where
  contDiff := by
    have hcc : ContDiff ℝ 1 (fun x => (c x : ℂ)) := by
      rw [contDiff_one_iff_deriv]
      refine ⟨fun x => ((hc x).ofReal_comp).differentiableAt, ?_⟩
      have : deriv (fun x => (c x : ℂ)) = fun x => (c' x : ℂ) :=
        funext fun x => ((hc x).ofReal_comp).deriv
      rw [this]; exact continuous_cplx hc'
    exact hcc.mul hφ.contDiff
  hasCompactSupport := hφ.hasCompactSupport.mul_left
  tsupport_subset := (tsupport_mul_subset_right).trans hφ.tsupport_subset

theorem IsTestFun.deriv_mul_left {φ : ℝ → ℂ} (hφ : IsTestFun Iπ φ) {c c' : ℝ → ℝ}
    (hc : ∀ x, HasDerivAt c (c' x) x) (x : ℝ) :
    deriv (fun x => (c x : ℂ) * φ x) x = (c' x : ℂ) * φ x + (c x : ℂ) * deriv φ x :=
  (((hc x).ofReal_comp).mul (hφ.hasDerivAt x)).deriv

/-- `val` of the test element `c φ`. -/
theorem val_ofTest_mul {φ : ℝ → ℂ} (hφ : IsTestFun Iπ φ) {c c' : ℝ → ℝ}
    (hc : ∀ x, HasDerivAt c (c' x) x) (hc' : Continuous c') (hcc : Continuous c) :
    val Iπ (ofTest (hφ.mul_left hc hc')) = mulL2 c hcc (toL2 Iπ φ hφ.memLp) := by
  apply Lp.ext
  filter_upwards [val_ofTest (hφ.mul_left hc hc'), coe_mulL2 hcc (toL2 Iπ φ hφ.memLp),
    coe_toL2 φ hφ.memLp] with x h1 h2 h3
  rw [h1, h2, h3]

/-- `dx` of the test element `c φ` is `c' φ + c φ'`. -/
theorem dx_ofTest_mul {φ : ℝ → ℂ} (hφ : IsTestFun Iπ φ) {c c' : ℝ → ℝ}
    (hc : ∀ x, HasDerivAt c (c' x) x) (hc' : Continuous c') (hcc : Continuous c) :
    dx Iπ (ofTest (hφ.mul_left hc hc'))
      = mulL2 c' hc' (toL2 Iπ φ hφ.memLp) + mulL2 c hcc (toL2 Iπ (deriv φ) hφ.memLp_deriv) := by
  apply Lp.ext
  filter_upwards [dx_ofTest (hφ.mul_left hc hc'), coe_mulL2 hc' (toL2 Iπ φ hφ.memLp),
    coe_mulL2 hcc (toL2 Iπ (deriv φ) hφ.memLp_deriv), coe_toL2 φ hφ.memLp,
    coe_toL2 (deriv φ) hφ.memLp_deriv, Lp.coeFn_add (mulL2 c' hc' (toL2 Iπ φ hφ.memLp))
      (mulL2 c hcc (toL2 Iπ (deriv φ) hφ.memLp_deriv))] with x h1 h2 h3 h4 h5 h6
  rw [h1, h6, Pi.add_apply, h2, h3, h4, h5, hφ.deriv_mul_left hc x]

/-- The form as an inner product: `𝔞(t)[v,w] = ⟨∂ₓw, 𝔞(t)∂ₓv⟩`. -/
theorem formH_eq_inner {c : ℝ → ℝ → ℝ} {t : ℝ} (hc : Continuous (c t)) (v w : H10 Iπ) :
    form Iπ c t v w = ⟪dx Iπ w, mulL2 (c t) hc (dx Iπ v)⟫_ℂ := by
  rw [inner_L2_eq, form]
  refine integral_congr_ae ?_
  filter_upwards [coe_mulL2 hc (dx Iπ v)] with x hx
  rw [hx]
  ring

/-- A realisation identity holds on `H¹₀` as soon as it holds on the test functions. -/
theorem isRealisation_of_test {c : ℝ → ℝ → ℝ} {t : ℝ} (hc : Continuous (c t)) (v : H10 Iπ)
    (h : L2 Iπ)
    (htest : ∀ φ : ℝ → ℂ, (hφ : IsTestFun Iπ φ) →
      ⟪toL2 Iπ (deriv φ) hφ.memLp_deriv, mulL2 (c t) hc (dx Iπ v)⟫_ℂ
        = ⟪toL2 Iπ φ hφ.memLp, h⟫_ℂ) :
    IsRealisation c t v h := by
  intro w
  set Λ : WithLp 2 (L2 Iπ × L2 Iπ) →L⋆[ℂ] ℂ :=
    (innerSLFlip ℂ (mulL2 (c t) hc (dx Iπ v))).comp (WithLp.sndL 2 ℂ (L2 Iπ) (L2 Iπ)) -
      (innerSLFlip ℂ h).comp (WithLp.fstL 2 ℂ (L2 Iπ) (L2 Iπ)) with hΛ
  have h0 : ∀ p ∈ testGraph Iπ, Λ p = 0 := by
    rintro p ⟨φ, hφc, hcs, hsub, h1, h2⟩
    have hφ : IsTestFun Iπ φ := ⟨hφc, hcs, hsub⟩
    have e1 : (WithLp.ofLp p).1 = toL2 Iπ φ hφ.memLp := by
      apply Lp.ext; filter_upwards [h1, coe_toL2 φ hφ.memLp] with x hx hx'; rw [hx, hx']
    have e2 : (WithLp.ofLp p).2 = toL2 Iπ (deriv φ) hφ.memLp_deriv := by
      apply Lp.ext
      filter_upwards [h2, coe_toL2 (deriv φ) hφ.memLp_deriv] with x hx hx'; rw [hx, hx']
    simp only [hΛ, sub_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, innerSLFlip_apply_apply, WithLp.sndL_apply, WithLp.fstL_apply]
    change ⟪(WithLp.ofLp p).2, _⟫_ℂ - ⟪(WithLp.ofLp p).1, h⟫_ℂ = 0
    rw [e1, e2, htest φ hφ, sub_self]
  have := eq_zero_of_testGraph Λ h0 w
  simp only [hΛ, sub_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, innerSLFlip_apply_apply, WithLp.sndL_apply, WithLp.fstL_apply] at this
  rw [formH_eq_inner hc]
  exact sub_eq_zero.1 this

theorem mulL2_congr {c d : ℝ → ℝ} (hc : Continuous c) (hd : Continuous d)
    (e : ∀ x ∈ Iπ, c x = d x) (F : L2 Iπ) : mulL2 c hc F = mulL2 d hd F := by
  apply Lp.ext
  filter_upwards [coe_mulL2 hc F, coe_mulL2 hd F, ae_restrict_mem measurableSet_Ioo] with x h1 h2 hx
  rw [h1, h2, e x hx]

theorem mulL2_one (F : L2 Iπ) : mulL2 (fun _ => 1) continuous_const F = F := by
  apply Lp.ext
  filter_upwards [coe_mulL2 (c := fun _ => (1 : ℝ)) continuous_const F] with x h
  rw [h]; simp

theorem mulL2_mulL2 {c d : ℝ → ℝ} (hc : Continuous c) (hd : Continuous d) (F : L2 Iπ) :
    mulL2 c hc (mulL2 d hd F) = mulL2 (fun x => c x * d x) (hc.mul hd) F := by
  apply Lp.ext
  filter_upwards [coe_mulL2 hc (mulL2 d hd F), coe_mulL2 hd F,
    coe_mulL2 (c := fun x => c x * d x) (hc.mul hd) F] with x h1 h2 h3
  rw [h1, h3, h2, Complex.ofReal_mul]
  ring

theorem continuous_one0 : Continuous (one 0) := continuous_const

/-- `mulL2_one` for the coefficient `one` at time `0`. -/
theorem mulL2_one_zero (hc : Continuous (one 0)) (F : L2 Iπ) : mulL2 (one 0) hc F = F :=
  mulL2_one F

theorem formH_one_eq (v w : H10 Iπ) :
    form Iπ one 0 v w = ⟪dx Iπ w, dx Iπ v⟫_ℂ := by
  rw [formH_eq_inner (c := one) (t := 0) continuous_one0, mulL2_one_zero]

theorem isRealisation_unique {c : ℝ → ℝ → ℝ} {t : ℝ} {v : H10 Iπ} {h₁ h₂ : L2 Iπ}
    (h₁r : IsRealisation c t v h₁) (h₂r : IsRealisation c t v h₂) : h₁ = h₂ := by
  apply ofL2_injective isOpen_Ioo
  ext w
  rw [← h₁r w, ← h₂r w]

/-! ### The coefficient at a fixed time and its reciprocal -/

theorem a_pos {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t x : ℝ) : 0 < a D ε t x :=
  lt_of_lt_of_le (by norm_num) (a_ge D hε0 hε1 t x)

theorem continuous_a'_x (ε t : ℝ) : Continuous fun x => ε * βx D t x :=
  continuous_const.mul (continuous_βx_x D t)

theorem hasDerivAt_ainv {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t x : ℝ) :
    HasDerivAt (fun x => 1 / a D ε t x) (-(ε * βx D t x) / (a D ε t x) ^ 2) x := by
  have h := (hasDerivAt_a_x D ε t x).inv (a_pos D hε0 hε1 t x).ne'
  simp only [one_div]
  convert h using 1

theorem continuous_ainv {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : ℝ) :
    Continuous fun x => 1 / a D ε t x :=
  continuous_const.div (continuous_a_x D ε t) fun x => (a_pos D hε0 hε1 t x).ne'

theorem continuous_ainv' {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : ℝ) :
    Continuous fun x => -(ε * βx D t x) / (a D ε t x) ^ 2 :=
  ((continuous_a'_x D ε t).neg).div ((continuous_a_x D ε t).pow 2) fun x =>
    pow_ne_zero 2 (a_pos D hε0 hε1 t x).ne'

/-- `D₀ ⊆ D(A_H(t))` for a coefficient `c(t,·) ∈ C¹` with continuous derivative `c'`:
`A_H(t)v = c(t) A_{0,H}v - c' ∂ₓv`. -/
theorem isRealisation_of_one {c : ℝ → ℝ → ℝ} {t : ℝ} {c' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt (c t) (c' x) x) (hc' : Continuous c') (hc : Continuous (c t))
    {v : H10 Iπ} {g : L2 Iπ} (hg : IsRealisation one 0 v g) :
    IsRealisation c t v (mulL2 (c t) hc g - mulL2 c' hc' (dx Iπ v)) := by
  refine isRealisation_of_test hc v _ fun φ hφ => ?_
  have hdx := dx_ofTest_mul hφ hd hc' hc
  have hval := val_ofTest_mul hφ hd hc' hc
  have key := hg (ofTest (hφ.mul_left hd hc'))
  rw [formH_eq_inner (c := one) (t := 0) continuous_one0, mulL2_one_zero, hdx] at key
  change _ = ⟪val Iπ _, g⟫_ℂ at key
  rw [hval, inner_add_left] at key
  rw [← inner_mulL2_left, inner_sub_right, ← inner_mulL2_left hc, ← inner_mulL2_left hc']
  linear_combination key

/-- `D₀ ⊆ D(A_H(t))`, with `A_H(t)v = 𝔞 A_{0,H}v - 𝔞' ∂ₓv`. -/
theorem isRealisation_a_of_one (ε t : ℝ) {v : H10 Iπ} {g : L2 Iπ}
    (hg : IsRealisation one 0 v g) :
    IsRealisation (a D ε) t v (mulL2 (fun x => a D ε t x) (continuous_a_x D ε t) g
      - mulL2 (fun x => ε * βx D t x) (continuous_a'_x D ε t) (dx Iπ v)) :=
  isRealisation_of_one (hasDerivAt_a_x D ε t) (continuous_a'_x D ε t) (continuous_a_x D ε t) hg

/-- `D(A_H(t)) ⊆ D₀`. -/
theorem isRealisation_one_of_a {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : ℝ) {v : H10 Iπ}
    {h : L2 Iπ} (hh : IsRealisation (a D ε) t v h) :
    IsRealisation one 0 v (mulL2 (fun x => 1 / a D ε t x) (continuous_ainv D hε0 hε1 t) h
      - mulL2 (fun x => -(ε * βx D t x) / (a D ε t x) ^ 2 * a D ε t x)
          ((continuous_ainv' D hε0 hε1 t).mul (continuous_a_x D ε t)) (dx Iπ v)) := by
  refine isRealisation_of_test (c := one) (t := 0) continuous_one0 v _ fun φ hφ => ?_
  rw [mulL2_one_zero]
  have hb := hasDerivAt_ainv D hε0 hε1 t
  have hdx := dx_ofTest_mul hφ hb (continuous_ainv' D hε0 hε1 t) (continuous_ainv D hε0 hε1 t)
  have hval := val_ofTest_mul hφ hb (continuous_ainv' D hε0 hε1 t) (continuous_ainv D hε0 hε1 t)
  have key := hh (ofTest (hφ.mul_left hb (continuous_ainv' D hε0 hε1 t)))
  rw [formH_eq_inner (continuous_a_x D ε t), hdx] at key
  change _ = ⟪val Iπ _, h⟫_ℂ at key
  rw [hval, inner_add_left, inner_mulL2_left, inner_mulL2_left, inner_mulL2_left,
    mulL2_mulL2, mulL2_mulL2] at key
  have e1 : mulL2 (fun x => 1 / a D ε t x * a D ε t x)
      ((continuous_ainv D hε0 hε1 t).mul (continuous_a_x D ε t)) (dx Iπ v) = dx Iπ v := by
    rw [mulL2_congr _ continuous_const (fun x _ => by
      rw [one_div, inv_mul_cancel₀ (a_pos D hε0 hε1 t x).ne']), mulL2_one]
  rw [e1] at key
  rw [inner_sub_right]
  linear_combination key

/-- `D(A_H(t)) = D₀`. -/
theorem domain_eq {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : ℝ) (v : H10 Iπ) :
    (∃ h, IsRealisation (a D ε) t v h) ↔ (∃ g, IsRealisation one 0 v g) :=
  ⟨fun ⟨_, hh⟩ => ⟨_, isRealisation_one_of_a D hε0 hε1 t hh⟩,
    fun ⟨_, hg⟩ => ⟨_, isRealisation_a_of_one D ε t hg⟩⟩

/-- For fixed `t`, `A_H(t) ∈ L(D₀, H)`: `‖A_H(t)v‖ ≤ C (‖v‖_V + ‖A_{0,H}v‖_H)`. -/
theorem exists_bound_on_D₀ {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : ℝ) :
    ∃ C : ℝ, ∀ (v : H10 Iπ) (h g : L2 Iπ),
      IsRealisation (a D ε) t v h → IsRealisation one 0 v g → ‖h‖ ≤ C * (‖v‖ + ‖g‖) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc 0 π)).exists_bound_of_continuousOn
    (continuous_a'_x D ε t).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, pi_pos.le⟩)
  refine ⟨max (481 / 480) M, fun v h g hh hg => ?_⟩
  rw [isRealisation_unique hh (isRealisation_a_of_one D ε t hg)]
  have h1 : ‖mulL2 (fun x => a D ε t x) (continuous_a_x D ε t) g‖ ≤ 481 / 480 * ‖g‖ :=
    norm_mulL2_le _ (fun x _ => by
      rw [abs_of_pos (a_pos D hε0 hε1 t x)]; exact a_le D hε0 hε1 t x) g
  have h2 : ‖mulL2 (fun x => ε * βx D t x) (continuous_a'_x D ε t) (dx Iπ v)‖ ≤ M * ‖v‖ :=
    (norm_mulL2_le _ (fun x hx => by rw [← Real.norm_eq_abs]; exact hM x hx) _).trans
      (by gcongr; exact norm_dx_le v)
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ 481 / 480 * ‖g‖ + M * ‖v‖ := add_le_add h1 h2
    _ ≤ max (481 / 480) M * ‖g‖ + max (481 / 480) M * ‖v‖ := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = max (481 / 480) M * (‖v‖ + ‖g‖) := by ring

/-! ### No uniform bound on `D₀` -/

theorem isC1Vanish_φ : IsC1Vanish φ φ' where
  hasDerivAt := hasDerivAt_φ
  cont' := continuous_iff_continuousAt.2 fun x => (hasDerivAt_φ' x).continuousAt
  zero_left := by simp [φ]
  zero_right := by simp [φ]
  zero_left' := φ'_zero
  zero_right' := φ'_pi

/-- The fixed profile `φ = sin² ∈ D₀`. -/
def φV : H10 Iπ := ofC1Z isC1Vanish_φ

theorem isRealisation_one_φV :
    IsRealisation one 0 φV (toL2c (fun x => -φ'' x) continuous_φ''.neg) := by
  intro w
  have hG : ∀ x, HasDerivAt (fun x => (φ' x : ℂ)) (φ'' x : ℂ) x :=
    fun x => (hasDerivAt_φ' x).ofReal_comp
  have key := inner_dx_eq hG (continuous_cplx continuous_φ'')
    (memLp_Ioo_of_continuous (a := 0) (b := π) (continuous_cplx isC1Vanish_φ.cont'))
    (memLp_Ioo_of_continuous (a := 0) (b := π) (continuous_cplx continuous_φ'')) w
  rw [formH_one_eq, φV, dx_ofC1Z]
  change ⟪dx Iπ w, toL2c φ' _⟫_ℂ = ⟪val Iπ w, _⟫_ℂ
  have e : toL2c (fun x => -φ'' x) continuous_φ''.neg = -toL2c φ'' continuous_φ'' := by
    apply Lp.ext
    filter_upwards [coe_toL2c (g := fun x => -φ'' x) continuous_φ''.neg,
      coe_toL2c continuous_φ'', Lp.coeFn_neg (toL2c φ'' continuous_φ'')] with x h1 h2 h3
    rw [h1, h3, Pi.neg_apply, h2, Complex.ofReal_neg]
  rw [e, inner_neg_right]
  exact key

theorem isRealisation_a_φV (ε t : ℝ) :
    IsRealisation (a D ε) t φV (toL2c (Aφ D ε t) (by
      show Continuous fun x => -(ε * βx D t x * φ' x) - a D ε t x * φ'' x
      exact ((continuous_const.mul (continuous_βx_x D t)).mul isC1Vanish_φ.cont').neg.sub
        ((continuous_a_x D ε t).mul continuous_φ''))) := by
  intro w
  set G : ℝ → ℂ := fun x => ((a D ε t x * φ' x : ℝ) : ℂ) with hGdef
  set g : ℝ → ℂ := fun x => ((-(Aφ D ε t x) : ℝ) : ℂ) with hgdef
  have hG : ∀ x, HasDerivAt G (g x) x := fun x => (hasDerivAt_Aφ_flux D ε t x).ofReal_comp
  have hAc : Continuous fun x => Aφ D ε t x :=
    ((continuous_const.mul (continuous_βx_x D t)).mul isC1Vanish_φ.cont').neg.sub
      ((continuous_a_x D ε t).mul continuous_φ'')
  have hgc : Continuous g := continuous_cplx hAc.neg
  have hGc : Continuous G := continuous_cplx ((continuous_a_x D ε t).mul isC1Vanish_φ.cont')
  have hG2 := memLp_Ioo_of_continuous (a := 0) (b := π) hGc
  have hg2 := memLp_Ioo_of_continuous (a := 0) (b := π) hgc
  have key := inner_dx_eq hG hgc hG2 hg2 w
  have e1 : mulL2 (a D ε t) (continuous_a_x D ε t) (dx Iπ φV) = toL2 Iπ G hG2 := by
    apply Lp.ext
    rw [φV, dx_ofC1Z]
    filter_upwards [coe_mulL2 (continuous_a_x D ε t) (toL2c φ' isC1Vanish_φ.cont'),
      coe_toL2c isC1Vanish_φ.cont', coe_toL2 G hG2] with x h1 h2 h3
    rw [h1, h2, h3]
    simp only [hGdef, Complex.ofReal_mul]
  have e2 : toL2 Iπ g hg2 = -toL2c (Aφ D ε t) hAc := by
    apply Lp.ext
    filter_upwards [coe_toL2 g hg2, coe_toL2c hAc, Lp.coeFn_neg (toL2c (Aφ D ε t) hAc)]
      with x h1 h2 h3
    rw [h1, h3, Pi.neg_apply, h2]
    simp only [hgdef, Complex.ofReal_neg]
  rw [formH_eq_inner (continuous_a_x D ε t), e1, key, e2, inner_neg_right, neg_neg]
  rfl

theorem norm_toL2c_Aφ_sq (ε t : ℝ) (hc : Continuous fun x => Aφ D ε t x) :
    ‖toL2c (Aφ D ε t) hc‖ ^ 2 = normSq (Aφ D ε t) := norm_toL2c_sq hc

/-- **Proposition 3.4, second part**: `sup_{t ∈ [0,1]} ‖A_H(t)‖_{L(D₀,H)} = ∞`.  No constant `C`
bounds `‖A_H(t)v‖_H ≤ C (‖v‖_V + ‖A_{0,H}v‖_H)` on `D₀` for all `t ∈ [0,1]`. -/
theorem not_uniform_bound_on_D₀ {ε : ℝ} (hε : ε ≠ 0) :
    ¬ ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ (v : H10 Iπ) (h g : L2 Iπ),
      IsRealisation (a D ε) t v h → IsRealisation one 0 v g → ‖h‖ ≤ C * (‖v‖ + ‖g‖) := by
  rintro ⟨C, hC⟩
  set B := C * (‖φV‖ + ‖toL2c (fun x => -φ'' x) continuous_φ''.neg‖)
  obtain ⟨t, ht, hge⟩ := exists_normSq_Aφ_ge D hε (B ^ 2 + 1)
  have hAc : Continuous fun x => Aφ D ε t x :=
    ((continuous_const.mul (continuous_βx_x D t)).mul isC1Vanish_φ.cont').neg.sub
      ((continuous_a_x D ε t).mul continuous_φ'')
  have hbound : ‖toL2c (Aφ D ε t) hAc‖ ≤ B :=
    hC t ht φV _ _ (isRealisation_a_φV D ε t) isRealisation_one_φV
  have hn0 := norm_nonneg (toL2c (Aφ D ε t) hAc)
  rw [← norm_toL2c_Aφ_sq D ε t hAc] at hge
  nlinarith

end LionsC12
