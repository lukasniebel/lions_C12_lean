module

public import LionsC12.Spaces.Forms
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral

/-!
# The operator norm `‖𝒜(t) − 𝒜(s)‖_{L(V,V')}` of a coefficient increment

For a coefficient `𝔞 : ℝ → ℝ → ℝ` and the forms `𝔞(t)[v,w] = ⟨𝒜(t)v, w⟩_{V',V}` of
`LionsC12.Paper.Statement` on `V = H¹₀(U)` (with its graph norm), the operator norm of
`𝒜(t) − 𝒜(s) : V → V'` is

`‖𝒜(t) − 𝒜(s)‖_{L(V,V')} = sup_{v, w ≠ 0} |𝔞(t)[v,w] − 𝔞(s)[v,w]| / (‖v‖_V ‖w‖_V)`.

We record it as an `ℝ≥0∞`-valued supremum `formOpDist U 𝔞 t s` and prove

* `enorm_form_sub_le` — `|𝔞(t)[v,w] − 𝔞(s)[v,w]| ≤ ‖𝒜(t) − 𝒜(s)‖ ‖v‖ ‖w‖`;
* `formOpDist_le_ofReal` — conversely, a bound `|𝔞(t)[v,w] − 𝔞(s)[v,w]| ≤ C ‖v‖ ‖w‖` for all
  `v, w` gives `‖𝒜(t) − 𝒜(s)‖ ≤ C`;
* `formOpDist_le_eLpNorm`, `norm_form_sub_le_eLpNorm` —
  `‖𝒜(t) − 𝒜(s)‖_{L(V,V')} ≤ ‖𝔞(t) − 𝔞(s)‖_{L^∞(U)}` for bounded measurable coefficients;
* `exists_form_sub_ge` — for `U = (a,b)`, `x ↦ 𝔞(t,x) − 𝔞(s,x)` continuous, `x₀ ∈ (a,b)` and
  `c < |𝔞(t,x₀) − 𝔞(s,x₀)|`, there is `v ≠ 0` with `|𝔞(t)[v,v] − 𝔞(s)[v,v]| ≥ c ‖v‖²`.  The
  element `v` is a localised bump `v(x) = ψ((x − x₀)/h)` with `h` small; its graph norm is
  dominated by `‖∂ₓv‖`, since `‖v‖²_{L²} = h ∫ψ²` and `‖∂ₓv‖²_{L²} = h⁻¹ ∫ψ'²`; the same
  for every `c < ‖𝔞(t) − 𝔞(s)‖_{L^∞(a,b)}` (`exists_form_sub_ge_of_lt_eLpNorm`);
* `formOpDist_eq_eLpNorm` — hence, for continuous coefficients on an interval,
  `‖𝒜(t) − 𝒜(s)‖_{L(V,V')} = ‖𝔞(t) − 𝔞(s)‖_{L^∞(a,b)}`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate ContDiff

variable {U : Set ℝ}

/-! ### The operator norm of a difference of forms -/

/-- The operator norm `‖𝒜(t) − 𝒜(s)‖_{L(V,V')}` of the difference of the operators
`𝒜(t), 𝒜(s) : V → V'` defined by the forms `form U 𝔞 t`, `form U 𝔞 s` on `V = H¹₀(U)`:
the supremum of `|𝔞(t)[v,w] − 𝔞(s)[v,w]| / (‖v‖_V ‖w‖_V)` over `v, w ≠ 0`, in `ℝ≥0∞`. -/
def formOpDist (U : Set ℝ) (𝔞 : ℝ → ℝ → ℝ) (t s : ℝ) : ℝ≥0∞ :=
  ⨆ (v : H10 U) (_ : v ≠ 0) (w : H10 U) (_ : w ≠ 0),
    ‖form U 𝔞 t v w - form U 𝔞 s v w‖ₑ / (‖v‖ₑ * ‖w‖ₑ)

theorem form_zero_left (𝔞 : ℝ → ℝ → ℝ) (t : ℝ) (w : H10 U) : form U 𝔞 t 0 w = 0 := by
  unfold form
  refine integral_eq_zero_of_ae ?_
  have h : ⇑(dx U 0) =ᵐ[volume.restrict U] 0 := by
    rw [map_zero]; exact Lp.coeFn_zero _ _ _
  filter_upwards [h] with x hx
  rw [hx, Pi.zero_apply, mul_zero, zero_mul]

theorem form_zero_right (𝔞 : ℝ → ℝ → ℝ) (t : ℝ) (v : H10 U) : form U 𝔞 t v 0 = 0 := by
  unfold form
  refine integral_eq_zero_of_ae ?_
  have h : ⇑(dx U 0) =ᵐ[volume.restrict U] 0 := by
    rw [map_zero]; exact Lp.coeFn_zero _ _ _
  filter_upwards [h] with x hx
  rw [hx, Pi.zero_apply, map_zero, mul_zero]

theorem div_le_formOpDist (𝔞 : ℝ → ℝ → ℝ) (t s : ℝ) {v w : H10 U} (hv : v ≠ 0) (hw : w ≠ 0) :
    ‖form U 𝔞 t v w - form U 𝔞 s v w‖ₑ / (‖v‖ₑ * ‖w‖ₑ) ≤ formOpDist U 𝔞 t s :=
  le_iSup₂_of_le v hv (le_iSup₂_of_le w hw le_rfl)

/-- `|𝔞(t)[v,w] − 𝔞(s)[v,w]| ≤ ‖𝒜(t) − 𝒜(s)‖_{L(V,V')} ‖v‖ ‖w‖`. -/
theorem enorm_form_sub_le (𝔞 : ℝ → ℝ → ℝ) (t s : ℝ) (v w : H10 U) :
    ‖form U 𝔞 t v w - form U 𝔞 s v w‖ₑ ≤ formOpDist U 𝔞 t s * (‖v‖ₑ * ‖w‖ₑ) := by
  by_cases hv : v = 0
  · subst hv; simp [form_zero_left]
  by_cases hw : w = 0
  · subst hw; simp [form_zero_right]
  have hne : ‖v‖ₑ * ‖w‖ₑ ≠ 0 := mul_ne_zero (enorm_ne_zero.2 hv) (enorm_ne_zero.2 hw)
  have hnt : ‖v‖ₑ * ‖w‖ₑ ≠ ⊤ := ENNReal.mul_ne_top enorm_ne_top enorm_ne_top
  exact (ENNReal.div_le_iff hne hnt).1 (div_le_formOpDist 𝔞 t s hv hw)

/-- The real form of `enorm_form_sub_le`, for a finite operator norm. -/
theorem norm_form_sub_le {𝔞 : ℝ → ℝ → ℝ} {t s : ℝ} (h : formOpDist U 𝔞 t s ≠ ⊤)
    (v w : H10 U) :
    ‖form U 𝔞 t v w - form U 𝔞 s v w‖ ≤ (formOpDist U 𝔞 t s).toReal * ‖v‖ * ‖w‖ := by
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top h (ENNReal.mul_ne_top enorm_ne_top
    enorm_ne_top)) (enorm_form_sub_le 𝔞 t s v w)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_enorm, toReal_enorm, toReal_enorm] at this
  rw [mul_assoc]
  exact this

/-- A bound `|𝔞(t)[v,w] − 𝔞(s)[v,w]| ≤ C ‖v‖ ‖w‖` for all `v, w` bounds the operator norm. -/
theorem formOpDist_le_ofReal {𝔞 : ℝ → ℝ → ℝ} {t s C : ℝ}
    (h : ∀ v w : H10 U, ‖form U 𝔞 t v w - form U 𝔞 s v w‖ ≤ C * ‖v‖ * ‖w‖) :
    formOpDist U 𝔞 t s ≤ ENNReal.ofReal C := by
  refine iSup₂_le fun v hv => iSup₂_le fun w hw => ENNReal.div_le_of_le_mul ?_
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  rcases le_or_gt 0 C with hC | hC
  · rw [← ENNReal.ofReal_mul hC, ← mul_assoc]
    exact ENNReal.ofReal_le_ofReal (h v w)
  · exfalso
    have h1 : 0 < ‖v‖ := norm_pos_iff.2 hv
    have h2 : 0 < ‖w‖ := norm_pos_iff.2 hw
    have h3 : C * ‖v‖ * ‖w‖ < 0 := by
      have : 0 < ‖v‖ * ‖w‖ := mul_pos h1 h2
      nlinarith
    linarith [h v w, norm_nonneg (form U 𝔞 t v w - form U 𝔞 s v w)]

/-! ### The upper bound by the `L^∞`-norm of the coefficient increment -/

/-- The difference of two forms is the form of the difference of the coefficients. -/
theorem form_sub_form {𝔞 : ℝ → ℝ → ℝ} {t s Λ : ℝ} (ht : IsBoundedCoeff 𝔞 t Λ)
    (hs : IsBoundedCoeff 𝔞 s Λ) (v w : H10 U) :
    form U 𝔞 t v w - form U 𝔞 s v w =
      ∫ x in U, ((𝔞 t x - 𝔞 s x : ℝ) : ℂ) * dx U v x * conj (dx U w x) := by
  unfold form
  rw [← integral_sub (integrable_form_integrand ht v w) (integrable_form_integrand hs v w)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Complex.ofReal_sub]
  ring

/-- The form bound `|∫_U g ∂ₓv conj(∂ₓw)| ≤ C ‖∂ₓv‖ ‖∂ₓw‖` for an a.e. bound `|g| ≤ C`. -/
theorem norm_integral_coeff_le {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ᵐ x ∂(volume.restrict U), |g x| ≤ C) (v w : H10 U) :
    ‖∫ x in U, (g x : ℂ) * dx U v x * conj (dx U w x)‖ ≤ C * ‖dx U v‖ * ‖dx U w‖ := by
  calc ‖∫ x in U, (g x : ℂ) * dx U v x * conj (dx U w x)‖
      ≤ ∫ x in U, C * (‖dx U v x‖ * ‖dx U w x‖) := by
        refine norm_integral_le_of_norm_le ?_ ?_
        · refine ((L2.integrable_inner (𝕜 := ℂ) (dx U v) (dx U w)).norm.const_mul C).congr
            (Eventually.of_forall fun x => ?_)
          simp only [RCLike.inner_apply, norm_mul, RCLike.norm_conj]
          ring
        · filter_upwards [hg] with x hx
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj, mul_assoc]
          gcongr
    _ = C * ∫ x in U, ‖dx U v x‖ * ‖dx U w x‖ := integral_const_mul _ _
    _ ≤ C * (‖dx U v‖ * ‖dx U w‖) := by
        gcongr
        exact integral_norm_mul_norm_le_L2 _ _
    _ = C * ‖dx U v‖ * ‖dx U w‖ := by ring

/-- A real function is a.e. bounded by its (finite) `L^∞`-norm. -/
theorem ae_abs_le_eLpNorm_top {g : ℝ → ℝ} {μ : Measure ℝ} (hg : eLpNorm g ∞ μ ≠ ⊤) :
    ∀ᵐ x ∂μ, |g x| ≤ (eLpNorm g ∞ μ).toReal := by
  filter_upwards [ae_le_eLpNormEssSup (f := g) (μ := μ)] with x hx
  rw [← Real.norm_eq_abs, ← toReal_enorm]
  exact ENNReal.toReal_mono hg (hx.trans eLpNormEssSup_le_eLpNorm_top)

/-- The `L^∞`-norm of the increment of a bounded coefficient is finite. -/
theorem eLpNorm_coeff_sub_le {𝔞 : ℝ → ℝ → ℝ} {t s Λ : ℝ} (ht : IsBoundedCoeff 𝔞 t Λ)
    (hs : IsBoundedCoeff 𝔞 s Λ) :
    eLpNorm (fun x => 𝔞 t x - 𝔞 s x) ∞ (volume.restrict U) ≤ ENNReal.ofReal (2 * Λ) := by
  rw [eLpNorm_exponent_top (show Measurable fun x => 𝔞 t x - 𝔞 s x from
    ht.measurable.sub hs.measurable).aestronglyMeasurable]
  refine eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  have h1 := ht.bound x
  have h2 := hs.bound x
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith

theorem eLpNorm_coeff_sub_ne_top {𝔞 : ℝ → ℝ → ℝ} {t s Λ : ℝ} (ht : IsBoundedCoeff 𝔞 t Λ)
    (hs : IsBoundedCoeff 𝔞 s Λ) :
    eLpNorm (fun x => 𝔞 t x - 𝔞 s x) ∞ (volume.restrict U) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eLpNorm_coeff_sub_le ht hs)

/-- **`‖𝒜(t) − 𝒜(s)‖_{L(V,V')} ≤ ‖𝔞(t) − 𝔞(s)‖_{L^∞(U)}`** for bounded measurable
coefficients. -/
theorem formOpDist_le_eLpNorm {𝔞 : ℝ → ℝ → ℝ} {t s Λ : ℝ} (ht : IsBoundedCoeff 𝔞 t Λ)
    (hs : IsBoundedCoeff 𝔞 s Λ) :
    formOpDist U 𝔞 t s ≤ eLpNorm (fun x => 𝔞 t x - 𝔞 s x) ∞ (volume.restrict U) := by
  have hEt := eLpNorm_coeff_sub_ne_top (U := U) ht hs
  rw [← ENNReal.ofReal_toReal hEt]
  refine formOpDist_le_ofReal fun v w => ?_
  rw [form_sub_form ht hs]
  calc _ ≤ (eLpNorm (fun x => 𝔞 t x - 𝔞 s x) ∞ (volume.restrict U)).toReal * ‖dx U v‖ *
        ‖dx U w‖ := norm_integral_coeff_le ENNReal.toReal_nonneg (ae_abs_le_eLpNorm_top hEt) v w
    _ ≤ _ := by gcongr <;> [exact norm_dx_le v; exact norm_dx_le w]

/-- **`|𝔞(t)[v,w] − 𝔞(s)[v,w]| ≤ ‖𝔞(t) − 𝔞(s)‖_{L^∞(U)} ‖v‖_V ‖w‖_V`** for bounded measurable
coefficients. -/
theorem norm_form_sub_le_eLpNorm {𝔞 : ℝ → ℝ → ℝ} {t s Λ : ℝ} (ht : IsBoundedCoeff 𝔞 t Λ)
    (hs : IsBoundedCoeff 𝔞 s Λ) (v w : H10 U) :
    ‖form U 𝔞 t v w - form U 𝔞 s v w‖ ≤
      (eLpNorm (fun x => 𝔞 t x - 𝔞 s x) ∞ (volume.restrict U)).toReal * ‖v‖ * ‖w‖ := by
  have hEt := eLpNorm_coeff_sub_ne_top (U := U) ht hs
  rw [form_sub_form ht hs]
  calc _ ≤ (eLpNorm (fun x => 𝔞 t x - 𝔞 s x) ∞ (volume.restrict U)).toReal * ‖dx U v‖ *
        ‖dx U w‖ := norm_integral_coeff_le ENNReal.toReal_nonneg (ae_abs_le_eLpNorm_top hEt) v w
    _ ≤ _ := by gcongr <;> [exact norm_dx_le v; exact norm_dx_le w]

/-! ### Localised bumps -/

/-- The fixed bump `ψ`: smooth, `ψ = 1` on `[-1/2, 1/2]`, `0 ≤ ψ ≤ 1`, supported in `(-1,1)`. -/
def bumpψ : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

theorem bumpψ_zero : bumpψ 0 = 1 :=
  bumpψ.one_of_mem_closedBall (Metric.mem_closedBall_self (by simp [bumpψ]))

theorem bumpψ_eq_zero {y : ℝ} (hy : 1 < |y|) : bumpψ y = 0 := by
  refine Function.notMem_support.1 fun h => ?_
  rw [bumpψ.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at h
  simp only [bumpψ] at h
  linarith

theorem deriv_bumpψ_eq_zero {y : ℝ} (hy : 1 < |y|) : deriv bumpψ y = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun h => ?_
  have h' := tsupport_deriv_subset h
  rw [bumpψ.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, sub_zero] at h'
  simp only [bumpψ] at h'
  linarith

theorem abs_le_of_deriv_bumpψ_ne_zero {y : ℝ} (hy : deriv bumpψ y ≠ 0) : |y| ≤ 1 := by
  by_contra h
  exact hy (deriv_bumpψ_eq_zero (not_le.1 h))

theorem contDiff_bumpψ : ContDiff ℝ 1 bumpψ := bumpψ.contDiff

theorem continuous_deriv_bumpψ : Continuous (deriv bumpψ) :=
  contDiff_bumpψ.continuous_deriv_one

theorem hasDerivAt_bumpψ (y : ℝ) : HasDerivAt bumpψ (deriv bumpψ y) y :=
  ((contDiff_bumpψ.differentiable one_ne_zero) y).hasDerivAt

/-- `A = ∫ ψ²`. -/
def bumpA : ℝ := ∫ y, bumpψ y ^ 2

/-- `B = ∫ ψ'²`. -/
def bumpB : ℝ := ∫ y, deriv bumpψ y ^ 2

theorem bumpA_nonneg : 0 ≤ bumpA := integral_nonneg fun _ => sq_nonneg _

theorem bumpB_pos : 0 < bumpB := by
  have hex : ∃ y, deriv bumpψ y ≠ 0 := by
    by_contra h
    push Not at h
    have := is_const_of_deriv_eq_zero (contDiff_bumpψ.differentiable one_ne_zero) h 0 2
    rw [bumpψ_zero, bumpψ_eq_zero (by norm_num)] at this
    exact one_ne_zero this
  obtain ⟨y, hy⟩ := hex
  have hcs : HasCompactSupport (fun y => deriv bumpψ y ^ 2) :=
    bumpψ.hasCompactSupport.deriv.comp_left (g := fun z : ℝ => z ^ 2) (by norm_num)
  exact (continuous_deriv_bumpψ.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero hcs
    (fun z => sq_nonneg _) (pow_ne_zero 2 hy)

/-- `∫ F((x − x₀)/h) dx = h ∫ F` for `h > 0`. -/
theorem integral_comp_affine {F : ℝ → ℝ} (x₀ : ℝ) {h : ℝ} (hh : 0 < h) :
    ∫ x, F ((x - x₀) / h) = h * ∫ y, F y := by
  rw [integral_sub_right_eq_self (fun x => F (x / h)) x₀, Measure.integral_comp_div,
    abs_of_pos hh, smul_eq_mul]

/-- The localised bump `ψ((x − x₀)/h)`, complex-valued. -/
def bumpAt (x₀ h : ℝ) (x : ℝ) : ℂ := ((bumpψ ((x - x₀) / h) : ℝ) : ℂ)

theorem hasDerivAt_bumpAt (x₀ h x : ℝ) :
    HasDerivAt (bumpAt x₀ h) (((deriv bumpψ ((x - x₀) / h)) / h : ℝ) : ℂ) x := by
  have hin : HasDerivAt (fun x : ℝ => (x - x₀) / h) (1 / h) x :=
    ((hasDerivAt_id x).sub_const x₀).div_const h
  have := ((hasDerivAt_bumpψ ((x - x₀) / h)).comp x hin).ofReal_comp
  rw [mul_one_div] at this
  exact this

theorem deriv_bumpAt (x₀ h x : ℝ) :
    deriv (bumpAt x₀ h) x = (((deriv bumpψ ((x - x₀) / h)) / h : ℝ) : ℂ) :=
  (hasDerivAt_bumpAt x₀ h x).deriv

theorem contDiff_bumpAt (x₀ h : ℝ) : ContDiff ℝ 1 (bumpAt x₀ h) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_bumpψ.comp (by fun_prop))

theorem bumpAt_eq_zero {x₀ h x : ℝ} (hh : 0 < h) (hx : h < |x - x₀|) : bumpAt x₀ h x = 0 := by
  unfold bumpAt
  rw [bumpψ_eq_zero, Complex.ofReal_zero]
  rw [abs_div, abs_of_pos hh, one_lt_div hh]
  exact hx

theorem deriv_bumpψ_comp_eq_zero {x₀ h x : ℝ} (hh : 0 < h) (hx : h < |x - x₀|) :
    deriv bumpψ ((x - x₀) / h) = 0 := by
  rw [deriv_bumpψ_eq_zero]
  rw [abs_div, abs_of_pos hh, one_lt_div hh]
  exact hx

/-- The localised bump as an element of `H¹₀((a,b))`, for `(x₀ − h, x₀ + h)` compactly inside
`(a,b)`. -/
def bumpVec {a b : ℝ} (hab : a < b) (x₀ h : ℝ) (hh : 0 < h) (ha : a < x₀ - h)
    (hb : x₀ + h < b) : H10 (Ioo a b) :=
  ofC1Ioo hab (contDiff_bumpAt x₀ h) fun x hx => bumpAt_eq_zero hh (by
    simp only [mem_Ioo, not_and_or, not_lt] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith)

/-- `‖f‖²_{L²(U)} = ∫_U ‖f‖²`. -/
theorem norm_sq_L2 (f : L2 U) : ‖f‖ ^ 2 = ∫ x in U, ‖f x‖ ^ 2 := by
  have := (Lp.memLp f).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
  rw [Lp.norm_def, this, ENNReal.toReal_ofReal (by positivity)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

section bumpVec

variable {a b : ℝ} (hab : a < b) {x₀ h : ℝ} (hh : 0 < h) (ha : a < x₀ - h) (hb : x₀ + h < b)
include hab hh ha hb

omit hab in
/-- Outside `(a,b)`, the bump is at distance `> h` from its centre. -/
theorem lt_abs_of_notMem_Ioo {x : ℝ} (hx : x ∉ Ioo a b) : h < |x - x₀| := by
  simp only [mem_Ioo, not_and_or, not_lt] at hx
  rcases hx with hx | hx
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem norm_val_bumpVec_sq : ‖val (Ioo a b) (bumpVec hab x₀ h hh ha hb)‖ ^ 2 = h * bumpA := by
  rw [norm_sq_L2]
  have e1 : ∫ x in Ioo a b, ‖val (Ioo a b) (bumpVec hab x₀ h hh ha hb) x‖ ^ 2
      = ∫ x in Ioo a b, bumpψ ((x - x₀) / h) ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [val_ofC1Ioo hab (contDiff_bumpAt x₀ h) _] with x hx
    rw [show bumpVec hab x₀ h hh ha hb = ofC1Ioo hab (contDiff_bumpAt x₀ h) _ from rfl, hx]
    simp only [bumpAt, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [e1, setIntegral_eq_integral_of_forall_compl_eq_zero,
    integral_comp_affine (F := fun y => bumpψ y ^ 2) x₀ hh]
  · rfl
  · intro x hx
    rw [bumpψ_eq_zero, zero_pow two_ne_zero]
    rw [abs_div, abs_of_pos hh, one_lt_div hh]
    exact lt_abs_of_notMem_Ioo hh ha hb hx

/-- The squared derivative `|∂ₓ ψ((x − x₀)/h)|² = ψ'((x − x₀)/h)² / h²`. -/
def bumpG (x₀ h : ℝ) (x : ℝ) : ℝ := (deriv bumpψ ((x - x₀) / h) / h) ^ 2

omit hab ha hb in
theorem integral_bumpG : ∫ x, bumpG x₀ h x = bumpB / h := by
  have e : ∀ x, bumpG x₀ h x = (1 / h ^ 2) * deriv bumpψ ((x - x₀) / h) ^ 2 := by
    intro x; unfold bumpG; rw [div_pow]; ring
  simp_rw [e]
  rw [integral_const_mul, integral_comp_affine (F := fun y => deriv bumpψ y ^ 2) x₀ hh]
  unfold bumpB
  field_simp

omit hab in
theorem bumpG_eq_zero {x : ℝ} (hx : x ∉ Ioo a b) : bumpG x₀ h x = 0 := by
  unfold bumpG
  rw [deriv_bumpψ_comp_eq_zero hh (lt_abs_of_notMem_Ioo hh ha hb hx), zero_div,
    zero_pow two_ne_zero]

omit hab ha hb in
theorem abs_sub_le_of_bumpG_ne_zero {x : ℝ} (hx : bumpG x₀ h x ≠ 0) : |x - x₀| ≤ h := by
  have hd : deriv bumpψ ((x - x₀) / h) ≠ 0 := by
    intro h0; apply hx; unfold bumpG; rw [h0, zero_div, zero_pow two_ne_zero]
  have := abs_le_of_deriv_bumpψ_ne_zero hd
  rwa [abs_div, abs_of_pos hh, div_le_one hh] at this

omit hab hh ha hb in
theorem continuous_bumpG : Continuous (bumpG x₀ h) := by
  unfold bumpG
  exact ((continuous_deriv_bumpψ.comp (by fun_prop)).div_const h).pow 2

omit hab ha hb in
theorem hasCompactSupport_bumpG : HasCompactSupport (bumpG x₀ h) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := x₀ - h) (b := x₀ + h)) fun x hx => ?_
  by_contra hne
  have := abs_sub_le_of_bumpG_ne_zero hh hne
  rw [abs_le] at this
  exact hx ⟨by linarith [this.1], by linarith [this.2]⟩

theorem norm_dx_bumpVec_sq : ‖dx (Ioo a b) (bumpVec hab x₀ h hh ha hb)‖ ^ 2 = bumpB / h := by
  rw [norm_sq_L2]
  have e1 : ∫ x in Ioo a b, ‖dx (Ioo a b) (bumpVec hab x₀ h hh ha hb) x‖ ^ 2
      = ∫ x in Ioo a b, bumpG x₀ h x := by
    refine integral_congr_ae ?_
    filter_upwards [dx_ofC1Ioo hab (contDiff_bumpAt x₀ h) _] with x hx
    rw [show bumpVec hab x₀ h hh ha hb = ofC1Ioo hab (contDiff_bumpAt x₀ h) _ from rfl, hx,
      deriv_bumpAt]
    simp only [bumpG, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [e1, setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => bumpG_eq_zero hh ha hb hx),
    integral_bumpG hh]

theorem norm_bumpVec_sq :
    ‖bumpVec hab x₀ h hh ha hb‖ ^ 2 = (h ^ 2 * bumpA + bumpB) / h := by
  rw [norm_sq_H10, norm_val_bumpVec_sq, norm_dx_bumpVec_sq]
  field_simp

theorem bumpVec_ne_zero : bumpVec hab x₀ h hh ha hb ≠ 0 := by
  intro h0
  have := norm_dx_bumpVec_sq hab hh ha hb
  rw [h0, map_zero, norm_zero, zero_pow two_ne_zero] at this
  exact (div_pos bumpB_pos hh).ne' this.symm

/-- The form of a coefficient `g` on the bump: `∫ g |∂ₓv|² = ∫ g(x) ψ'((x − x₀)/h)²/h² dx`. -/
theorem integral_coeff_bumpVec (g : ℝ → ℝ) :
    ∫ x in Ioo a b, (g x : ℂ) * dx (Ioo a b) (bumpVec hab x₀ h hh ha hb) x *
        conj (dx (Ioo a b) (bumpVec hab x₀ h hh ha hb) x)
      = ((∫ x, g x * bumpG x₀ h x : ℝ) : ℂ) := by
  have e1 : ∫ x in Ioo a b, (g x : ℂ) * dx (Ioo a b) (bumpVec hab x₀ h hh ha hb) x *
        conj (dx (Ioo a b) (bumpVec hab x₀ h hh ha hb) x)
      = ∫ x in Ioo a b, ((g x * bumpG x₀ h x : ℝ) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [dx_ofC1Ioo hab (contDiff_bumpAt x₀ h) _] with x hx
    rw [show bumpVec hab x₀ h hh ha hb = ofC1Ioo hab (contDiff_bumpAt x₀ h) _ from rfl, hx,
      deriv_bumpAt, Complex.conj_ofReal]
    unfold bumpG
    push_cast
    ring
  rw [e1, integral_complex_ofReal, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [bumpG_eq_zero hh ha hb hx, mul_zero]

end bumpVec

/-- **Localisation.**  For a coefficient whose increment `Δ = 𝔞(t) − 𝔞(s)` is continuous, and
`c < |Δ(x₀)|` at a point `x₀ ∈ (a,b)`, there is `v ∈ H¹₀((a,b))`, `v ≠ 0`, with
`|𝔞(t)[v,v] − 𝔞(s)[v,v]| ≥ c ‖v‖²` (graph norm).  The element is a bump `ψ((x − x₀)/h)` with
`h` so small that `Δ` is almost constant on its support and `‖v‖²_{L²} = h² (A/B) ‖∂ₓv‖²` is
negligible. -/
theorem exists_form_sub_ge {a b : ℝ} (hab : a < b) {𝔞 : ℝ → ℝ → ℝ} {t s Λ : ℝ}
    (ht : IsBoundedCoeff 𝔞 t Λ) (hs : IsBoundedCoeff 𝔞 s Λ)
    (hc : Continuous fun x => 𝔞 t x - 𝔞 s x) {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo a b) {c : ℝ}
    (hlt : c < |𝔞 t x₀ - 𝔞 s x₀|) :
    ∃ v : H10 (Ioo a b), v ≠ 0 ∧
      c * ‖v‖ ^ 2 ≤ ‖form (Ioo a b) 𝔞 t v v - form (Ioo a b) 𝔞 s v v‖ := by
  set Δ : ℝ → ℝ := fun x => 𝔞 t x - 𝔞 s x with hΔ
  set η : ℝ := (|Δ x₀| - c) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  obtain ⟨ρ, hρ, hρη⟩ := Metric.continuous_iff.1 hc x₀ η hη0
  have hA := bumpA_nonneg
  have hB := bumpB_pos
  set h : ℝ := min (min (ρ / 2) (min ((x₀ - a) / 2) ((b - x₀) / 2)))
    (min 1 (η * bumpB / (|c| * bumpA + 1))) with hhdef
  have hx₀a : 0 < x₀ - a := by linarith [hx₀.1]
  have hx₀b : 0 < b - x₀ := by linarith [hx₀.2]
  have hh : 0 < h := by
    have : 0 < η * bumpB / (|c| * bumpA + 1) := by positivity
    simp only [hhdef, lt_min_iff]
    exact ⟨⟨by linarith, by linarith, by linarith⟩, by norm_num, this⟩
  have hhρ : h ≤ ρ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hha : h ≤ (x₀ - a) / 2 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhb : h ≤ (b - x₀) / 2 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hh1 : h ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hhc : h ≤ η * bumpB / (|c| * bumpA + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have ha : a < x₀ - h := by linarith
  have hb : x₀ + h < b := by linarith
  set v := bumpVec hab x₀ h hh ha hb with hv
  refine ⟨v, bumpVec_ne_zero hab hh ha hb, ?_⟩
  rw [form_sub_form ht hs, integral_coeff_bumpVec hab hh ha hb, Complex.norm_real,
    Real.norm_eq_abs, norm_bumpVec_sq hab hh ha hb]
  -- the integral `∫ Δ G` against the bump density `G`
  have hGint : Integrable (bumpG x₀ h) := (continuous_bumpG).integrable_of_hasCompactSupport
    (hasCompactSupport_bumpG hh)
  have hΔGint : Integrable fun x => Δ x * bumpG x₀ h x :=
    (hc.mul (continuous_bumpG)).integrable_of_hasCompactSupport
      (hasCompactSupport_bumpG hh).mul_left
  have hint2 : Integrable fun x => (Δ x - Δ x₀) * bumpG x₀ h x :=
    (hΔGint.sub (hGint.const_mul (Δ x₀))).congr
      (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  have hsplit : ∫ x, Δ x * bumpG x₀ h x =
      Δ x₀ * (∫ x, bumpG x₀ h x) + ∫ x, (Δ x - Δ x₀) * bumpG x₀ h x := by
    calc ∫ x, Δ x * bumpG x₀ h x = ∫ x, (Δ x₀ * bumpG x₀ h x + (Δ x - Δ x₀) * bumpG x₀ h x) := by
          congr 1; ext x; ring
      _ = _ := by
          rw [integral_add (hGint.const_mul _) hint2, integral_const_mul]
  have herr : |∫ x, (Δ x - Δ x₀) * bumpG x₀ h x| ≤ η * ∫ x, bumpG x₀ h x := by
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hGint.const_mul η) (Eventually.of_forall fun x => ?_)
    have hG0 : 0 ≤ bumpG x₀ h x := sq_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hG0]
    by_cases hGx : bumpG x₀ h x = 0
    · rw [hGx]; simp
    · have hx := abs_sub_le_of_bumpG_ne_zero hh hGx
      have hd : dist x x₀ < ρ := by rw [Real.dist_eq]; linarith
      have := hρη x hd
      rw [Real.dist_eq] at this
      gcongr
  have hGB : ∫ x, bumpG x₀ h x = bumpB / h := integral_bumpG hh
  rw [hsplit, hGB]
  rw [hGB] at herr
  -- conclude
  have hBh : 0 < bumpB / h := div_pos hB hh
  have hlow : (|Δ x₀| - η) * (bumpB / h) ≤
      |Δ x₀ * (bumpB / h) + ∫ x, (Δ x - Δ x₀) * bumpG x₀ h x| := by
    have h1 : |Δ x₀ * (bumpB / h)| = |Δ x₀| * (bumpB / h) := by
      rw [abs_mul, abs_of_pos hBh]
    have := abs_sub_abs_le_abs_sub (Δ x₀ * (bumpB / h)) (-∫ x, (Δ x - Δ x₀) * bumpG x₀ h x)
    rw [abs_neg, sub_neg_eq_add, h1] at this
    nlinarith
  refine le_trans ?_ hlow
  have hcη : |Δ x₀| - η = c + η := by rw [hη]; ring
  rw [hcη]
  -- `c (h² A + B)/h ≤ (c + η) B/h` iff `c h² A ≤ η B`
  have key : c * (h ^ 2 * bumpA) ≤ η * bumpB := by
    have h2 : h ^ 2 ≤ h := by nlinarith
    have h3 : |c| * bumpA * h ≤ (|c| * bumpA + 1) * h := by nlinarith
    have h4 : (|c| * bumpA + 1) * h ≤ η * bumpB := by
      rw [le_div_iff₀ (by positivity)] at hhc
      linarith
    calc c * (h ^ 2 * bumpA) ≤ |c| * (h ^ 2 * bumpA) := by
          gcongr
          exact le_abs_self c
      _ ≤ |c| * (h * bumpA) := by gcongr
      _ = |c| * bumpA * h := by ring
      _ ≤ η * bumpB := h3.trans h4
  rw [mul_div_assoc', div_le_iff₀ hh]
  field_simp
  nlinarith

/-- **`‖𝒜(t) − 𝒜(s)‖_{L(V,V')} = ‖𝔞(t) − 𝔞(s)‖_{L^∞(a,b)}`** for bounded coefficients with a
continuous increment `x ↦ 𝔞(t,x) − 𝔞(s,x)`. -/
theorem formOpDist_eq_eLpNorm {a b : ℝ} (hab : a < b) {𝔞 : ℝ → ℝ → ℝ} {t s Λ : ℝ}
    (ht : IsBoundedCoeff 𝔞 t Λ) (hs : IsBoundedCoeff 𝔞 s Λ)
    (hc : Continuous fun x => 𝔞 t x - 𝔞 s x) :
    formOpDist (Ioo a b) 𝔞 t s =
      eLpNorm (fun x => 𝔞 t x - 𝔞 s x) ∞ (volume.restrict (Ioo a b)) := by
  refine le_antisymm (formOpDist_le_eLpNorm ht hs) (le_of_forall_lt fun c hc' => ?_)
  have hEt := eLpNorm_coeff_sub_ne_top (U := Ioo a b) ht hs
  have hct : c ≠ ⊤ := ne_top_of_lt hc'
  set r := c.toReal with hr
  have hex : ∃ x₀ ∈ Ioo a b, r < |𝔞 t x₀ - 𝔞 s x₀| := by
    by_contra hno
    push Not at hno
    have : eLpNorm (fun x => 𝔞 t x - 𝔞 s x) ∞ (volume.restrict (Ioo a b)) ≤ c := by
      rw [eLpNorm_exponent_top hc.aestronglyMeasurable, ← ENNReal.ofReal_toReal hct]
      refine eLpNormEssSup_le_of_ae_bound ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [Real.norm_eq_abs]
      exact hno x hx
    exact absurd hc' (not_lt.2 this)
  obtain ⟨x₀, hx₀, hrx⟩ := hex
  set r' := (r + |𝔞 t x₀ - 𝔞 s x₀|) / 2 with hr'
  have hrr' : r < r' := by rw [hr']; linarith
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  obtain ⟨v, hv, hle⟩ := exists_form_sub_ge hab ht hs hc hx₀ (c := r') (by rw [hr']; linarith)
  calc c = ENNReal.ofReal r := (ENNReal.ofReal_toReal hct).symm
    _ < ENNReal.ofReal r' := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hrr'
    _ ≤ ‖form (Ioo a b) 𝔞 t v v - form (Ioo a b) 𝔞 s v v‖ₑ / (‖v‖ₑ * ‖v‖ₑ) := by
        have hne : ‖v‖ₑ * ‖v‖ₑ ≠ 0 := mul_ne_zero (enorm_ne_zero.2 hv) (enorm_ne_zero.2 hv)
        have hnt : ‖v‖ₑ * ‖v‖ₑ ≠ ⊤ := ENNReal.mul_ne_top enorm_ne_top enorm_ne_top
        rw [ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl hnt), ← ofReal_norm, ← ofReal_norm,
          ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by linarith)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← pow_two]
        exact hle
    _ ≤ formOpDist (Ioo a b) 𝔞 t s := div_le_formOpDist 𝔞 t s hv hv

/-- **The converse bound against the essential supremum:** for every
`c < ‖𝔞(t) − 𝔞(s)‖_{L^∞(a,b)}` (continuous increment) there is `v ∈ H¹₀((a,b))`, `v ≠ 0`, with
`|𝔞(t)[v,v] − 𝔞(s)[v,v]| ≥ c ‖v‖²_V`. -/
theorem exists_form_sub_ge_of_lt_eLpNorm {a b : ℝ} (hab : a < b) {𝔞 : ℝ → ℝ → ℝ} {t s Λ : ℝ}
    (ht : IsBoundedCoeff 𝔞 t Λ) (hs : IsBoundedCoeff 𝔞 s Λ)
    (hc : Continuous fun x => 𝔞 t x - 𝔞 s x) {c : ℝ}
    (hlt : ENNReal.ofReal c < eLpNorm (fun x => 𝔞 t x - 𝔞 s x) ∞ (volume.restrict (Ioo a b))) :
    ∃ v : H10 (Ioo a b), v ≠ 0 ∧
      c * ‖v‖ ^ 2 ≤ ‖form (Ioo a b) 𝔞 t v v - form (Ioo a b) 𝔞 s v v‖ := by
  rcases lt_or_ge c 0 with hc0 | hc0
  · exact exists_form_sub_ge hab ht hs hc (x₀ := (a + b) / 2) ⟨by linarith, by linarith⟩
      (lt_of_lt_of_le hc0 (abs_nonneg _))
  have hex : ∃ x₀ ∈ Ioo a b, c < |𝔞 t x₀ - 𝔞 s x₀| := by
    by_contra hno
    push Not at hno
    have : eLpNorm (fun x => 𝔞 t x - 𝔞 s x) ∞ (volume.restrict (Ioo a b)) ≤ ENNReal.ofReal c := by
      rw [eLpNorm_exponent_top hc.aestronglyMeasurable]
      refine eLpNormEssSup_le_of_ae_bound ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [Real.norm_eq_abs]
      exact hno x hx
    exact absurd hlt (not_lt.2 this)
  obtain ⟨x₀, hx₀, hcx⟩ := hex
  exact exists_form_sub_ge hab ht hs hc hx₀ hcx

end LionsC12
