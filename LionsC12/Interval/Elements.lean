module

public import LionsC12.Construction.Cutoffs
public import LionsC12.Coefficient.Sharpness
public import LionsC12.Coefficient.FrozenDomain
public import LionsC12.Solution.Bochner
public import LionsC12.Forcing.Bounds
public import LionsC12.Forcing.Truncation
public import LionsC12.Transfer.Rescaling
public import LionsC12.Spaces.Forms

/-!
# The concrete functions as elements of `L²((0,π);ℂ)`, `H¹₀((0,π);ℂ)` and `H⁻¹((0,π);ℂ)`

The concrete construction (`LionsC12.Construction.Defs`) consists of real functions of
`(t,x)` with classical derivatives.  This file turns them into elements of the statement-level
spaces of `LionsC12.Paper.Statement` on `U = (0,π)`:

* `toL2c g` — the class in `L²((0,π);ℂ)` of a continuous real function `g`, with
  `‖toL2c g‖² = ∫₀^π g²` (`norm_toL2c_sq`) and `⟨toL2c g, toL2c h⟩ = ∫₀^π g h`;
* `hasDerivAt_Z_of_vanish` — the zero extension of a `C¹` function vanishing together with its
  derivative at `0` and `π` is `C¹` on `ℝ`;
* `ofC1Z` — the element `(g, g')` of `H¹₀((0,π))` of such a function (`IsC1Vanish`),
  with `val_ofC1Z`, `dx_ofC1Z`.

The dual-norm estimate in `H⁻¹((0,π);ℂ)` from estimates against test functions is in
`LionsC12.Interval.Dual`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped InnerProductSpace ComplexConjugate

/-- The interval `(0,π)`. -/
abbrev Iπ : Set ℝ := Ioo 0 π

theorem norm_toL2_sq {U : Set ℝ} (G : ℝ → ℂ) (hG : MemLp G 2 (volume.restrict U)) :
    ‖toL2 U G hG‖ ^ 2 = ∫ x in U, ‖G x‖ ^ 2 := by
  have h := (Lp.memLp (toL2 U G hG)).eLpNorm_eq_integral_rpow_norm two_ne_zero
    ENNReal.ofNat_ne_top
  rw [Lp.norm_def, h, ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  norm_num
  refine integral_congr_ae ?_
  filter_upwards [coe_toL2 G hG] with x hx
  rw [hx]

theorem integral_Iπ_eq (F : ℝ → ℝ) : ∫ x in Iπ, F x = ∫ x in (0 : ℝ)..π, F x := by
  rw [intervalIntegral.integral_of_le pi_pos.le, integral_Ioc_eq_integral_Ioo]

theorem integral_Iπ_eq_complex (F : ℝ → ℂ) : ∫ x in Iπ, F x = ∫ x in (0 : ℝ)..π, F x := by
  rw [intervalIntegral.integral_of_le pi_pos.le, integral_Ioc_eq_integral_Ioo]

/-! ### Continuous real functions in `L²((0,π);ℂ)` -/

theorem continuous_cplx {g : ℝ → ℝ} (hg : Continuous g) : Continuous fun x => (g x : ℂ) :=
  Complex.continuous_ofReal.comp hg

/-- The class in `L²((0,π);ℂ)` of a continuous real function. -/
def toL2c (g : ℝ → ℝ) (hg : Continuous g) : L2 Iπ :=
  toL2 Iπ (fun x => (g x : ℂ)) (memLp_Ioo_of_continuous (continuous_cplx hg))

variable {g h : ℝ → ℝ}

theorem coe_toL2c (hg : Continuous g) :
    ⇑(toL2c g hg) =ᵐ[volume.restrict Iπ] fun x => (g x : ℂ) := coe_toL2 _ _

theorem toL2c_congr (hg : Continuous g) (hh : Continuous h) (e : ∀ x ∈ Iπ, g x = h x) :
    toL2c g hg = toL2c h hh := by
  apply Lp.ext
  filter_upwards [coe_toL2c hg, coe_toL2c hh, ae_restrict_mem measurableSet_Ioo] with x h1 h2 hx
  rw [h1, h2, e x hx]

theorem toL2c_add (hg : Continuous g) (hh : Continuous h) :
    toL2c (fun x => g x + h x) (hg.add hh) = toL2c g hg + toL2c h hh := by
  apply Lp.ext
  filter_upwards [coe_toL2c (g := fun x => g x + h x) (hg.add hh), coe_toL2c hg, coe_toL2c hh,
    Lp.coeFn_add (toL2c g hg) (toL2c h hh)] with x h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3, Complex.ofReal_add]

theorem toL2c_sub (hg : Continuous g) (hh : Continuous h) :
    toL2c (fun x => g x - h x) (hg.sub hh) = toL2c g hg - toL2c h hh := by
  apply Lp.ext
  filter_upwards [coe_toL2c (g := fun x => g x - h x) (hg.sub hh), coe_toL2c hg, coe_toL2c hh,
    Lp.coeFn_sub (toL2c g hg) (toL2c h hh)] with x h1 h2 h3 h4
  rw [h1, h4, Pi.sub_apply, h2, h3, Complex.ofReal_sub]

theorem toL2c_smul (c : ℝ) (hg : Continuous g) :
    toL2c (fun x => c * g x) (continuous_const.mul hg) = (c : ℂ) • toL2c g hg := by
  apply Lp.ext
  filter_upwards [coe_toL2c (g := fun x => c * g x) (continuous_const.mul hg), coe_toL2c hg,
    Lp.coeFn_smul (c : ℂ) (toL2c g hg)] with x h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2, smul_eq_mul, Complex.ofReal_mul]

theorem toL2c_zero : toL2c (fun _ => 0) continuous_const = 0 := by
  apply Lp.ext
  filter_upwards [coe_toL2c (g := fun _ => (0 : ℝ)) continuous_const, Lp.coeFn_zero ℂ 2
    (volume.restrict Iπ)] with x h1 h2
  rw [h1, h2]; simp

theorem norm_toL2c_sq (hg : Continuous g) : ‖toL2c g hg‖ ^ 2 = normSq g := by
  rw [toL2c, norm_toL2_sq, normSq, ← integral_Iπ_eq]
  congr 1; ext x
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem norm_toL2c (hg : Continuous g) : ‖toL2c g hg‖ = Real.sqrt (normSq g) := by
  rw [← norm_toL2c_sq hg, Real.sqrt_sq (norm_nonneg _)]

theorem inner_toL2c (hg : Continuous g) (hh : Continuous h) :
    ⟪toL2c g hg, toL2c h hh⟫_ℂ = ((inner g h : ℝ) : ℂ) := by
  rw [inner_L2_eq, inner, ← intervalIntegral.integral_ofReal, ← integral_Iπ_eq_complex]
  refine integral_congr_ae ?_
  filter_upwards [coe_toL2c hg, coe_toL2c hh] with x h1 h2
  rw [h1, h2, Complex.conj_ofReal, Complex.ofReal_mul]

theorem im_toL2c (hg : Continuous g) : ∀ᵐ x ∂(volume.restrict Iπ), (toL2c g hg x).im = 0 := by
  filter_upwards [coe_toL2c hg] with x hx
  rw [hx, Complex.ofReal_im]

/-! ### `C¹` zero extensions -/

/-- The zero extension of a `C¹` function that vanishes together with its derivative at `0` and
`π` is differentiable on `ℝ`, with the zero extension of the derivative as derivative. -/
theorem hasDerivAt_Z_of_vanish {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (h0 : g 0 = 0) (hπ : g π = 0) (h0' : g' 0 = 0) (hπ' : g' π = 0) (x : ℝ) :
    HasDerivAt (Z g) (Z g' x) x := by
  by_cases hx : x ∈ Ioo (0 : ℝ) π
  · rw [Z_of_mem hx]
    exact (hg x).congr_of_eventuallyEq (Z_eventuallyEq_of_mem hx)
  by_cases hx0 : x = 0 ∨ x = π
  · -- at an endpoint: `|Z g y| ≤ |g y - g x - (y - x) g'(x)|`, which is `o(y - x)`
    have hgx : g x = 0 := by rcases hx0 with h | h <;> rw [h] <;> assumption
    have hg'x : g' x = 0 := by rcases hx0 with h | h <;> rw [h] <;> assumption
    rw [Z_of_notMem hx]
    rw [hasDerivAt_iff_isLittleO]
    have hlo := (hasDerivAt_iff_isLittleO.1 (hg x))
    have hZx : Z g x = 0 := Z_of_notMem hx
    refine Asymptotics.IsBigO.trans_isLittleO ?_ hlo
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun y => ?_)
    simp only [hZx, hgx, hg'x, sub_zero, smul_zero, one_mul, Real.norm_eq_abs]
    exact abs_Z_le g y
  · push Not at hx0
    rw [Z_of_notMem hx]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq (Z_eventuallyEq_zero hx hx0.1 hx0.2)

/-- The data of a `C¹` function on `ℝ` whose values and derivatives vanish at `0` and `π`. -/
structure IsC1Vanish (g g' : ℝ → ℝ) : Prop where
  hasDerivAt : ∀ x, HasDerivAt g (g' x) x
  cont' : Continuous g'
  zero_left : g 0 = 0
  zero_right : g π = 0
  zero_left' : g' 0 = 0
  zero_right' : g' π = 0

namespace IsC1Vanish

variable {g g' : ℝ → ℝ} (hg : IsC1Vanish g g')
include hg

theorem continuous : Continuous g :=
  continuous_iff_continuousAt.2 fun x => (hg.hasDerivAt x).continuousAt

theorem hasDerivAt_cplxZ (x : ℝ) :
    HasDerivAt (fun y => (Z g y : ℂ)) (Z g' x : ℂ) x :=
  (hasDerivAt_Z_of_vanish hg.hasDerivAt hg.zero_left hg.zero_right hg.zero_left'
    hg.zero_right' x).ofReal_comp

theorem deriv_cplxZ : deriv (fun y => (Z g y : ℂ)) = fun x => (Z g' x : ℂ) :=
  funext fun x => (hg.hasDerivAt_cplxZ x).deriv

theorem contDiff_cplxZ : ContDiff ℝ 1 (fun y => (Z g y : ℂ)) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hg.hasDerivAt_cplxZ x).differentiableAt, ?_⟩
  rw [hg.deriv_cplxZ]
  exact continuous_cplx (continuous_Z hg.cont' hg.zero_left' hg.zero_right')

end IsC1Vanish

theorem cplxZ_eq_zero {g : ℝ → ℝ} {x : ℝ} (hx : x ∉ Iπ) : (Z g x : ℂ) = 0 := by
  rw [Z_of_notMem hx, Complex.ofReal_zero]

/-- The element `(g, g')` of `H¹₀((0,π);ℂ)` defined by a real `C¹` function vanishing with its
derivative at `0` and `π`. -/
def ofC1Z {g g' : ℝ → ℝ} (hg : IsC1Vanish g g') : H10 Iπ :=
  ofC1Ioo pi_pos hg.contDiff_cplxZ fun _ hx => cplxZ_eq_zero hx

theorem val_ofC1Z {g g' : ℝ → ℝ} (hg : IsC1Vanish g g') :
    val Iπ (ofC1Z hg) = toL2c g hg.continuous := by
  unfold ofC1Z
  apply Lp.ext
  filter_upwards [val_ofC1Ioo pi_pos hg.contDiff_cplxZ (fun _ hx => cplxZ_eq_zero hx),
    coe_toL2c hg.continuous, ae_restrict_mem measurableSet_Ioo] with x h1 h2 hx
  rw [h1, h2, Z_of_mem hx]

theorem dx_ofC1Z {g g' : ℝ → ℝ} (hg : IsC1Vanish g g') :
    dx Iπ (ofC1Z hg) = toL2c g' hg.cont' := by
  unfold ofC1Z
  apply Lp.ext
  filter_upwards [dx_ofC1Ioo pi_pos hg.contDiff_cplxZ (fun _ hx => cplxZ_eq_zero hx),
    coe_toL2c hg.cont', ae_restrict_mem measurableSet_Ioo] with x h1 h2 hx
  rw [h1, hg.deriv_cplxZ, h2]
  simp only [Z_of_mem hx]

end LionsC12
