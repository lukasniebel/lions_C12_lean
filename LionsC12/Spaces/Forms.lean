module

public import LionsC12.Spaces.Line

/-!
# The forms `𝔞(t)[v,w]` on `H¹₀(U)` and uniqueness of the Lions solution

For a bounded measurable coefficient `𝔞`, the form
`form U 𝔞 t v w = ∫_U 𝔞(t,x) ∂ₓv conj(∂ₓw)` of `LionsC12.Paper.Statement` is

* additive in `v` (`form_sub`) and bounded, `|𝔞(t)[v,w]| ≤ Λ ‖∂ₓv‖ ‖∂ₓw‖ ≤ Λ ‖v‖ ‖w‖`
  (`norm_form_le`);
* accretive, `Re 𝔞(t)[v,v] ≥ 0`, for `𝔞 ≥ 0` (`form_self_re_nonneg`), and coercive in `‖∂ₓv‖`,
  `Re 𝔞(t)[v,v] ≥ λ ‖∂ₓv‖²`, for `𝔞 ≥ λ` (`form_self_re_ge`).

With the Gelfand triple of `LionsC12.Spaces.Line`, the uniqueness theorem
`LionsC12.IsLionsSol.ae_eq` applies: `isLionsSolution_unique`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge
open scoped InnerProductSpace ComplexConjugate

variable {U : Set ℝ}

instance (U : Set ℝ) : CompleteSpace (H10Graph U) :=
  (Submodule.span ℂ (testGraph U)).isClosed_topologicalClosure.completeSpace_coe

instance (U : Set ℝ) : CompleteSpace (H10 U) := inferInstanceAs (CompleteSpace (H10Graph U))

theorem isLionsSolution_iff (𝔞 : ℝ → ℝ → ℝ) (f : ℝ → L2 U) (w : ℝ → H10 U) :
    IsLionsSolution U 𝔞 f w ↔ IsLionsSol (val U) (form U 𝔞) f w := Iff.rfl

theorem ofL2_eq_ofHL (h : L2 U) : ofL2 U h = ofHL (val U) h := rfl

theorem ofH10_eq (v : H10 U) : ofH10 U v = ofHL (val U) (val U v) := rfl

/-- A coefficient that is bounded and measurable in `x` at the time `t`. -/
structure IsBoundedCoeff (𝔞 : ℝ → ℝ → ℝ) (t : ℝ) (Λ : ℝ) : Prop where
  measurable : Measurable (𝔞 t)
  bound : ∀ x, |𝔞 t x| ≤ Λ

theorem integrable_form_integrand {𝔞 : ℝ → ℝ → ℝ} {t Λ : ℝ} (h : IsBoundedCoeff 𝔞 t Λ)
    (v w : H10 U) :
    Integrable (fun x => (𝔞 t x : ℂ) * dx U v x * conj (dx U w x)) (volume.restrict U) := by
  have hi : Integrable (fun x => ⟪dx U w x, dx U v x⟫_ℂ) (volume.restrict U) :=
    L2.integrable_inner (dx U w) (dx U v)
  have hm : AEStronglyMeasurable (fun x => (𝔞 t x : ℂ)) (volume.restrict U) :=
    (Complex.measurable_ofReal.comp h.measurable).aestronglyMeasurable
  refine (hi.bdd_mul (c := Λ) hm (Eventually.of_forall fun x => ?_)).congr ?_
  · rw [Complex.norm_real, Real.norm_eq_abs]; exact h.bound x
  · filter_upwards with x
    simp only [RCLike.inner_apply]
    ring

theorem form_sub {𝔞 : ℝ → ℝ → ℝ} {t Λ : ℝ} (h : IsBoundedCoeff 𝔞 t Λ) (v₁ v₂ z : H10 U) :
    form U 𝔞 t (v₁ - v₂) z = form U 𝔞 t v₁ z - form U 𝔞 t v₂ z := by
  unfold form
  rw [← integral_sub (integrable_form_integrand h v₁ z) (integrable_form_integrand h v₂ z)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (dx U v₁) (dx U v₂)] with x hx
  rw [map_sub, hx, Pi.sub_apply]
  ring

/-- Cauchy–Schwarz: `∫ ‖f‖ ‖g‖ ≤ ‖f‖_{L²} ‖g‖_{L²}`. -/
theorem integral_norm_mul_norm_le_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (f : Lp E 2 μ) (g : Lp F 2 μ) :
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤ ‖f‖ * ‖g‖ := by
  have hfm : MemLp (fun x => ‖f x‖) (ENNReal.ofReal 2) μ := by simpa using (Lp.memLp f).norm
  have hgm : MemLp (fun x => ‖g x‖) (ENNReal.ofReal 2) μ := by simpa using (Lp.memLp g).norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => norm_nonneg (f x))
    (Eventually.of_forall fun x => norm_nonneg (g x))
    hfm hgm
  have kf : (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = ‖f‖ := by
    rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofReal (by positivity)]
    norm_num
  have kg : (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = ‖g‖ := by
    rw [Lp.norm_def, (Lp.memLp g).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofReal (by positivity)]
    norm_num
  rw [kf, kg] at h
  exact h

/-- The forms are bounded: `|𝔞(t)[v,w]| ≤ Λ ‖∂ₓv‖ ‖∂ₓw‖`. -/
theorem norm_form_le {𝔞 : ℝ → ℝ → ℝ} {t Λ : ℝ} (h : IsBoundedCoeff 𝔞 t Λ) (v w : H10 U) :
    ‖form U 𝔞 t v w‖ ≤ Λ * ‖dx U v‖ * ‖dx U w‖ := by
  unfold form
  calc ‖∫ x in U, (𝔞 t x : ℂ) * dx U v x * conj (dx U w x)‖
      ≤ ∫ x in U, Λ * (‖dx U v x‖ * ‖dx U w x‖) := by
        refine norm_integral_le_of_norm_le ?_ (Eventually.of_forall fun x => ?_)
        · refine ((L2.integrable_inner (𝕜 := ℂ) (dx U v) (dx U w)).norm.const_mul Λ).congr
            (Eventually.of_forall fun x => ?_)
          simp only [RCLike.inner_apply, norm_mul, RCLike.norm_conj]
          ring
        · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj, mul_assoc]
          gcongr
          exact h.bound x
    _ = Λ * ∫ x in U, ‖dx U v x‖ * ‖dx U w x‖ := integral_const_mul _ _
    _ ≤ Λ * (‖dx U v‖ * ‖dx U w‖) := by
        have hΛ : 0 ≤ Λ := (abs_nonneg _).trans (h.bound 0)
        gcongr
        exact integral_norm_mul_norm_le_L2 _ _
    _ = Λ * ‖dx U v‖ * ‖dx U w‖ := by ring

/-- For `𝔞 ≥ λ`: `Re 𝔞(t)[v,v] ≥ λ ‖∂ₓv‖²`. -/
theorem form_self_re_ge {𝔞 : ℝ → ℝ → ℝ} {t Λ lam : ℝ} (h : IsBoundedCoeff 𝔞 t Λ)
    (hlam0 : 0 ≤ lam) (hlam : ∀ x, lam ≤ 𝔞 t x) (v : H10 U) :
    lam * ‖dx U v‖ ^ 2 ≤ (form U 𝔞 t v v).re := by
  have hint := integrable_form_integrand h v v
  unfold form
  show lam * _ ≤ RCLike.re (∫ x in U, (𝔞 t x : ℂ) * dx U v x * conj (dx U v x))
  rw [← integral_re hint]
  have hsq : ‖dx U v‖ ^ 2 = ∫ x in U, ‖dx U v x‖ ^ 2 := by
    have := (Lp.memLp (dx U v)).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
    rw [Lp.norm_def, this, ENNReal.toReal_ofReal (by positivity)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hsq, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) hint.re
    (Eventually.of_forall fun x => ?_)
  have e : RCLike.re ((𝔞 t x : ℂ) * dx U v x * conj (dx U v x)) = 𝔞 t x * ‖dx U v x‖ ^ 2 := by
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
    rfl
  show lam * ‖dx U v x‖ ^ 2 ≤ RCLike.re ((𝔞 t x : ℂ) * dx U v x * conj (dx U v x))
  rw [e]
  gcongr
  exact hlam x

/-- For `𝔞 ≥ 0`: `Re 𝔞(t)[v,v] ≥ 0`. -/
theorem form_self_re_nonneg {𝔞 : ℝ → ℝ → ℝ} {t Λ : ℝ} (h : IsBoundedCoeff 𝔞 t Λ)
    (h0 : ∀ x, 0 ≤ 𝔞 t x) (v : H10 U) : 0 ≤ (form U 𝔞 t v v).re := by
  have := form_self_re_ge h le_rfl h0 v
  simpa using this

/-- **Uniqueness of the Lions variational solution** on an open set `U ⊆ ℝ`, for a coefficient
which is measurable, bounded and nonnegative: two solutions of the class `IsLionsSolution`
with the same forcing agree almost everywhere on `(0,1)`. -/
theorem isLionsSolution_unique (hU : IsOpen U) {𝔞 : ℝ → ℝ → ℝ} {Λ : ℝ}
    (h𝔞 : ∀ t, IsBoundedCoeff 𝔞 t Λ) (h0 : ∀ t x, 0 ≤ 𝔞 t x) {f : ℝ → L2 U} {w₁ w₂ : ℝ → H10 U}
    (h₁ : IsLionsSolution U 𝔞 f w₁) (h₂ : IsLionsSolution U 𝔞 f w₂) :
    ∀ᵐ t ∂μ01, w₁ t = w₂ t :=
  IsLionsSol.ae_eq (val_injective hU) (denseRange_val hU)
    (fun t v₁ v₂ z => form_sub (h𝔞 t) v₁ v₂ z) (fun t v => form_self_re_nonneg (h𝔞 t) (h0 t) v)
    ((isLionsSolution_iff _ _ _).1 h₁) ((isLionsSolution_iff _ _ _).1 h₂)

end LionsC12
