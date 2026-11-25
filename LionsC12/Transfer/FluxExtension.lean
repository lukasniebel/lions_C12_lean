module

public import LionsC12.Spaces.Time
public import LionsC12.Transfer.Rescaling

/-!
# Lemma 6.1: zero extension of a vanishing flux

Lemma 6.1 of the paper: if `q ∈ L¹(0,1;H¹(0,π))` has vanishing traces `q(t,0) = q(t,π) = 0`
for almost every `t`, then `∂ₓ(E₀q) = E₀(∂ₓq)` in `𝒟'((0,1) × ℝ)`, where `E₀` is the zero
extension in space: the spatial derivative of the extended flux has no Dirac masses at the
endpoints.

`zero_extension_flux` proves this for `q ∈ L¹(0,1;W^{1,1}(0,π))` (which contains
`L¹(0,1;H¹(0,π))`), in the following form: `q(t,·)` is, for almost every `t`, the primitive
`x ↦ ∫₀ˣ ∂ₓq(t,y) dy` of `∂ₓq(t,·)` on `[0,π]` (the absolutely continuous representative with
`q(t,0) = 0`), `q(t,π) = 0`, `q` and `∂ₓq` are integrable on `(0,1) × (0,π)`, and the identity
`∫∫ E₀q ∂ₓψ = -∫∫ E₀(∂ₓq) ψ` holds for every `ψ ∈ C¹_c(ℝ²)`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology Real

/-- Fubini on the triangle on `[0,b]`: for `g ∈ L¹(0,b)` and `φ ∈ C¹(ℝ)`,
`∫₀ᵇ φ'(x) (∫₀ˣ g) dx = φ(b) ∫₀ᵇ g - ∫₀ᵇ φ g`. -/
theorem integral_deriv_mul_primitive {b : ℝ} (hb : 0 < b) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioc 0 b)) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    ∫ x in (0 : ℝ)..b, deriv φ x * ∫ y in (0 : ℝ)..x, g y
      = φ b * (∫ y in (0 : ℝ)..b, g y) - ∫ x in (0 : ℝ)..b, φ x * g x := by
  classical
  set μ : Measure ℝ := volume.restrict (Ioc 0 b) with hμ
  have hdc : Continuous (deriv φ) := hφ.continuous_deriv_one
  have hdint : Integrable (deriv φ) μ := hdc.integrableOn_Ioc
  set Fn : ℝ → ℝ → ℝ := fun x y => if y ≤ x then deriv φ x * g y else 0 with hFdef
  have hbase : Integrable (fun p : ℝ × ℝ => deriv φ p.1 * g p.2) (μ.prod μ) :=
    hdint.mul_prod hg
  have hmeasset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hprod : Integrable (Function.uncurry Fn) (μ.prod μ) := by
    have := hbase.indicator hmeasset
    refine this.congr ?_
    filter_upwards with p
    by_cases hp : p.2 ≤ p.1 <;> simp [hFdef, Function.uncurry, hp]
  have hIO : IntegrableOn (Function.uncurry Fn) (Set.uIoc 0 b ×ˢ Set.uIoc 0 b) := by
    rw [Set.uIoc_of_le hb.le, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact hprod
  have hswap : ∫ x in (0 : ℝ)..b, ∫ y in (0 : ℝ)..b, Fn x y
      = ∫ y in (0 : ℝ)..b, ∫ x in (0 : ℝ)..b, Fn x y :=
    MeasureTheory.intervalIntegral_intervalIntegral_swap hIO
  have hL : ∀ x ∈ Set.uIoc (0 : ℝ) b,
      deriv φ x * (∫ y in (0 : ℝ)..x, g y) = ∫ y in (0 : ℝ)..b, Fn x y := by
    intro x hx
    rw [Set.uIoc_of_le hb.le] at hx
    rw [intervalIntegral.integral_of_le hx.1.le, intervalIntegral.integral_of_le hb.le,
      ← integral_const_mul]
    have : ∀ y, Fn x y = Set.indicator (Set.Iic x) (fun y => deriv φ x * g y) y := by
      intro y; by_cases hy : y ≤ x <;> simp [hFdef, hy]
    simp only [this]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Iic, Set.Ioc_inter_Iic,
      inf_eq_right.2 hx.2]
  have hR : ∀ y ∈ Set.uIoc (0 : ℝ) b,
      (∫ x in (0 : ℝ)..b, Fn x y) = (φ b - φ y) * g y := by
    intro y hy
    rw [Set.uIoc_of_le hb.le] at hy
    have : ∀ x, Fn x y = Set.indicator (Set.Ici y) (fun x => deriv φ x * g y) x := by
      intro x; by_cases hxy : y ≤ x <;> simp [hFdef, hxy]
    simp only [this]
    rw [intervalIntegral.integral_of_le hb.le,
      MeasureTheory.setIntegral_indicator measurableSet_Ici]
    have hset : Set.Ioc 0 b ∩ Set.Ici y = Set.Icc y b := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
      exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨lt_of_lt_of_le hy.1 hx.1, hx.2⟩, hx.1⟩⟩
    rw [hset, ← MeasureTheory.setIntegral_congr_set Ioc_ae_eq_Icc,
      ← intervalIntegral.integral_of_le hy.2, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hφ.differentiable one_ne_zero x)
        (hdc.intervalIntegrable y b)]
  have hgI : IntervalIntegrable g volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).2 hg
  have hφg : IntervalIntegrable (fun x => φ x * g x) volume 0 b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc 0 b)).exists_bound_of_continuousOn
      hφ.continuous.continuousOn
    refine (hg.bdd_mul (c := C) hφ.continuous.aestronglyMeasurable.restrict ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hC x (Ioc_subset_Icc_self hx)
  calc ∫ x in (0 : ℝ)..b, deriv φ x * ∫ y in (0 : ℝ)..x, g y
      = ∫ x in (0 : ℝ)..b, ∫ y in (0 : ℝ)..b, Fn x y :=
        intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall hL)
    _ = ∫ y in (0 : ℝ)..b, ∫ x in (0 : ℝ)..b, Fn x y := hswap
    _ = ∫ y in (0 : ℝ)..b, (φ b - φ y) * g y :=
        intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall hR)
    _ = φ b * (∫ y in (0 : ℝ)..b, g y) - ∫ x in (0 : ℝ)..b, φ x * g x := by
        simp_rw [sub_mul]
        rw [intervalIntegral.integral_sub (hgI.const_mul _) hφg,
          intervalIntegral.integral_const_mul]

/-- **Lemma 6.1** (zero extension of a vanishing flux).  Let `q, ∂ₓq ∈ L¹((0,1) × (0,π))` with
`q(t,x) = ∫₀ˣ ∂ₓq(t,y) dy` on `[0,π]` (so `q(t,0) = 0`) and `q(t,π) = 0` for almost every
`t ∈ (0,1)`.  Then, with `E₀ = Z` the zero extension to `ℝ` in `x`,
`∫₀¹ ∫_ℝ E₀q ∂ₓψ dx dt = -∫₀¹ ∫_ℝ E₀(∂ₓq) ψ dx dt` for every `ψ` that is `C¹` in `x`; in
particular `∂ₓ(E₀q) = E₀(∂ₓq)` in `𝒟'((0,1) × ℝ)` (by Fubini the iterated integrals are the
double integrals for `ψ ∈ C_c^∞((0,1) × ℝ)`). -/
theorem zero_extension_flux {q qx : ℝ → ℝ → ℝ}
    (hqx : IntegrableOn (Function.uncurry qx) (Ioo 0 1 ×ˢ Ioo 0 π))
    (hq : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∀ x ∈ Icc 0 π,
      q t x = ∫ y in (0 : ℝ)..x, qx t y)
    (hπ : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), q t π = 0)
    {ψ : ℝ → ℝ → ℝ} (hψ : ∀ t, ContDiff ℝ 1 (ψ t)) :
    ∫ t in Ioo (0 : ℝ) 1, ∫ x, Z (q t) x * deriv (ψ t) x
      = -∫ t in Ioo (0 : ℝ) 1, ∫ x, Z (qx t) x * ψ t x := by
  rw [← integral_neg]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), IntegrableOn (qx t) (Ioo 0 π) := by
    have h := hqx
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
    exact h.prod_right_ae
  filter_upwards [hae, hq, hπ] with t ht hqt hπt
  have hZ : ∀ g : ℝ → ℝ, ∀ F : ℝ → ℝ, ∫ x, Z g x * F x = ∫ x in (0 : ℝ)..π, g x * F x := by
    intro g F
    rw [intervalIntegral.integral_of_le pi_pos.le, integral_Ioc_eq_integral_Ioo,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo 0 π)
        (fun x hx => by rw [Z_of_notMem hx, zero_mul])]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    simp only [Z_of_mem hx]
  rw [hZ, hZ]
  have hIoc : IntegrableOn (qx t) (Ioc 0 π) := ht.congr_set_ae Ioo_ae_eq_Ioc.symm
  have h1 : ∫ x in (0 : ℝ)..π, q t x * deriv (ψ t) x
      = ∫ x in (0 : ℝ)..π, deriv (ψ t) x * ∫ y in (0 : ℝ)..x, qx t y := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le pi_pos.le] at hx
    rw [hqt x hx, mul_comm]
  rw [h1, integral_deriv_mul_primitive pi_pos hIoc (hψ t), ← hqt π ⟨pi_pos.le, le_rfl⟩, hπt,
    mul_zero, zero_sub]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  ring

end LionsC12
