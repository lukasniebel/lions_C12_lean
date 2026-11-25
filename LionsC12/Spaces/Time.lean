module

public import LionsC12.Paper.Statement
public import LionsC12.Lions.WeakDeriv
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Distributional derivatives in time

Facts about `LionsC12Challenge.HasWeakDeriv`, the distributional derivative on the time interval
`(0,1)` with scalar `C_c^∞` test functions, for functions with values in a Banach space `E`:

* `integral_deriv_smul_primitive` — Fubini on the triangle:
  `∫₀¹ φ'(t) ∫₀ᵗ g = -∫₀¹ φ g` for `φ ∈ C¹` with `φ(1) = 0`;
* `HasWeakDeriv.exists_ae_eq_const_add_integral` — the absolutely continuous representative:
  `u = c + ∫₀ᵗ g` almost everywhere (du Bois-Reymond);
* `hasWeakDeriv_of_hasDerivAt_off_countable` — a continuous function on `[0,1]`, differentiable
  off a countable set with integrable derivative, has that derivative as distributional
  derivative;
* `HasWeakDeriv.sub`, `HasWeakDeriv.map` — linearity, and compatibility with bounded linear maps;
  `HasWeakDeriv.of_map` — a distributional derivative is detected after an injective one;
* `HasWeakDeriv.ae_eq` — uniqueness: functions which agree almost everywhere have the same
  integrable distributional derivatives, almost everywhere.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Lebesgue measure on `(0,1)`. -/
abbrev μ01 : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

theorem μT_one_eq_μ01 : μT 1 = μ01 := μT_eq_restrict_Ioo 1

theorem setIntegral_Ioo_eq_intervalIntegral (g : ℝ → E) :
    ∫ t in Ioo (0 : ℝ) 1, g t = ∫ t in (0 : ℝ)..1, g t := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- A test function supported in `(0,1)` vanishes at `0` and `1`. -/
theorem eq_zero_of_tsupport_subset {φ : ℝ → ℝ} (h : tsupport φ ⊆ Ioo 0 1) {t : ℝ}
    (ht : t ∉ Ioo (0 : ℝ) 1) : φ t = 0 :=
  image_eq_zero_of_notMem_tsupport fun h' => ht (h h')

/-- Fubini on the triangle: for `g ∈ L¹(0,1;E)` and `φ ∈ C¹(ℝ;ℝ)` with `φ(1) = 0`,
`∫₀¹ φ'(t) (∫₀ᵗ g) dt = -∫₀¹ φ(t) g(t) dt`. -/
theorem integral_deriv_smul_primitive [CompleteSpace E] {g : ℝ → E} (hg : IntegrableOn g (Ioo 0 1))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (h1 : φ 1 = 0) :
    ∫ t in Ioo (0 : ℝ) 1, deriv φ t • ∫ τ in (0 : ℝ)..t, g τ
      = -∫ t in Ioo (0 : ℝ) 1, φ t • g t := by
  classical
  have hg' : Integrable g (μT 1) := by rw [μT_one_eq_μ01]; exact hg
  have hdc : Continuous (deriv φ) := hφ.continuous_deriv_one
  have hdint : Integrable (deriv φ) (μT 1) := hdc.integrableOn_Ioc
  set Fn : ℝ → ℝ → E := fun t τ => if τ ≤ t then deriv φ t • g τ else 0 with hFdef
  have hbase : Integrable (fun p : ℝ × ℝ => deriv φ p.1 • g p.2) ((μT 1).prod (μT 1)) :=
    hdint.smul_prod hg'
  have hmeasset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hprod : Integrable (Function.uncurry Fn) ((μT 1).prod (μT 1)) := by
    have := hbase.indicator hmeasset
    refine this.congr ?_
    filter_upwards with p
    by_cases hp : p.2 ≤ p.1 <;> simp [hFdef, Function.uncurry, hp]
  have hIO : IntegrableOn (Function.uncurry Fn) (Set.uIoc 0 1 ×ˢ Set.uIoc 0 1) := by
    rw [Set.uIoc_of_le zero_le_one, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact hprod
  have hswap : ∫ t in (0 : ℝ)..1, ∫ τ in (0 : ℝ)..1, Fn t τ
      = ∫ τ in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, Fn t τ :=
    MeasureTheory.intervalIntegral_intervalIntegral_swap hIO
  have hL : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      deriv φ t • (∫ τ in (0 : ℝ)..t, g τ) = ∫ τ in (0 : ℝ)..1, Fn t τ := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht0 : (0 : ℝ) ≤ t := ht.1.le
    rw [intervalIntegral.integral_of_le ht0, intervalIntegral.integral_of_le zero_le_one,
      ← integral_smul]
    have : ∀ τ, Fn t τ = Set.indicator (Set.Iic t) (fun τ => deriv φ t • g τ) τ := by
      intro τ; by_cases hτ : τ ≤ t <;> simp [hFdef, hτ]
    simp only [this]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Iic, Set.Ioc_inter_Iic,
      inf_eq_right.2 ht.2]
  have hR : ∀ τ ∈ Set.uIoc (0 : ℝ) 1,
      (∫ t in (0 : ℝ)..1, Fn t τ) = -(φ τ • g τ) := by
    intro τ hτ
    rw [Set.uIoc_of_le zero_le_one] at hτ
    have : ∀ t, Fn t τ = Set.indicator (Set.Ici τ) (fun t => deriv φ t • g τ) t := by
      intro t; by_cases htt : τ ≤ t <;> simp [hFdef, htt]
    simp only [this]
    rw [intervalIntegral.integral_of_le zero_le_one,
      MeasureTheory.setIntegral_indicator measurableSet_Ici]
    have hset : Set.Ioc 0 1 ∩ Set.Ici τ = Set.Icc τ 1 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
      exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨lt_of_lt_of_le hτ.1 hx.1, hx.2⟩, hx.1⟩⟩
    rw [hset, ← MeasureTheory.setIntegral_congr_set Ioc_ae_eq_Icc,
      ← intervalIntegral.integral_of_le hτ.2, intervalIntegral.integral_smul_const,
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hφ.differentiable one_ne_zero x)
        (hdc.intervalIntegrable τ 1), h1, zero_sub, neg_smul]
  rw [setIntegral_Ioo_eq_intervalIntegral, setIntegral_Ioo_eq_intervalIntegral]
  calc ∫ t in (0 : ℝ)..1, deriv φ t • ∫ τ in (0 : ℝ)..t, g τ
      = ∫ t in (0 : ℝ)..1, ∫ τ in (0 : ℝ)..1, Fn t τ :=
        intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall hL)
    _ = ∫ τ in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, Fn t τ := hswap
    _ = ∫ τ in (0 : ℝ)..1, -(φ τ • g τ) :=
        intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall hR)
    _ = -∫ t in (0 : ℝ)..1, φ t • g t := intervalIntegral.integral_neg


/-- A continuous compactly supported scalar function times an integrable function is
integrable. -/
theorem integrableOn_smul_of_continuous {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    {u : ℝ → E} {s : Set ℝ} (hu : IntegrableOn u s) : IntegrableOn (fun t => ψ t • u t) s := by
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hc
  exact hu.bdd_smul C hψ.aestronglyMeasurable (Eventually.of_forall hC)

/-- **The absolutely continuous representative** (du Bois-Reymond): if `g ∈ L¹(0,1;E)` is the
distributional derivative of `u ∈ L¹(0,1;E)`, then `u = c + ∫₀ᵗ g` almost everywhere on `(0,1)`. -/
theorem HasWeakDeriv.exists_ae_eq_const_add_integral [CompleteSpace E] {u g : ℝ → E}
    (h : HasWeakDeriv u g) (hu : IntegrableOn u (Ioo 0 1)) (hg : IntegrableOn g (Ioo 0 1)) :
    ∃ c : E, ∀ᵐ t ∂μ01, u t = c + ∫ τ in (0 : ℝ)..t, g τ := by
  have hu' : Integrable u (μT 1) := by rw [μT_one_eq_μ01]; exact hu
  have hg' : Integrable g (μT 1) := by rw [μT_one_eq_μ01]; exact hg
  have hP : Integrable (fun t => ∫ τ in (0 : ℝ)..t, g τ) (μT 1) := integrable_primitive one_pos hg'
  have hw : Integrable (fun t => u t - ∫ τ in (0 : ℝ)..t, g τ) (μT 1) := hu'.sub hP
  have key : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo 0 1 →
      ∫ t in (0 : ℝ)..1, deriv ψ t • (u t - ∫ τ in (0 : ℝ)..t, g τ) = 0 := by
    intro ψ hψ hcs hsub
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    have hdc : Continuous (deriv ψ) := hψ1.continuous_deriv_one
    have hdcs : HasCompactSupport (deriv ψ) := hcs.deriv
    have hPμ : IntegrableOn (fun t => ∫ τ in (0 : ℝ)..t, g τ) (Ioo 0 1) := by
      have := hP; rwa [μT_one_eq_μ01] at this
    have h1 : IntegrableOn (fun t => deriv ψ t • u t) (Ioo 0 1) :=
      integrableOn_smul_of_continuous hdc hdcs hu
    have h2 : IntegrableOn (fun t => deriv ψ t • ∫ τ in (0 : ℝ)..t, g τ) (Ioo 0 1) :=
      integrableOn_smul_of_continuous hdc hdcs hPμ
    have hψ1z : ψ 1 = 0 := eq_zero_of_tsupport_subset hsub (by simp)
    rw [← setIntegral_Ioo_eq_intervalIntegral]
    simp_rw [smul_sub]
    rw [integral_sub h1 h2, h ψ hψ hcs hsub, integral_deriv_smul_primitive hg hψ1 hψ1z]
    abel
  obtain ⟨c, hc⟩ := ae_eq_const_of_integral_deriv_smul_eq_zero one_pos hw key
  refine ⟨c, ?_⟩
  rw [← μT_one_eq_μ01]
  filter_upwards [hc] with t ht
  rw [← ht]
  exact (sub_add_cancel _ _).symm

/-- A function continuous on `[0,1]` and differentiable off a countable set, with integrable
derivative, has that derivative as its distributional derivative on `(0,1)`. -/
theorem hasWeakDeriv_of_hasDerivAt_off_countable [CompleteSpace E] {u g : ℝ → E} {s : Set ℝ}
    (hs : s.Countable) (hu : ContinuousOn u (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1 \ s, HasDerivAt u (g t) t) (hg : IntegrableOn g (Ioo 0 1)) :
    HasWeakDeriv u g := by
  intro φ hφ hcs hsub
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hdc : Continuous (deriv φ) := hφ1.continuous_deriv_one
  have hbu : IntegrableOn u (Icc 0 1) := hu.integrableOn_compact isCompact_Icc
  have h1 : IntegrableOn (fun t => deriv φ t • u t) (Ioo 0 1) :=
    (integrableOn_smul_of_continuous hdc hcs.deriv hbu).mono_set Ioo_subset_Icc_self
  have h2 : IntegrableOn (fun t => φ t • g t) (Ioo 0 1) :=
    integrableOn_smul_of_continuous hφ1.continuous hcs hg
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le (fun t => φ t • u t)
    (fun t => deriv φ t • u t + φ t • g t) zero_le_one hs
    (hφ1.continuous.continuousOn.smul hu)
    (fun t ht => by
      have := (hφ1.differentiable one_ne_zero t).hasDerivAt.smul (hd t ht)
      rw [add_comm] at this
      exact this)
    (by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
      exact h1.add h2)
  have h0 : φ 0 = 0 := eq_zero_of_tsupport_subset hsub (by simp)
  have h1' : φ 1 = 0 := eq_zero_of_tsupport_subset hsub (by simp)
  rw [h0, h1', zero_smul, zero_smul, sub_zero, ← setIntegral_Ioo_eq_intervalIntegral,
    integral_add h1 h2] at hFTC
  exact eq_neg_of_add_eq_zero_left hFTC

/-- Distributional derivatives of a difference. -/
theorem HasWeakDeriv.sub {u₁ u₂ g₁ g₂ : ℝ → E} (h₁ : HasWeakDeriv u₁ g₁)
    (h₂ : HasWeakDeriv u₂ g₂) (hu₁ : IntegrableOn u₁ (Ioo 0 1)) (hu₂ : IntegrableOn u₂ (Ioo 0 1))
    (hg₁ : IntegrableOn g₁ (Ioo 0 1)) (hg₂ : IntegrableOn g₂ (Ioo 0 1)) :
    HasWeakDeriv (fun t => u₁ t - u₂ t) (fun t => g₁ t - g₂ t) := by
  intro φ hφ hcs hsub
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hdc : Continuous (deriv φ) := hφ1.continuous_deriv_one
  simp_rw [smul_sub]
  rw [integral_sub (integrableOn_smul_of_continuous hdc hcs.deriv hu₁)
      (integrableOn_smul_of_continuous hdc hcs.deriv hu₂),
    integral_sub (integrableOn_smul_of_continuous hφ1.continuous hcs hg₁)
      (integrableOn_smul_of_continuous hφ1.continuous hcs hg₂),
    h₁ φ hφ hcs hsub, h₂ φ hφ hcs hsub]
  abel

/-- Distributional derivatives commute with bounded linear maps. -/
theorem HasWeakDeriv.map [CompleteSpace E] [CompleteSpace F] {u g : ℝ → E} (h : HasWeakDeriv u g)
    (hu : IntegrableOn u (Ioo 0 1)) (hg : IntegrableOn g (Ioo 0 1)) (L : E →L[ℝ] F) :
    HasWeakDeriv (fun t => L (u t)) (fun t => L (g t)) := by
  intro φ hφ hcs hsub
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hdc : Continuous (deriv φ) := hφ1.continuous_deriv_one
  simp_rw [← L.map_smul]
  rw [L.integral_comp_comm (integrableOn_smul_of_continuous hdc hcs.deriv hu),
    L.integral_comp_comm (integrableOn_smul_of_continuous hφ1.continuous hcs hg),
    h φ hφ hcs hsub, map_neg]

/-- A distributional derivative can be detected after an injective bounded linear map. -/
theorem HasWeakDeriv.of_map [CompleteSpace E] [CompleteSpace F] {u g : ℝ → E} (L : E →L[ℝ] F)
    (hL : Function.Injective L) (h : HasWeakDeriv (fun t => L (u t)) (fun t => L (g t)))
    (hu : IntegrableOn u (Ioo 0 1)) (hg : IntegrableOn g (Ioo 0 1)) : HasWeakDeriv u g := by
  intro φ hφ hcs hsub
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hdc : Continuous (deriv φ) := hφ1.continuous_deriv_one
  apply hL
  rw [map_neg, ← L.integral_comp_comm (integrableOn_smul_of_continuous hdc hcs.deriv hu),
    ← L.integral_comp_comm (integrableOn_smul_of_continuous hφ1.continuous hcs hg)]
  simp_rw [L.map_smul]
  exact h φ hφ hcs hsub

/-- **Uniqueness of distributional derivatives**: functions which agree almost everywhere on
`(0,1)` have the same integrable distributional derivatives, almost everywhere. -/
theorem HasWeakDeriv.ae_eq [CompleteSpace E] {u₁ u₂ g₁ g₂ : ℝ → E} (h₁ : HasWeakDeriv u₁ g₁)
    (h₂ : HasWeakDeriv u₂ g₂) (hu : u₁ =ᵐ[μ01] u₂) (hg₁ : IntegrableOn g₁ (Ioo 0 1))
    (hg₂ : IntegrableOn g₂ (Ioo 0 1)) : g₁ =ᵐ[μ01] g₂ := by
  have key : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioo 0 1 →
      ∫ x, ψ x • (g₁ x - g₂ x) = 0 := by
    intro ψ hψ' hcs hsub
    have hψ1 : ContDiff ℝ 1 ψ := hψ'.of_le (by exact_mod_cast le_top)
    have i1 : IntegrableOn (fun t => ψ t • g₁ t) (Ioo 0 1) :=
      integrableOn_smul_of_continuous hψ1.continuous hcs hg₁
    have i2 : IntegrableOn (fun t => ψ t • g₂ t) (Ioo 0 1) :=
      integrableOn_smul_of_continuous hψ1.continuous hcs hg₂
    have e3 : ∫ t in Ioo 0 1, deriv ψ t • u₁ t = ∫ t in Ioo 0 1, deriv ψ t • u₂ t :=
      integral_congr_ae (hu.mono fun t ht => by simp only [ht])
    have e : ∫ t in Ioo 0 1, ψ t • g₁ t = ∫ t in Ioo 0 1, ψ t • g₂ t := by
      rw [← neg_inj, ← h₁ ψ hψ' hcs hsub, ← h₂ ψ hψ' hcs hsub, e3]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo 0 1) (fun x hx => by
      rw [eq_zero_of_tsupport_subset hsub hx, zero_smul])]
    simp_rw [smul_sub]
    rw [integral_sub i1 i2, e, sub_self]
  have hloc : LocallyIntegrableOn (fun x => g₁ x - g₂ x) (Ioo 0 1) volume :=
    (hg₁.sub hg₂).locallyIntegrableOn
  have h := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc key
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [h] with x hx hxI using sub_eq_zero.1 (hx hxI)

end LionsC12
