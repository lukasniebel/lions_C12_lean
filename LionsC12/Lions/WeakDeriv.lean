module

public import LionsC12.Lions.Gelfand
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Weak derivatives in `V'`, the absolutely continuous representative, integration by parts

This file is part of the abstract (Gelfand-triple) half of the formalisation of Lions' theorem.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set
open scoped InnerProductSpace ContDiff

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ### Elementary facts about `μT` -/

theorem μT_eq_restrict_Ioo (T : ℝ) : μT T = volume.restrict (Set.Ioo 0 T) := by
  rw [μT, Measure.restrict_congr_set Ioo_ae_eq_Ioc]

theorem integral_μT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ} (hT : 0 ≤ T)
    (f : ℝ → E) : ∫ t in (0 : ℝ)..T, f t = ∫ t, f t ∂(μT T) := by
  rw [intervalIntegral.integral_of_le hT]; rfl

theorem intervalIntegrable_of_integrable_μT {E : Type*} [NormedAddCommGroup E] {T : ℝ}
    (hT : 0 ≤ T) {f : ℝ → E} (hf : Integrable f (μT T)) : IntervalIntegrable f volume 0 T :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hf

/-- `1 ≤ ∞` for smoothness exponents. -/
theorem one_le_infty : (1 : ℕ∞ω) ≤ ∞ := by
  exact_mod_cast le_top (α := ℕ∞)

/-! ### The weak derivative -/

/-- `g ∈ L¹(0,T;V')` is the weak derivative of `u` (as a `V'`-valued function via `H ↪ V'`):
`∫₀ᵀ ⟪u, φ'⟫_H = −∫₀ᵀ ⟨g, φ⟩` for all `C¹` test functions compactly supported in `(0,T)`. -/
def HasWeakDerivV' (G : GelfandTriple V H) (T : ℝ) (u : ℝ → V) (g : ℝ → StrongDual ℝ V) : Prop :=
  ∀ φ : ℝ → V, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Set.Ioo 0 T →
    ∫ t in (0 : ℝ)..T, ⟪G.j (u t), G.j (deriv φ t)⟫_ℝ = -∫ t in (0 : ℝ)..T, g t (φ t)

/-! ### The du Bois-Reymond lemma -/

/-- A smooth function with compact support in `Icc a d ⊆ Ioo 0 T` and total integral zero has a
smooth primitive with compact support in `Ioo 0 T`. -/
theorem exists_primitive {T : ℝ} {gg : ℝ → ℝ} (hgg : ContDiff ℝ ∞ gg) {a d : ℝ} (ha : 0 < a)
    (hd : d < T) (hsupp : ∀ x, x ∉ Set.Icc a d → gg x = 0)
    (hzero : ∫ s in (0 : ℝ)..T, gg s = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Set.Ioo 0 T ∧
      deriv ψ = gg := by
  have hcont : Continuous gg := hgg.continuous
  have hint : ∀ x y : ℝ, IntervalIntegrable gg volume x y := fun x y =>
    hcont.intervalIntegrable x y
  have hderiv : deriv (fun t => ∫ s in (0 : ℝ)..t, gg s) = gg :=
    funext fun t => hcont.deriv_integral gg 0 t
  have hdiff : Differentiable ℝ (fun t => ∫ s in (0 : ℝ)..t, gg s) := fun t =>
    (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt.differentiableAt
  have hsm : ContDiff ℝ ∞ (fun t => ∫ s in (0 : ℝ)..t, gg s) :=
    contDiff_infty_iff_deriv.2 ⟨hdiff, by rw [hderiv]; exact hgg⟩
  have hvanish : ∀ x y : ℝ, (∀ s ∈ Set.uIcc x y, gg s = 0) → ∫ s in x..y, gg s = 0 := by
    intro x y hxy
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) hxy]
    simp
  have hzeroout : ∀ x, x ∉ Set.Icc a d → (∫ s in (0 : ℝ)..x, gg s) = 0 := by
    intro x hx
    rcases lt_or_ge x a with hxa | hxa
    · refine hvanish _ _ fun s hs => hsupp s fun hs' => ?_
      have h1 : s ≤ max 0 x := by
        rcases Set.mem_uIcc.mp hs with ⟨_, h⟩ | ⟨_, h⟩
        · exact h.trans (le_max_right _ _)
        · exact h.trans (le_max_left _ _)
      have h2 : max 0 x < a := max_lt ha hxa
      have h3 : a ≤ s := hs'.1
      linarith
    · have hxd : d < x := by
        by_contra hcon
        exact hx ⟨hxa, le_of_not_gt hcon⟩
      have hsplit : (∫ s in (0 : ℝ)..x, gg s)
          = (∫ s in (0 : ℝ)..T, gg s) + ∫ s in T..x, gg s :=
        (intervalIntegral.integral_add_adjacent_intervals (hint 0 T) (hint T x)).symm
      rw [hsplit, hzero, zero_add]
      refine hvanish _ _ fun s hs => hsupp s fun hs' => ?_
      have h2 : s ≤ d := hs'.2
      rcases Set.mem_uIcc.mp hs with ⟨h1, _⟩ | ⟨h1, _⟩
      · linarith
      · linarith
  have hsupp' : Function.support (fun t => ∫ s in (0 : ℝ)..t, gg s) ⊆ Set.Icc a d := by
    intro x hx
    by_contra hc
    exact hx (hzeroout x hc)
  have htsupp : tsupport (fun t => ∫ s in (0 : ℝ)..t, gg s) ⊆ Set.Icc a d :=
    closure_minimal hsupp' isClosed_Icc
  exact ⟨fun t => ∫ s in (0 : ℝ)..t, gg s, hsm,
    isCompact_Icc.of_isClosed_subset isClosed_closure htsupp,
    htsupp.trans (Set.Icc_subset_Ioo ha hd), hderiv⟩

/-- A normalised smooth bump supported well inside `(0,T)`. -/
theorem exists_bump {T : ℝ} (hT : 0 < T) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ tsupport ρ ⊆ Set.Icc (T / 4) (3 * T / 4) ∧
      ∫ t in (0 : ℝ)..T, ρ t = 1 := by
  have h1 : (0 : ℝ) < T / 8 := by positivity
  have h2 : T / 8 < T / 4 := by linarith
  let B : ContDiffBump (T / 2) := ⟨T / 8, T / 4, h1, h2⟩
  have hrOut : B.rOut = T / 4 := rfl
  have hts : tsupport (B.normed volume) ⊆ Set.Icc (T / 4) (3 * T / 4) := by
    rw [ContDiffBump.tsupport_normed_eq, hrOut, Real.closedBall_eq_Icc]
    apply Set.Icc_subset_Icc <;> linarith
  have hcompl : ∀ x ∉ Set.Ioc 0 T, B.normed volume x = 0 := by
    intro x hx
    by_contra hcon
    have hmem := hts (subset_tsupport _ (Function.mem_support.mpr hcon))
    exact hx ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  refine ⟨B.normed volume, B.contDiff_normed, hts, ?_⟩
  rw [intervalIntegral.integral_of_le hT.le,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hcompl, B.integral_normed]

/-- **Vector-valued du Bois-Reymond lemma.**  A locally integrable `w : ℝ → E` with
`∫₀ᵀ ψ' • w = 0` for all `ψ ∈ C_c^∞(0,T)` is a.e. constant on `(0,T)`.

NOTE.  The interface stated the smoothness hypothesis on `ψ` as `ContDiff ℝ ⊤ ψ`; in current
Mathlib `⊤ : ℕ∞ω` is the *analytic* exponent `ω`, and a nonzero analytic function on `ℝ` cannot
have compact support, so that version of the hypothesis is vacuous and the statement false.  We
use the intended `∞ = ((⊤ : ℕ∞) : ℕ∞ω)`. -/
theorem ae_eq_const_of_integral_deriv_smul_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {T : ℝ} (hT : 0 < T) {w : ℝ → E}
    (hw : MeasureTheory.Integrable w (μT T))
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo 0 T →
      ∫ t in (0 : ℝ)..T, deriv ψ t • w t = 0) :
    ∃ c : E, ∀ᵐ t ∂(μT T), w t = c := by
  classical
  obtain ⟨ρ, hρsm, hρts, hρone⟩ := exists_bump hT
  have hρcs : HasCompactSupport ρ := isCompact_Icc.of_isClosed_subset isClosed_closure hρts
  refine ⟨∫ t in (0 : ℝ)..T, ρ t • w t, ?_⟩
  have hwloc : LocallyIntegrable w (μT T) := hw.locallyIntegrable
  have hρw : IntervalIntegrable (fun t => ρ t • w t) volume 0 T :=
    intervalIntegrable_of_integrable_μT hT.le
      (hwloc.integrable_smul_left_of_hasCompactSupport hρsm.continuous hρcs)
  have main : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ Set.Ioo 0 T →
      ∫ t, θ t • (w t - ∫ s in (0 : ℝ)..T, ρ s • w s) ∂(μT T) = 0 := by
    intro θ hθ hθc hθs
    have hθw : IntervalIntegrable (fun t => θ t • w t) volume 0 T :=
      intervalIntegrable_of_integrable_μT hT.le
        (hwloc.integrable_smul_left_of_hasCompactSupport hθ.continuous hθc)
    -- the compact set carrying both `θ` and `ρ`
    have hK : IsCompact (tsupport θ ∪ Set.Icc (T / 4) (3 * T / 4)) := hθc.union isCompact_Icc
    have hKne : (tsupport θ ∪ Set.Icc (T / 4) (3 * T / 4)).Nonempty :=
      ⟨T / 2, Or.inr ⟨by linarith, by linarith⟩⟩
    have hKsub : tsupport θ ∪ Set.Icc (T / 4) (3 * T / 4) ⊆ Set.Ioo 0 T := by
      rintro x (hx | hx)
      · exact hθs hx
      · exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    obtain ⟨a, haK, hamin⟩ := hK.exists_isLeast hKne
    obtain ⟨d, hdK, hdmax⟩ := hK.exists_isGreatest hKne
    have hggsm : ContDiff ℝ ∞ (fun t => θ t - (∫ s in (0 : ℝ)..T, θ s) * ρ t) :=
      hθ.sub (contDiff_const.mul hρsm)
    have hggsupp : ∀ x, x ∉ Set.Icc a d → θ x - (∫ s in (0 : ℝ)..T, θ s) * ρ x = 0 := by
      intro x hx
      have hxK : x ∉ tsupport θ ∪ Set.Icc (T / 4) (3 * T / 4) := fun hh => hx ⟨hamin hh, hdmax hh⟩
      have e1 : θ x = 0 := image_eq_zero_of_notMem_tsupport fun hh => hxK (Or.inl hh)
      have e2 : ρ x = 0 := image_eq_zero_of_notMem_tsupport fun hh => hxK (Or.inr (hρts hh))
      rw [e1, e2]; ring
    have hggzero : ∫ s in (0 : ℝ)..T, (θ s - (∫ r in (0 : ℝ)..T, θ r) * ρ s) = 0 := by
      rw [intervalIntegral.integral_sub (hθ.continuous.intervalIntegrable 0 T)
        ((hρsm.continuous.intervalIntegrable 0 T).const_mul _),
        intervalIntegral.integral_const_mul, hρone]
      ring
    obtain ⟨ψ, hψsm, hψc, hψs, hψd⟩ :=
      exists_primitive hggsm (hKsub haK).1 (hKsub hdK).2 hggsupp hggzero
    have hkey := h ψ hψsm hψc hψs
    rw [hψd] at hkey
    have hρw' : IntervalIntegrable
        (fun t => (∫ s in (0 : ℝ)..T, θ s) • (ρ t • w t)) volume 0 T := hρw.smul _
    have hsplit : ∫ t in (0 : ℝ)..T, (θ t - (∫ s in (0 : ℝ)..T, θ s) * ρ t) • w t
        = (∫ t in (0 : ℝ)..T, θ t • w t)
          - (∫ s in (0 : ℝ)..T, θ s) • ∫ t in (0 : ℝ)..T, ρ t • w t := by
      have e : ∀ t, (θ t - (∫ s in (0 : ℝ)..T, θ s) * ρ t) • w t
          = θ t • w t - (∫ s in (0 : ℝ)..T, θ s) • (ρ t • w t) := by
        intro t; rw [sub_smul, mul_smul]
      simp only [e]
      rw [intervalIntegral.integral_sub hθw hρw', intervalIntegral.integral_smul]
    rw [hsplit, sub_eq_zero] at hkey
    rw [← integral_μT hT.le]
    have e2 : ∀ t, θ t • (w t - ∫ s in (0 : ℝ)..T, ρ s • w s)
        = θ t • w t - θ t • (∫ s in (0 : ℝ)..T, ρ s • w s) := fun t => smul_sub _ _ _
    simp only [e2]
    have hconst : IntervalIntegrable
        (fun t => θ t • (∫ s in (0 : ℝ)..T, ρ s • w s)) volume 0 T :=
      (hθ.continuous.smul continuous_const).intervalIntegrable 0 T
    rw [intervalIntegral.integral_sub hθw hconst, intervalIntegral.integral_smul_const, hkey,
      sub_self]
  have hfin : ∀ᵐ t ∂(μT T), t ∈ Set.Ioo 0 T → w t - (∫ s in (0 : ℝ)..T, ρ s • w s) = 0 :=
    isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hw.sub (integrable_const _)).locallyIntegrable.locallyIntegrableOn _) main
  have hIoo : ∀ᵐ t ∂(μT T), t ∈ Set.Ioo 0 T := by
    rw [μT_eq_restrict_Ioo]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hfin, hIoo] with t h1 h2 using sub_eq_zero.mp (h1 h2)

/-! ### Measurability and integrability helpers for `V'`-valued functions -/

omit [CompleteSpace V] in
theorem aestronglyMeasurable_apply {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → StrongDual ℝ V} {φ : α → V} (hg : AEStronglyMeasurable g μ)
    (hφ : AEStronglyMeasurable φ μ) : AEStronglyMeasurable (fun x => g x (φ x)) μ :=
  (ContinuousLinearMap.id ℝ (StrongDual ℝ V)).aestronglyMeasurable_comp₂ hg hφ

omit [CompleteSpace V] in
theorem aestronglyMeasurable_apply₂ {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A : α → V →L[ℝ] V →L[ℝ] ℝ} {u : α → V} (hA : AEStronglyMeasurable A μ)
    (hu : AEStronglyMeasurable u μ) : AEStronglyMeasurable (fun x => A x (u x)) μ := by
  have hcont : Continuous (fun p : (V →L[ℝ] V →L[ℝ] ℝ) × V => p.1 p.2) :=
    isBoundedBilinearMap_apply.continuous
  exact hcont.comp_aestronglyMeasurable (hA.prodMk hu)

omit [CompleteSpace V] in
theorem integrable_apply_of_continuous {T : ℝ} {g : ℝ → StrongDual ℝ V}
    (hg : MeasureTheory.Integrable g (μT T)) {φ : ℝ → V} (hφ : Continuous φ) :
    MeasureTheory.Integrable (fun t => g t (φ t)) (μT T) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hφ.continuousOn
  refine Integrable.mono' (hg.norm.mul_const C)
    (aestronglyMeasurable_apply hg.aestronglyMeasurable hφ.aestronglyMeasurable) ?_
  have hmem : ∀ᵐ t ∂(μT T), t ∈ Set.Ioc 0 T := by
    rw [μT]; exact ae_restrict_mem measurableSet_Ioc
  filter_upwards [hmem] with t ht
  refine (g t).le_opNorm (φ t) |>.trans ?_
  exact mul_le_mul_of_nonneg_left (hC t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)

/-! ### Fubini on the triangle -/

/-- Fubini form of the product rule: for `g ∈ L¹(0,T;V')` and `φ ∈ C¹(ℝ;V)`,
`∫₀ᵀ (∫₀ᵗ g)(φ'(t)) dt = (∫₀ᵀ g)(φ T) − ∫₀ᵀ g(t)(φ t) dt`. -/
theorem integral_integral_apply_deriv {T : ℝ} (hT : 0 < T) {g : ℝ → StrongDual ℝ V}
    (hg : MeasureTheory.Integrable g (μT T)) {φ : ℝ → V} (hφ : ContDiff ℝ 1 φ) :
    ∫ t in (0 : ℝ)..T, (∫ τ in (0 : ℝ)..t, g τ) (deriv φ t)
      = (∫ τ in (0 : ℝ)..T, g τ) (φ T) - ∫ t in (0 : ℝ)..T, g t (φ t) := by
  classical
  have hdc : Continuous (deriv φ) := hφ.continuous_deriv_one
  have hdint : Integrable (deriv φ) (μT T) := hdc.integrableOn_Ioc
  set F : ℝ → ℝ → ℝ := fun t τ => if τ ≤ t then g τ (deriv φ t) else 0 with hFdef
  -- integrability of the uncurried integrand on the square
  have hbase : Integrable (fun p : ℝ × ℝ => g p.2 (deriv φ p.1)) ((μT T).prod (μT T)) := by
    refine Integrable.op_fst_snd (op := fun (v : V) (L : StrongDual ℝ V) => L v) ?_ ?_ hdint hg
    · exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := V) (F := ℝ)).continuous.comp
        continuous_swap
    · exact ⟨1, fun v L => by rw [one_mul, mul_comm]; exact L.le_opNorm v⟩
  have hmeasset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hprod : Integrable (Function.uncurry F) ((μT T).prod (μT T)) := by
    have := hbase.indicator hmeasset
    refine this.congr ?_
    filter_upwards with p
    by_cases hp : p.2 ≤ p.1 <;> simp [hFdef, Function.uncurry, hp]
  have hIO : IntegrableOn (Function.uncurry F) (Set.uIoc 0 T ×ˢ Set.uIoc 0 T) := by
    rw [Set.uIoc_of_le hT.le, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact hprod
  have hswap : ∫ t in (0 : ℝ)..T, ∫ τ in (0 : ℝ)..T, F t τ
      = ∫ τ in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, F t τ :=
    MeasureTheory.intervalIntegral_intervalIntegral_swap hIO
  -- the left-hand side
  have hL : ∀ t ∈ Set.uIoc (0 : ℝ) T,
      (∫ τ in (0 : ℝ)..t, g τ) (deriv φ t) = ∫ τ in (0 : ℝ)..T, F t τ := by
    intro t ht
    rw [Set.uIoc_of_le hT.le] at ht
    have ht0 : (0 : ℝ) ≤ t := ht.1.le
    have hgt : Integrable g (volume.restrict (Set.Ioc 0 t)) :=
      hg.mono_measure (Measure.restrict_mono (Set.Ioc_subset_Ioc_right ht.2) le_rfl)
    rw [intervalIntegral.integral_of_le ht0, ContinuousLinearMap.integral_apply hgt,
      intervalIntegral.integral_of_le hT.le]
    have : ∀ τ, F t τ = Set.indicator (Set.Iic t) (fun τ => g τ (deriv φ t)) τ := by
      intro τ; by_cases hτ : τ ≤ t <;> simp [hFdef, hτ]
    simp only [this]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Iic, Set.Ioc_inter_Iic,
      inf_eq_right.2 ht.2]
  -- the right-hand side
  have hR : ∀ τ ∈ Set.uIoc (0 : ℝ) T,
      (∫ t in (0 : ℝ)..T, F t τ) = g τ (φ T) - g τ (φ τ) := by
    intro τ hτ
    rw [Set.uIoc_of_le hT.le] at hτ
    have : ∀ t, F t τ = Set.indicator (Set.Ici τ) (fun t => g τ (deriv φ t)) t := by
      intro t; by_cases htt : τ ≤ t <;> simp [hFdef, htt]
    simp only [this]
    rw [intervalIntegral.integral_of_le hT.le,
      MeasureTheory.setIntegral_indicator measurableSet_Ici]
    have hset : Set.Ioc 0 T ∩ Set.Ici τ = Set.Icc τ T := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
      exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨lt_of_lt_of_le hτ.1 hx.1, hx.2⟩, hx.1⟩⟩
    rw [hset, ← MeasureTheory.setIntegral_congr_set Ioc_ae_eq_Icc,
      ← intervalIntegral.integral_of_le hτ.2,
      ContinuousLinearMap.intervalIntegral_comp_comm _ (hdc.intervalIntegrable τ T),
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hφ.differentiable one_ne_zero x)
        (hdc.intervalIntegrable τ T), map_sub]
  calc ∫ t in (0 : ℝ)..T, (∫ τ in (0 : ℝ)..t, g τ) (deriv φ t)
      = ∫ t in (0 : ℝ)..T, ∫ τ in (0 : ℝ)..T, F t τ :=
        intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall hL)
    _ = ∫ τ in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, F t τ := hswap
    _ = ∫ τ in (0 : ℝ)..T, (g τ (φ T) - g τ (φ τ)) :=
        intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall hR)
    _ = (∫ τ in (0 : ℝ)..T, g τ) (φ T) - ∫ t in (0 : ℝ)..T, g t (φ t) := by
        rw [intervalIntegral.integral_sub
          (intervalIntegrable_of_integrable_μT hT.le (hg.apply_continuousLinearMap _))
          (intervalIntegrable_of_integrable_μT hT.le
            (integrable_apply_of_continuous hg hφ.continuous))]
        congr 1
        rw [integral_μT hT.le (fun τ => g τ (φ T)), integral_μT hT.le g,
          ContinuousLinearMap.integral_apply hg]

/-! ### The absolutely continuous representative -/

/-- The primitive `t ↦ ∫₀ᵗ g` of an `L¹` function is bounded and measurable on `(0,T]`. -/
theorem integrable_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ}
    (hT : 0 < T) {g : ℝ → E} (hg : MeasureTheory.Integrable g (μT T)) :
    MeasureTheory.Integrable (fun t => ∫ τ in (0 : ℝ)..t, g τ) (μT T) := by
  have hgIcc : IntegrableOn g (Set.uIcc 0 T) volume := by
    rw [Set.uIcc_of_le hT.le]
    have hgIoc : IntegrableOn g (Set.Ioc 0 T) volume := hg
    exact hgIoc.congr_set_ae Ioc_ae_eq_Icc.symm
  have hGcont : ContinuousOn (fun t => ∫ τ in (0 : ℝ)..t, g τ) (Set.Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval hgIcc
    rwa [Set.uIcc_of_le hT.le] at this
  obtain ⟨C, hCbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hGcont
  have hmem : ∀ᵐ t ∂(μT T), t ∈ Set.Ioc 0 T := by
    rw [μT]; exact ae_restrict_mem measurableSet_Ioc
  refine Integrable.mono' (integrable_const C) ?_ ?_
  · rw [μT]
    exact (hGcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [hmem] with t ht
    exact hCbound t ⟨ht.1.le, ht.2⟩

theorem exists_ae_eq_const_add_integral (G : GelfandTriple V H) {T : ℝ} (hT : 0 < T) {u : ℝ → V}
    {g : ℝ → StrongDual ℝ V} (hu : MeasureTheory.Integrable u (μT T))
    (hg : MeasureTheory.Integrable g (μT T)) (h : HasWeakDerivV' G T u g) :
    ∃ c : StrongDual ℝ V, ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ := by
  have hflat : MeasureTheory.Integrable (fun t => G.flat (G.j (u t))) (μT T) :=
    ContinuousLinearMap.integrable_comp (G.flat ∘L G.j) hu
  have hGint : MeasureTheory.Integrable (fun t => ∫ τ in (0 : ℝ)..t, g τ) (μT T) :=
    integrable_primitive hT hg
  have hwint : MeasureTheory.Integrable
      (fun t => G.flat (G.j (u t)) - ∫ τ in (0 : ℝ)..t, g τ) (μT T) := hflat.sub hGint
  have hyp : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo 0 T →
      ∫ t in (0 : ℝ)..T, deriv ψ t • (G.flat (G.j (u t)) - ∫ τ in (0 : ℝ)..t, g τ) = 0 := by
    intro ψ hψ hψc hψs
    have hψ' : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.1 hψ).2
    have hint : MeasureTheory.Integrable
        (fun t => deriv ψ t • (G.flat (G.j (u t)) - ∫ τ in (0 : ℝ)..t, g τ)) (μT T) :=
      hwint.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hψ'.continuous hψc.deriv
    rw [integral_μT hT.le]
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.integral_apply hint, zero_apply,
      ← integral_μT hT.le]
    -- the test function `ψ • v`
    have hsub : tsupport (fun t => ψ t • v) ⊆ tsupport ψ :=
      closure_mono fun x hx hc0 => hx (by simp only [Function.mem_support] at *; simp [hc0])
    have hφc : HasCompactSupport (fun t => ψ t • v) :=
      hψc.of_isClosed_subset isClosed_closure hsub
    have hφ1 : ContDiff ℝ 1 (fun t => ψ t • v) :=
      (hψ.of_le one_le_infty).smul contDiff_const
    have hdφ : ∀ t, deriv (fun s => ψ s • v) t = deriv ψ t • v := fun t =>
      deriv_smul_const (hψ.differentiable (by simp) t) v
    have hψT : ψ T = 0 :=
      image_eq_zero_of_notMem_tsupport fun hh => absurd (hψs hh).2 (lt_irrefl T)
    -- (a) the definition of the weak derivative
    have ha := h (fun t => ψ t • v) hφ1 hφc (hsub.trans hψs)
    simp only [hdφ, map_smul, real_inner_smul_right] at ha
    -- (b) the Fubini identity
    have hb := integral_integral_apply_deriv hT hg hφ1
    simp only [hdφ, hψT, zero_smul, map_zero] at hb
    -- put them together
    have hXint : IntervalIntegrable (fun t => deriv ψ t * (G.flat (G.j (u t))) v) volume 0 T :=
      intervalIntegrable_of_integrable_μT hT.le
        ((hflat.apply_continuousLinearMap v).locallyIntegrable
          |>.integrable_smul_left_of_hasCompactSupport hψ'.continuous hψc.deriv)
    have hYint : IntervalIntegrable
        (fun t => deriv ψ t * (∫ τ in (0 : ℝ)..t, g τ) v) volume 0 T :=
      intervalIntegrable_of_integrable_μT hT.le
        ((hGint.apply_continuousLinearMap v).locallyIntegrable
          |>.integrable_smul_left_of_hasCompactSupport hψ'.continuous hψc.deriv)
    have hrw : ∀ t : ℝ, (deriv ψ t • (G.flat (G.j (u t)) - ∫ τ in (0 : ℝ)..t, g τ)) v
        = deriv ψ t * (G.flat (G.j (u t))) v - deriv ψ t * (∫ τ in (0 : ℝ)..t, g τ) v := by
      intro t
      simp only [smul_apply, sub_apply, smul_eq_mul,
        mul_sub]
    simp only [hrw]
    rw [intervalIntegral.integral_sub hXint hYint]
    simp only [GelfandTriple.flat_apply]
    have hbb : ∫ t in (0 : ℝ)..T, deriv ψ t * (∫ τ in (0 : ℝ)..t, g τ) v
        = -∫ t in (0 : ℝ)..T, ψ t * (g t) v := by
      have hb' := hb
      simp only [smul_eq_mul, map_smul] at hb' ⊢
      rw [hb']
      simp
    have haa : ∫ t in (0 : ℝ)..T, deriv ψ t * ⟪G.j (u t), G.j v⟫_ℝ
        = -∫ t in (0 : ℝ)..T, ψ t * (g t) v := by
      simpa only [smul_eq_mul] using ha
    rw [haa, hbb, sub_self]
  obtain ⟨c, hc⟩ := ae_eq_const_of_integral_deriv_smul_eq_zero hT hwint hyp
  refine ⟨c, ?_⟩
  filter_upwards [hc] with t ht
  exact sub_eq_iff_eq_add.mp ht

theorem integral_inner_deriv_eq (G : GelfandTriple V H) {T : ℝ} (hT : 0 < T) {u : ℝ → V}
    {g : ℝ → StrongDual ℝ V} (hg : MeasureTheory.Integrable g (μT T)) {c : StrongDual ℝ V}
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ) {φ : ℝ → V}
    (hφ : ContDiff ℝ 1 φ) :
    ∫ t in (0 : ℝ)..T, ⟪G.j (u t), G.j (deriv φ t)⟫_ℝ
      = (c + ∫ τ in (0 : ℝ)..T, g τ) (φ T) - c (φ 0) - ∫ t in (0 : ℝ)..T, g t (φ t) := by
  have hdc : Continuous (deriv φ) := hφ.continuous_deriv_one
  have hc' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc 0 T →
      G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ :=
    (ae_restrict_iff' measurableSet_Ioc).mp hc
  have step1 : ∫ t in (0 : ℝ)..T, ⟪G.j (u t), G.j (deriv φ t)⟫_ℝ
      = ∫ t in (0 : ℝ)..T, (c (deriv φ t) + (∫ τ in (0 : ℝ)..t, g τ) (deriv φ t)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hc'] with t ht htI
    rw [Set.uIoc_of_le hT.le] at htI
    rw [← GelfandTriple.flat_apply, ht htI]
    rfl
  have hcint : IntervalIntegrable (fun t => c (deriv φ t)) volume 0 T :=
    (c.continuous.comp hdc).intervalIntegrable 0 T
  have hGint : MeasureTheory.Integrable (fun t => ∫ τ in (0 : ℝ)..t, g τ) (μT T) :=
    integrable_primitive hT hg
  have hGint2 : IntervalIntegrable
      (fun t => (∫ τ in (0 : ℝ)..t, g τ) (deriv φ t)) volume 0 T :=
    intervalIntegrable_of_integrable_μT hT.le (integrable_apply_of_continuous hGint hdc)
  have hcc : ∫ t in (0 : ℝ)..T, c (deriv φ t) = c (φ T) - c (φ 0) := by
    rw [ContinuousLinearMap.intervalIntegral_comp_comm _ (hdc.intervalIntegrable 0 T),
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hφ.differentiable one_ne_zero x)
        (hdc.intervalIntegrable 0 T), map_sub]
  rw [step1, intervalIntegral.integral_add hcint hGint2, hcc,
    integral_integral_apply_deriv hT hg hφ]
  simp only [add_apply]
  ring

omit [CompleteSpace V] in
/-- `t ↦ A t (u t)` is integrable whenever `u` is. -/
theorem integrable_form_apply_left {T : ℝ} {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α : ℝ}
    (hA : IsFormFamily T A M α) {u : ℝ → V} (hu : MeasureTheory.Integrable u (μT T)) :
    MeasureTheory.Integrable (fun t => A t (u t)) (μT T) := by
  refine Integrable.mono' (hu.norm.const_mul M)
    (aestronglyMeasurable_apply₂ hA.meas hu.aestronglyMeasurable) ?_
  filter_upwards with t
  exact (A t).le_opNorm (u t) |>.trans (mul_le_mul_of_nonneg_right (hA.bound t) (norm_nonneg _))

omit [CompleteSpace V] in
/-- `t ↦ A t (u t)` is in `L²(0,T;V')` whenever `u` is in `L²(0,T;V)`. -/
theorem memLp_form_apply_left {T : ℝ} {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α : ℝ}
    (hA : IsFormFamily T A M α) {u : ℝ → V} (hu : MeasureTheory.MemLp u 2 (μT T)) :
    MeasureTheory.MemLp (fun t => A t (u t)) 2 (μT T) := by
  refine MemLp.mono' (hu.norm.const_mul M)
    (aestronglyMeasurable_apply₂ hA.meas hu.aestronglyMeasurable) ?_
  filter_upwards with t
  exact (A t).le_opNorm (u t) |>.trans (mul_le_mul_of_nonneg_right (hA.bound t) (norm_nonneg _))

theorem const_eq_flat_of_variational (G : GelfandTriple V H) {T : ℝ} (hT : 0 < T)
    {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α : ℝ} (hA : IsFormFamily T A M α)
    {f : ℝ → StrongDual ℝ V} (hf : MeasureTheory.MemLp f 2 (μT T)) {u₀ : H} {u : ℝ → V}
    (hu : IsVariationalSolution G T A f u₀ u) {c : StrongDual ℝ V}
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, (fun τ => f τ - A τ (u τ)) τ) :
    c = G.flat u₀ := by
  obtain ⟨huL2, hvar⟩ := hu
  have hu1 : MeasureTheory.Integrable u (μT T) := huL2.integrable one_le_two
  have hf1 : MeasureTheory.Integrable f (μT T) := hf.integrable one_le_two
  have hAu : MeasureTheory.Integrable (fun t => A t (u t)) (μT T) :=
    integrable_form_apply_left hA hu1
  have hgint : MeasureTheory.Integrable (fun τ => f τ - A τ (u τ)) (μT T) := hf1.sub hAu
  have hflat : MeasureTheory.Integrable (fun t => G.flat (G.j (u t))) (μT T) :=
    ContinuousLinearMap.integrable_comp (G.flat ∘L G.j) hu1
  -- a smooth cutoff `B` with `B 0 = 1` and `B = 0` on `[T, ∞)`
  have h1 : (0 : ℝ) < T / 4 := by positivity
  have h2 : T / 4 < T / 2 := by linarith
  let B : ContDiffBump (0 : ℝ) := ⟨T / 4, T / 2, h1, h2⟩
  have hBsm : ContDiff ℝ 1 (B : ℝ → ℝ) := B.contDiff
  have hB0 : B 0 = 1 := B.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt h1))
  have hBT : ∀ t, T ≤ t → B t = 0 := by
    intro t ht
    refine B.zero_of_le_dist ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)]
    show T / 2 ≤ t
    linarith
  refine ContinuousLinearMap.ext fun v => ?_
  have hφ1 : ContDiff ℝ 1 (fun t => B t • v) := hBsm.smul contDiff_const
  have hφT : IsTestV T (fun t => B t • v) := ⟨hφ1, fun t ht => by simp [hBT t ht]⟩
  have hφ0 : B 0 • v = v := by simp [hB0]
  have hφTz : B T • v = (0 : V) := by simp [hBT T le_rfl]
  have hφcont : Continuous (fun t => B t • v) := hφ1.continuous
  have hdc : Continuous (deriv (fun t => B t • v)) := hφ1.continuous_deriv_one
  have hvar' := hvar (fun t => B t • v) hφT
  have hibp := integral_inner_deriv_eq G hT hgint hc hφ1
  rw [hφTz, map_zero, hφ0] at hibp
  have hX : IntervalIntegrable
      (fun t => ⟪G.j (u t), G.j (deriv (fun s => B s • v) t)⟫_ℝ) volume 0 T := by
    have : IntervalIntegrable
        (fun t => G.flat (G.j (u t)) (deriv (fun s => B s • v) t)) volume 0 T :=
      intervalIntegrable_of_integrable_μT hT.le (integrable_apply_of_continuous hflat hdc)
    simpa only [GelfandTriple.flat_apply] using this
  have hXn : IntervalIntegrable
      (fun t => -(⟪G.j (u t), G.j (deriv (fun s => B s • v) t)⟫_ℝ)) volume 0 T := hX.neg
  have hY : IntervalIntegrable (fun t => A t (u t) (B t • v)) volume 0 T :=
    intervalIntegrable_of_integrable_μT hT.le (integrable_apply_of_continuous hAu hφcont)
  have hZ : IntervalIntegrable (fun t => f t (B t • v)) volume 0 T :=
    intervalIntegrable_of_integrable_μT hT.le (integrable_apply_of_continuous hf1 hφcont)
  rw [intervalIntegral.integral_add hXn hY, intervalIntegral.integral_neg, hφ0] at hvar'
  have hsub : ∫ t in (0 : ℝ)..T, (f t - A t (u t)) (B t • v)
      = (∫ t in (0 : ℝ)..T, f t (B t • v)) - ∫ t in (0 : ℝ)..T, A t (u t) (B t • v) := by
    simp only [sub_apply]
    exact intervalIntegral.integral_sub hZ hY
  rw [hsub] at hibp
  rw [GelfandTriple.flat_apply]
  linarith [hvar', hibp]

theorem hasWeakDerivV'_of_variational (G : GelfandTriple V H) {T : ℝ} (hT : 0 < T)
    {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α : ℝ} (hA : IsFormFamily T A M α)
    {f : ℝ → StrongDual ℝ V} (hf : MeasureTheory.MemLp f 2 (μT T)) {u₀ : H} {u : ℝ → V}
    (hu : IsVariationalSolution G T A f u₀ u) :
    HasWeakDerivV' G T u (fun t => f t - A t (u t)) ∧
      MeasureTheory.MemLp (fun t => f t - A t (u t)) 2 (μT T) := by
  obtain ⟨huL2, hvar⟩ := hu
  have hu1 : MeasureTheory.Integrable u (μT T) := huL2.integrable one_le_two
  have hf1 : MeasureTheory.Integrable f (μT T) := hf.integrable one_le_two
  have hflat : MeasureTheory.Integrable (fun t => G.flat (G.j (u t))) (μT T) :=
    ContinuousLinearMap.integrable_comp (G.flat ∘L G.j) hu1
  have hAu : MeasureTheory.Integrable (fun t => A t (u t)) (μT T) :=
    integrable_form_apply_left hA hu1
  refine ⟨?_, hf.sub (memLp_form_apply_left hA huL2)⟩
  intro φ hφ hφc hφs
  have hφcont : Continuous φ := hφ.continuous
  have hdc : Continuous (deriv φ) := hφ.continuous_deriv_one
  have hφT : IsTestV T φ :=
    ⟨hφ, fun t ht => image_eq_zero_of_notMem_tsupport fun hh => absurd ht (not_le.2 (hφs hh).2)⟩
  have hφ0 : φ 0 = 0 :=
    image_eq_zero_of_notMem_tsupport fun hh => absurd (hφs hh).1 (lt_irrefl 0)
  have hvar' := hvar φ hφT
  -- integrability of the three integrands
  have hX : IntervalIntegrable (fun t => ⟪G.j (u t), G.j (deriv φ t)⟫_ℝ) volume 0 T := by
    have : IntervalIntegrable (fun t => G.flat (G.j (u t)) (deriv φ t)) volume 0 T :=
      intervalIntegrable_of_integrable_μT hT.le (integrable_apply_of_continuous hflat hdc)
    simpa only [GelfandTriple.flat_apply] using this
  have hY : IntervalIntegrable (fun t => A t (u t) (φ t)) volume 0 T :=
    intervalIntegrable_of_integrable_μT hT.le (integrable_apply_of_continuous hAu hφcont)
  have hZ : IntervalIntegrable (fun t => f t (φ t)) volume 0 T :=
    intervalIntegrable_of_integrable_μT hT.le (integrable_apply_of_continuous hf1 hφcont)
  have hXn : IntervalIntegrable (fun t => -(⟪G.j (u t), G.j (deriv φ t)⟫_ℝ)) volume 0 T := hX.neg
  rw [intervalIntegral.integral_add hXn hY, intervalIntegral.integral_neg, hφ0, map_zero,
    inner_zero_right, add_zero] at hvar'
  have hsub : ∫ t in (0 : ℝ)..T, (f t - A t (u t)) (φ t)
      = (∫ t in (0 : ℝ)..T, f t (φ t)) - ∫ t in (0 : ℝ)..T, A t (u t) (φ t) := by
    simp only [sub_apply]
    exact intervalIntegral.integral_sub hZ hY
  show ∫ t in (0 : ℝ)..T, ⟪G.j (u t), G.j (deriv φ t)⟫_ℝ
      = -∫ t in (0 : ℝ)..T, (f t - A t (u t)) (φ t)
  rw [hsub]
  linarith [hvar']

end LionsC12

end
