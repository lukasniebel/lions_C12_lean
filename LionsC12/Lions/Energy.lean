module

public import LionsC12.Lions.Gelfand
public import LionsC12.Lions.WeakDeriv
public import LionsC12.Lions.Steklov
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The Lions–Magenes lemma

For `u ∈ W(0,T) = {u ∈ L²(0,T;V) : u' ∈ L²(0,T;V')}` we construct a continuous
representative `ũ : [0,T) → H` and prove the energy identity

`‖ũ(t)‖²_H − ‖ũ(s)‖²_H = 2 ∫_s^t ⟨g(τ), u(τ)⟩ dτ`.

The proof goes through (double) Steklov averages, for which the identity is a
consequence of the fundamental theorem of calculus, and then passes to the limit.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Filter
open scoped InnerProductSpace ENNReal

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `u ∈ W(0,T) := {u ∈ L²(0,T;V) : u' ∈ L²(0,T;V')}`. -/
structure MemW (G : GelfandTriple V H) (T : ℝ) (u : ℝ → V) (g : ℝ → StrongDual ℝ V) : Prop where
  memLp_u : MeasureTheory.MemLp u 2 (μT T)
  memLp_g : MeasureTheory.MemLp g 2 (μT T)
  weak : HasWeakDerivV' G T u g

/-! ### Steklov averages of continuous functions -/

section SteklovAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The Steklov average of a *continuous* function is differentiable, with derivative
`(1/h) • (u (t + h) − u t)`. -/
theorem hasDerivAt_steklov_of_continuous {h : ℝ} {u : ℝ → E} (hu : Continuous u) (t : ℝ) :
    HasDerivAt (steklov h u) ((1 / h) • (u (t + h) - u t)) t := by
  have hint : ∀ a b : ℝ, IntervalIntegrable u volume a b := fun a b => hu.intervalIntegrable a b
  have hH : ∀ s : ℝ, HasDerivAt (fun s => ∫ σ in (0 : ℝ)..s, u σ) (u s) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (hint 0 s)
      (hu.stronglyMeasurableAtFilter _ _) hu.continuousAt
  have hrw : (steklov h u) =
      fun t => (1 / h) • ((∫ σ in (0 : ℝ)..(t + h), u σ) - ∫ σ in (0 : ℝ)..t, u σ) := by
    funext t
    unfold steklov
    congr 1
    rw [eq_sub_iff_add_eq, add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t (t + h))
  rw [hrw]
  have d1 : HasDerivAt (fun t : ℝ => ∫ σ in (0 : ℝ)..(t + h), u σ) (u (t + h)) t :=
    HasDerivAt.comp_add_const t h (hH (t + h))
  exact (d1.sub (hH t)).const_smul (1 / h : ℝ)

/-- A continuous linear map commutes with Steklov averaging. -/
theorem clm_steklov {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) {h : ℝ} {u : ℝ → E} (hu : MeasureTheory.LocallyIntegrable u) (t : ℝ) :
    L (steklov h u t) = steklov h (fun τ => L (u τ)) t := by
  unfold steklov
  rw [L.map_smul, L.intervalIntegral_comp_comm (intervalIntegrable_of_locallyIntegrable hu _ _)]

/-- Steklov average of a constant. -/
@[simp] theorem steklov_const {h : ℝ} (hh : 0 < h) (e : E) (t : ℝ) :
    steklov h (fun _ => e) t = e := by
  unfold steklov
  rw [intervalIntegral.integral_const, smul_smul]
  simp only [add_sub_cancel_left, one_div]
  rw [inv_mul_cancel₀ hh.ne', one_smul]

/-- Steklov average of a sum with a constant. -/
theorem steklov_const_add {h : ℝ} (hh : 0 < h) (e : E) {u : ℝ → E}
    (hu : MeasureTheory.LocallyIntegrable u) (t : ℝ) :
    steklov h (fun τ => e + u τ) t = e + steklov h u t := by
  unfold steklov
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (intervalIntegrable_of_locallyIntegrable hu _ _), smul_add]
  congr 1
  rw [intervalIntegral.integral_const, smul_smul]
  simp only [add_sub_cancel_left, one_div]
  rw [inv_mul_cancel₀ hh.ne', one_smul]

omit [CompleteSpace E] in
/-- Steklov averaging preserves local integrability (the average is continuous). -/
theorem locallyIntegrable_steklov (h : ℝ) {u : ℝ → E}
    (hu : MeasureTheory.LocallyIntegrable u) :
    MeasureTheory.LocallyIntegrable (steklov h u) :=
  (continuous_steklov h hu).locallyIntegrable

end SteklovAux

section NormSq

variable {E : Type*} [NormedAddCommGroup E]

theorem integrable_norm_sq {μ : MeasureTheory.Measure ℝ} {f : ℝ → E}
    (hf : MeasureTheory.MemLp f 2 μ) : MeasureTheory.Integrable (fun a => ‖f a‖ ^ 2) μ := by
  have h := hf.integrable_norm_rpow (by norm_num) (by norm_num)
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2] at h
  refine h.congr (Filter.Eventually.of_forall fun a => ?_)
  simp only
  rw [← Real.rpow_natCast (‖f a‖) 2]
  norm_num

/-- `∫ ‖f‖²` in terms of the `L²`-norm. -/
theorem integral_norm_sq_eq {μ : MeasureTheory.Measure ℝ} {f : ℝ → E}
    (hf : MeasureTheory.MemLp f 2 μ) :
    ∫ a, ‖f a‖ ^ 2 ∂μ = ((MeasureTheory.eLpNorm f 2 μ).toReal) ^ 2 := by
  have hnn : 0 ≤ ∫ a, ‖f a‖ ^ (2 : ℝ) ∂μ :=
    MeasureTheory.integral_nonneg fun a => by positivity
  have key := hf.eLpNorm_eq_integral_rpow_norm (p := 2) (by norm_num) (by norm_num)
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2] at key
  rw [key, ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast _ 2, ← Real.rpow_mul hnn]
  norm_num

end NormSq

/-! ### The energy identity for a `C¹` function -/

theorem uIcc_subset_Icc_of_mem {a b c d : ℝ} (ha : a ∈ Set.Icc c d) (hb : b ∈ Set.Icc c d) :
    Set.uIcc a b ⊆ Set.Icc c d := by
  have hcd : c ≤ d := le_trans ha.1 ha.2
  rw [← Set.uIcc_of_le hcd]
  exact Set.uIcc_subset_uIcc (by rwa [Set.uIcc_of_le hcd]) (by rwa [Set.uIcc_of_le hcd])

/-- **Abstract energy identity.**  If `U : ℝ → V` is differentiable with continuous derivative `D`
and the functional `G.flat (G.j (D τ))` coincides with `Γ τ` on `[s,t]`, then
`‖j U t‖² − ‖j U s‖² = 2 ∫_s^t Γ τ (U τ)`. -/
theorem energy_of_hasDerivAt (G : GelfandTriple V H) {U D : ℝ → V}
    (hU : ∀ τ, HasDerivAt U (D τ) τ) (hDc : Continuous D)
    {Γ : ℝ → StrongDual ℝ V} {s t : ℝ}
    (hcompat : ∀ τ ∈ Set.uIcc s t, G.flat (G.j (D τ)) = Γ τ) :
    ‖G.j (U t)‖ ^ 2 - ‖G.j (U s)‖ ^ 2 = 2 * ∫ τ in s..t, Γ τ (U τ) := by
  have hUc : Continuous U := by
    refine continuous_iff_continuousAt.2 fun τ => (hU τ).continuousAt
  -- the derivative of `τ ↦ j (U τ)`
  have hjU : ∀ τ, HasDerivAt (fun τ => G.j (U τ)) (G.j (D τ)) τ := fun τ =>
    (G.j.hasFDerivAt (x := U τ)).comp_hasDerivAt τ (hU τ)
  -- the derivative of the squared norm
  have hN : ∀ τ, HasDerivAt (fun τ => ⟪G.j (U τ), G.j (U τ)⟫_ℝ)
      (⟪G.j (U τ), G.j (D τ)⟫_ℝ + ⟪G.j (D τ), G.j (U τ)⟫_ℝ) τ := fun τ =>
    (hjU τ).inner ℝ (hjU τ)
  have hcontD : Continuous fun τ => ⟪G.j (U τ), G.j (D τ)⟫_ℝ + ⟪G.j (D τ), G.j (U τ)⟫_ℝ := by
    have h1 : Continuous fun τ => G.j (U τ) := G.j.continuous.comp hUc
    have h2 : Continuous fun τ => G.j (D τ) := G.j.continuous.comp hDc
    exact (h1.inner h2).add (h2.inner h1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun τ => ⟪G.j (U τ), G.j (U τ)⟫_ℝ)
    (f' := fun τ => ⟪G.j (U τ), G.j (D τ)⟫_ℝ + ⟪G.j (D τ), G.j (U τ)⟫_ℝ)
    (fun τ _ => hN τ) (hcontD.intervalIntegrable s t)
  have hrw : ∫ τ in s..t, (⟪G.j (U τ), G.j (D τ)⟫_ℝ + ⟪G.j (D τ), G.j (U τ)⟫_ℝ)
      = ∫ τ in s..t, 2 * Γ τ (U τ) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    have h1 : ⟪G.j (D τ), G.j (U τ)⟫_ℝ = Γ τ (U τ) := by
      rw [← GelfandTriple.flat_apply, hcompat τ hτ]
    have h2 : ⟪G.j (U τ), G.j (D τ)⟫_ℝ = Γ τ (U τ) := by
      rw [real_inner_comm]; exact h1
    rw [h1, h2]; ring
  rw [hrw, intervalIntegral.integral_const_mul] at hFTC
  rw [hFTC, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- A pair `(U, Γ)` such that `U` is differentiable with continuous derivative `D` and
`G.flat (G.j (D τ)) = Γ τ` on `[0,b]`.  This is the structure enjoyed by the Steklov averages,
and it is stable under differences. -/
structure RegPair (G : GelfandTriple V H) (b : ℝ) (U D : ℝ → V) (Γ : ℝ → StrongDual ℝ V) :
    Prop where
  hasDerivAt : ∀ τ, HasDerivAt U (D τ) τ
  continuous : Continuous D
  compat : ∀ τ ∈ Set.Icc (0 : ℝ) b, G.flat (G.j (D τ)) = Γ τ

namespace RegPair

variable {G : GelfandTriple V H} {b : ℝ} {U D : ℝ → V} {Γ : ℝ → StrongDual ℝ V}

theorem continuous_fun (hP : RegPair G b U D Γ) : Continuous U :=
  continuous_iff_continuousAt.2 fun τ => (hP.hasDerivAt τ).continuousAt

/-- The energy identity holds for a regular pair. -/
theorem energy (hP : RegPair G b U D Γ) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) b)
    (ht : t ∈ Set.Icc (0 : ℝ) b) :
    ‖G.j (U t)‖ ^ 2 - ‖G.j (U s)‖ ^ 2 = 2 * ∫ τ in s..t, Γ τ (U τ) :=
  energy_of_hasDerivAt G hP.hasDerivAt hP.continuous
    fun τ hτ => hP.compat τ (uIcc_subset_Icc_of_mem hs ht hτ)

theorem mono (hP : RegPair G b U D Γ) {b' : ℝ} (hb : b' ≤ b) : RegPair G b' U D Γ :=
  ⟨hP.hasDerivAt, hP.continuous, fun τ hτ => hP.compat τ ⟨hτ.1, le_trans hτ.2 hb⟩⟩

theorem sub {U₁ D₁ U₂ D₂ : ℝ → V} {Γ₁ Γ₂ : ℝ → StrongDual ℝ V}
    (h1 : RegPair G b U₁ D₁ Γ₁) (h2 : RegPair G b U₂ D₂ Γ₂) :
    RegPair G b (fun τ => U₁ τ - U₂ τ) (fun τ => D₁ τ - D₂ τ) (fun τ => Γ₁ τ - Γ₂ τ) where
  hasDerivAt := fun τ => (h1.hasDerivAt τ).sub (h2.hasDerivAt τ)
  continuous := h1.continuous.sub h2.continuous
  compat := fun τ hτ => by
    simp only [map_sub, h1.compat τ hτ, h2.compat τ hτ]

/-- On `[0,b]` the functional `Γ` of a regular pair is continuous. -/
theorem continuousOn_dual (hP : RegPair G b U D Γ) : ContinuousOn Γ (Set.Icc (0 : ℝ) b) :=
  ContinuousOn.congr ((G.flat ∘L G.j).continuous.comp hP.continuous).continuousOn
    fun τ hτ => (hP.compat τ hτ).symm

/-- **Uniform bound on `[0,b]`** obtained from the energy identity by averaging the starting
point `s` over `[0,b]`. -/
theorem sup_bound (hP : RegPair G b U D Γ) (hb : 0 < b) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b) :
    ‖G.j (U t)‖ ^ 2 ≤ (1 / b) * (∫ s in Set.Icc (0 : ℝ) b, ‖G.j (U s)‖ ^ 2)
      + 2 * ∫ τ in Set.Icc (0 : ℝ) b, ‖Γ τ‖ * ‖U τ‖ := by
  have hUc : Continuous U := hP.continuous_fun
  have hΓc : ContinuousOn Γ (Set.Icc (0 : ℝ) b) := hP.continuousOn_dual
  set I : ℝ := ∫ τ in Set.Icc (0 : ℝ) b, ‖Γ τ‖ * ‖U τ‖ with hIdef
  have hprodOn : ContinuousOn (fun τ => ‖Γ τ‖ * ‖U τ‖) (Set.Icc (0 : ℝ) b) :=
    hΓc.norm.mul hUc.norm.continuousOn
  have hintI : MeasureTheory.IntegrableOn (fun τ => ‖Γ τ‖ * ‖U τ‖) (Set.Icc (0 : ℝ) b) :=
    hprodOn.integrableOn_compact isCompact_Icc
  -- the pointwise bound with an arbitrary starting point
  have hstep : ∀ s ∈ Set.Icc (0 : ℝ) b, ‖G.j (U t)‖ ^ 2 ≤ ‖G.j (U s)‖ ^ 2 + 2 * I := by
    intro s hs
    have he := hP.energy hs ht
    have hsub : Set.uIoc s t ⊆ Set.Icc (0 : ℝ) b := by
      intro x hx
      rw [Set.uIoc] at hx
      exact ⟨le_of_lt (lt_of_le_of_lt (le_min hs.1 ht.1) hx.1), le_trans hx.2 (max_le hs.2 ht.2)⟩
    have h1 : ‖∫ τ in s..t, Γ τ (U τ)‖ ≤ ∫ τ in Set.uIoc s t, ‖Γ τ (U τ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    have h2 : ∫ τ in Set.uIoc s t, ‖Γ τ (U τ)‖ ≤ ∫ τ in Set.uIoc s t, ‖Γ τ‖ * ‖U τ‖ := by
      refine MeasureTheory.setIntegral_mono_on
        ((hintI.mono hsub le_rfl).mono' ?_ ?_) (hintI.mono hsub le_rfl)
        measurableSet_uIoc fun τ _ => (Γ τ).le_opNorm (U τ)
      · exact ((hΓc.mono hsub).clm_apply (hUc.continuousOn.mono hsub)).norm.aestronglyMeasurable
          measurableSet_uIoc
      · filter_upwards with τ
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact (Γ τ).le_opNorm (U τ)
    have h3 : ∫ τ in Set.uIoc s t, ‖Γ τ‖ * ‖U τ‖ ≤ I :=
      MeasureTheory.setIntegral_mono_set hintI
        (Filter.Eventually.of_forall fun τ => by positivity)
        hsub.eventuallyLE
    have h4 : ‖∫ τ in s..t, Γ τ (U τ)‖ ≤ I := le_trans h1 (le_trans h2 h3)
    rw [Real.norm_eq_abs] at h4
    have := abs_le.1 h4
    linarith [he]
  -- average the bound over `s ∈ [0,b]`
  have hcont2 : ContinuousOn (fun s => ‖G.j (U s)‖ ^ 2) (Set.Icc (0 : ℝ) b) :=
    (((G.j.continuous.comp hUc).norm).pow 2).continuousOn
  have hint2 : MeasureTheory.IntegrableOn (fun s => ‖G.j (U s)‖ ^ 2) (Set.Icc (0 : ℝ) b) :=
    hcont2.integrableOn_compact isCompact_Icc
  have hconstInt : ∀ c : ℝ, MeasureTheory.IntegrableOn (fun _ : ℝ => c) (Set.Icc (0 : ℝ) b) :=
    fun c => continuousOn_const.integrableOn_compact isCompact_Icc
  have hmono := MeasureTheory.setIntegral_mono_on (hconstInt (‖G.j (U t)‖ ^ 2))
    (hint2.add (hconstInt (2 * I))) measurableSet_Icc hstep
  have hvol : (MeasureTheory.volume).real (Set.Icc (0 : ℝ) b) = b := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
  simp only [Pi.add_apply] at hmono
  rw [MeasureTheory.integral_add hint2 (hconstInt (2 * I))] at hmono
  simp only [MeasureTheory.setIntegral_const, hvol, smul_eq_mul] at hmono
  have hrw : (1 / b) * (∫ s in Set.Icc (0 : ℝ) b, ‖G.j (U s)‖ ^ 2) + 2 * I
      = ((∫ s in Set.Icc (0 : ℝ) b, ‖G.j (U s)‖ ^ 2) + b * (2 * I)) / b := by
    field_simp
  rw [hrw, le_div_iff₀ hb]
  linarith [hmono, mul_comm b (‖G.j (U t)‖ ^ 2)]

/-- **The uniform bound in purely `L²` terms.**  Combining `RegPair.sup_bound` with
`xy ≤ (x² + y²)/2` and `∫_{[0,b]} ≤ ∫_ℝ` for nonnegative integrands. -/
theorem sup_bound_L2 (hP : RegPair G b U D Γ) (hb : 0 < b)
    (hU2 : MeasureTheory.MemLp U 2 MeasureTheory.volume)
    (hΓ2 : MeasureTheory.MemLp Γ 2 MeasureTheory.volume) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b) :
    ‖G.j (U t)‖ ^ 2 ≤ (1 / b) * ‖G.j‖ ^ 2 * (∫ τ, ‖U τ‖ ^ 2)
      + ((∫ τ, ‖Γ τ‖ ^ 2) + ∫ τ, ‖U τ‖ ^ 2) := by
  have hUc : Continuous U := hP.continuous_fun
  have hΓc : ContinuousOn Γ (Set.Icc (0 : ℝ) b) := hP.continuousOn_dual
  have base := hP.sup_bound hb ht
  have hnnU : (0 : ℝ → ℝ) ≤ᵐ[MeasureTheory.volume] fun τ => ‖U τ‖ ^ 2 :=
    Filter.Eventually.of_forall fun τ => by positivity
  have hnnΓ : (0 : ℝ → ℝ) ≤ᵐ[MeasureTheory.volume] fun τ => ‖Γ τ‖ ^ 2 :=
    Filter.Eventually.of_forall fun τ => by positivity
  have hUsq : MeasureTheory.IntegrableOn (fun s => ‖U s‖ ^ 2) (Set.Icc (0 : ℝ) b) :=
    ((hUc.norm.pow 2).continuousOn).integrableOn_compact isCompact_Icc
  have hΓsq : MeasureTheory.IntegrableOn (fun s => ‖Γ s‖ ^ 2) (Set.Icc (0 : ℝ) b) :=
    ((hΓc.norm.pow 2)).integrableOn_compact isCompact_Icc
  -- first term
  have hT1 : (∫ s in Set.Icc (0 : ℝ) b, ‖G.j (U s)‖ ^ 2) ≤ ‖G.j‖ ^ 2 * ∫ τ, ‖U τ‖ ^ 2 := by
    have hint_jU : MeasureTheory.IntegrableOn (fun s => ‖G.j (U s)‖ ^ 2) (Set.Icc (0 : ℝ) b) :=
      (((G.j.continuous.comp hUc).norm.pow 2).continuousOn).integrableOn_compact isCompact_Icc
    calc (∫ s in Set.Icc (0 : ℝ) b, ‖G.j (U s)‖ ^ 2)
        ≤ ∫ s in Set.Icc (0 : ℝ) b, ‖G.j‖ ^ 2 * ‖U s‖ ^ 2 := by
          refine MeasureTheory.setIntegral_mono_on hint_jU (hUsq.const_mul _)
            measurableSet_Icc fun s _ => ?_
          have h1 := G.j.le_opNorm (U s)
          have h2 : (0 : ℝ) ≤ ‖G.j (U s)‖ := norm_nonneg _
          nlinarith [norm_nonneg (U s), norm_nonneg G.j]
      _ = ‖G.j‖ ^ 2 * ∫ s in Set.Icc (0 : ℝ) b, ‖U s‖ ^ 2 := MeasureTheory.integral_const_mul _ _
      _ ≤ ‖G.j‖ ^ 2 * ∫ τ, ‖U τ‖ ^ 2 := by
          have h2 : (∫ τ in Set.Icc (0 : ℝ) b, ‖U τ‖ ^ 2) ≤ ∫ τ, ‖U τ‖ ^ 2 :=
            MeasureTheory.setIntegral_le_integral (integrable_norm_sq hU2) hnnU
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
  -- second term
  have hT2 : (∫ τ in Set.Icc (0 : ℝ) b, ‖Γ τ‖ * ‖U τ‖)
      ≤ ((∫ τ, ‖Γ τ‖ ^ 2) + ∫ τ, ‖U τ‖ ^ 2) / 2 := by
    have hintP : MeasureTheory.IntegrableOn (fun τ => ‖Γ τ‖ * ‖U τ‖) (Set.Icc (0 : ℝ) b) :=
      (hΓc.norm.mul hUc.norm.continuousOn).integrableOn_compact isCompact_Icc
    calc (∫ τ in Set.Icc (0 : ℝ) b, ‖Γ τ‖ * ‖U τ‖)
        ≤ ∫ τ in Set.Icc (0 : ℝ) b, (‖Γ τ‖ ^ 2 + ‖U τ‖ ^ 2) / 2 := by
          refine MeasureTheory.setIntegral_mono_on hintP ((hΓsq.add hUsq).div_const 2)
            measurableSet_Icc fun τ _ => ?_
          nlinarith [sq_nonneg (‖Γ τ‖ - ‖U τ‖)]
      _ = ((∫ τ in Set.Icc (0 : ℝ) b, ‖Γ τ‖ ^ 2) + ∫ τ in Set.Icc (0 : ℝ) b, ‖U τ‖ ^ 2) / 2 := by
          rw [MeasureTheory.integral_div, MeasureTheory.integral_add hΓsq hUsq]
      _ ≤ ((∫ τ, ‖Γ τ‖ ^ 2) + ∫ τ, ‖U τ‖ ^ 2) / 2 := by
          have h1 : (∫ τ in Set.Icc (0 : ℝ) b, ‖Γ τ‖ ^ 2) ≤ ∫ τ, ‖Γ τ‖ ^ 2 :=
            MeasureTheory.setIntegral_le_integral (integrable_norm_sq hΓ2) hnnΓ
          have h2 : (∫ τ in Set.Icc (0 : ℝ) b, ‖U τ‖ ^ 2) ≤ ∫ τ, ‖U τ‖ ^ 2 :=
            MeasureTheory.setIntegral_le_integral (integrable_norm_sq hU2) hnnU
          linarith
  have hbpos : (0 : ℝ) < 1 / b := by positivity
  have hstep1 := mul_le_mul_of_nonneg_left hT1 hbpos.le
  linarith [base, hT2]

end RegPair

/-- **The double Steklov average is a regular pair.**  `U` plays the role of `steklov h ū`,
`W` of `steklov h w` (the primitive of `Γ`), `Γ` of `steklov h ḡ`. -/
theorem regPair_steklov (G : GelfandTriple V H) {T h : ℝ} (hh : 0 < h)
    {U : ℝ → V} (hUc : Continuous U)
    {W Γ : ℝ → StrongDual ℝ V}
    (hWΓ : ∀ σ τ : ℝ, W τ - W σ = ∫ ρ in σ..τ, Γ ρ)
    (hflat : ∀ σ ∈ Set.Icc (0 : ℝ) (T - h), G.flat (G.j (U σ)) = W σ) :
    RegPair G (T - 2 * h) (steklov h U) (fun τ => (1 / h) • (U (τ + h) - U τ)) (steklov h Γ) where
  hasDerivAt := fun τ => hasDerivAt_steklov_of_continuous hUc τ
  continuous := ((hUc.comp (continuous_id.add continuous_const)).sub hUc).const_smul (1 / h : ℝ)
  compat := by
    intro τ hτ'
    have h1 : G.flat (G.j (U τ)) = W τ := hflat τ ⟨hτ'.1, by linarith [hτ'.2]⟩
    have h2 : G.flat (G.j (U (τ + h))) = W (τ + h) :=
      hflat _ ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
    have hkey : G.flat (G.j ((1 / h) • (U (τ + h) - U τ))) = (1 / h) • (W (τ + h) - W τ) := by
      simp only [map_smul, map_sub, h1, h2]
    rw [hkey, hWΓ τ (τ + h)]
    rfl

/-! ### The concrete Steklov data -/

section Concrete

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The primitive of a locally integrable function is continuous. -/
theorem continuous_primitive_add_const {gb : ℝ → E} (hgb : MeasureTheory.LocallyIntegrable gb)
    (c : E) : Continuous fun t => c + ∫ ρ in (0 : ℝ)..t, gb ρ :=
  continuous_const.add
    (intervalIntegral.continuous_primitive
      (fun a b => intervalIntegrable_of_locallyIntegrable hgb a b) 0)

/-- The Steklov average of `c + ∫₀^· gb` is differentiable with derivative `steklov h gb`. -/
theorem hasDerivAt_steklov_primitive {h : ℝ} (hh : 0 < h) {gb : ℝ → E}
    (hgb : MeasureTheory.LocallyIntegrable gb) (c : E) (t : ℝ) :
    HasDerivAt (steklov h fun τ => c + ∫ ρ in (0 : ℝ)..τ, gb ρ) (steklov h gb t) t := by
  have hP : MeasureTheory.LocallyIntegrable fun τ : ℝ => ∫ ρ in (0 : ℝ)..τ, gb ρ :=
    (intervalIntegral.continuous_primitive
      (fun a b => intervalIntegrable_of_locallyIntegrable hgb a b) 0).locallyIntegrable
  have hrw : (steklov h fun τ => c + ∫ ρ in (0 : ℝ)..τ, gb ρ)
      = fun t => c + steklov h (fun τ => ∫ ρ in (0 : ℝ)..τ, gb ρ) t := by
    funext t; exact steklov_const_add hh c hP t
  rw [hrw]
  simpa using ((hasDerivAt_steklov_integral h hgb t).const_add c)

/-- Exact increment formula for the Steklov average of a primitive. -/
theorem steklov_primitive_sub {h : ℝ} (hh : 0 < h) {gb : ℝ → E}
    (hgb : MeasureTheory.LocallyIntegrable gb) (c : E) (σ τ : ℝ) :
    (steklov h fun t => c + ∫ ρ in (0 : ℝ)..t, gb ρ) τ
      - (steklov h fun t => c + ∫ ρ in (0 : ℝ)..t, gb ρ) σ = ∫ ρ in σ..τ, steklov h gb ρ := by
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_steklov_primitive hh hgb c x)
    ((continuous_steklov h hgb).intervalIntegrable σ τ)

end Concrete

/-- The Steklov average intertwines `flat ∘ j` with the `V'`-valued primitive, on the range of
times for which the averaging window stays inside `(0,T]`. -/
theorem flat_j_steklov_eq (G : GelfandTriple V H) {T h : ℝ} (hh : 0 < h)
    {ub : ℝ → V} (hub : MeasureTheory.LocallyIntegrable ub)
    {w : ℝ → StrongDual ℝ V}
    (hae : ∀ᵐ τ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      τ ∈ Set.Ioc (0 : ℝ) T → G.flat (G.j (ub τ)) = w τ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) (T - h)) :
    G.flat (G.j (steklov h ub σ)) = steklov h w σ := by
  have hcomp : (G.flat ∘L G.j) (steklov h ub σ)
      = steklov h (fun τ => (G.flat ∘L G.j) (ub τ)) σ := clm_steklov _ hub σ
  simp only [ContinuousLinearMap.comp_apply] at hcomp
  rw [hcomp]
  unfold steklov
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hae] with τ hτ hmem
  refine hτ ?_
  rw [Set.uIoc_of_le (by linarith)] at hmem
  exact ⟨lt_of_le_of_lt hσ.1 hmem.1, le_trans hmem.2 (by linarith [hσ.2])⟩

/-- Extension by zero outside `(0,T]`. -/
def zext {E : Type*} [Zero E] (T : ℝ) (f : ℝ → E) : ℝ → E := (Set.Ioc 0 T).indicator f

theorem integrable_zext {E : Type*} [NormedAddCommGroup E] {T : ℝ} {f : ℝ → E}
    (hf : MeasureTheory.Integrable f (μT T)) :
    MeasureTheory.Integrable (zext T f) MeasureTheory.volume :=
  (MeasureTheory.integrable_indicator_iff measurableSet_Ioc).2 hf

theorem memLp_zext {E : Type*} [NormedAddCommGroup E] {T : ℝ} {f : ℝ → E}
    (hf : MeasureTheory.MemLp f 2 (μT T)) :
    MeasureTheory.MemLp (zext T f) 2 MeasureTheory.volume :=
  (MeasureTheory.memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).2 hf

theorem locallyIntegrable_zext {E : Type*} [NormedAddCommGroup E] {T : ℝ} {f : ℝ → E}
    (hf : MeasureTheory.Integrable f (μT T)) :
    MeasureTheory.LocallyIntegrable (zext T f) :=
  (integrable_zext hf).locallyIntegrable

/-- **The double Steklov averages of the data form a regular pair on `[0, T − 2h]`.** -/
theorem regPair_steklov_data (G : GelfandTriple V H) {T : ℝ}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {c : StrongDual ℝ V}
    (hu : MeasureTheory.Integrable u (μT T)) (hg : MeasureTheory.Integrable g (μT T))
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ)
    {h : ℝ} (hh : 0 < h) :
    RegPair G (T - 2 * h) (steklov h (steklov h (zext T u)))
      (fun τ => (1 / h) • (steklov h (zext T u) (τ + h) - steklov h (zext T u) τ))
      (steklov h (steklov h (zext T g))) := by
  have huL : MeasureTheory.LocallyIntegrable (zext T u) := locallyIntegrable_zext hu
  have hgL : MeasureTheory.LocallyIntegrable (zext T g) := locallyIntegrable_zext hg
  set w : ℝ → StrongDual ℝ V := fun t => c + ∫ ρ in (0 : ℝ)..t, zext T g ρ with hwdef
  have hae : ∀ᵐ τ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      τ ∈ Set.Ioc (0 : ℝ) T → G.flat (G.j (zext T u τ)) = w τ := by
    have hc2 : ∀ᵐ τ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) T)),
        G.flat (G.j (u τ)) = c + ∫ ρ in (0 : ℝ)..τ, g ρ := hc
    have hc' := (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp hc2
    filter_upwards [hc'] with τ hτ hmem
    rw [zext, Set.indicator_of_mem hmem, hτ hmem, hwdef]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with ρ hρ
    rw [Set.uIoc_of_le hmem.1.le] at hρ
    have hρ' : ρ ∈ Set.Ioc (0 : ℝ) T := ⟨hρ.1, le_trans hρ.2 hmem.2⟩
    rw [zext, Set.indicator_of_mem hρ']
  exact regPair_steklov G hh (continuous_steklov h huL) (W := steklov h w)
    (fun σ τ => steklov_primitive_sub hh hgL c σ τ)
    (fun σ hσ => flat_j_steklov_eq G hh huL hae hσ)

/-- **Energy identity for the double Steklov average of the data.** -/
theorem energy_steklov_data (G : GelfandTriple V H) {T : ℝ}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {c : StrongDual ℝ V}
    (hu : MeasureTheory.Integrable u (μT T)) (hg : MeasureTheory.Integrable g (μT T))
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ)
    {h : ℝ} (hh : 0 < h) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) (T - 2 * h)) (ht : t ∈ Set.Icc (0 : ℝ) (T - 2 * h)) :
    ‖G.j (steklov h (steklov h (zext T u)) t)‖ ^ 2
        - ‖G.j (steklov h (steklov h (zext T u)) s)‖ ^ 2
      = 2 * ∫ τ in s..t,
          steklov h (steklov h (zext T g)) τ (steklov h (steklov h (zext T u)) τ) :=
  (regPair_steklov_data G hu hg hc hh).energy hs ht

/-! ### `L²`-convergence of the double Steklov averages -/

section L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem eLpNorm_steklov2_sub_le {h : ℝ} (hh : 0 < h) {u : ℝ → E} (hu : MeasureTheory.MemLp u 2) :
    MeasureTheory.eLpNorm (fun t => steklov h (steklov h u) t - u t) 2 MeasureTheory.volume
      ≤ 2 * MeasureTheory.eLpNorm (fun t => steklov h u t - u t) 2 MeasureTheory.volume := by
  have hloc : MeasureTheory.LocallyIntegrable u := hu.locallyIntegrable one_le_two
  have hSu : MeasureTheory.MemLp (steklov h u) 2 := memLp_steklov hh hu
  have hSloc : MeasureTheory.LocallyIntegrable (steklov h u) :=
    (continuous_steklov h hloc).locallyIntegrable
  have hd : MeasureTheory.MemLp (fun t => steklov h u t - u t) 2 := hSu.sub hu
  have heq : ∀ t, steklov h (steklov h u) t - steklov h u t
      = steklov h (fun τ => steklov h u τ - u τ) t := fun t => steklov_sub hSloc hloc t
  have hsplit : (fun t => steklov h (steklov h u) t - u t)
      = fun t => (steklov h (steklov h u) t - steklov h u t) + (steklov h u t - u t) := by
    funext t; abel
  rw [hsplit]
  have hm1 : MeasureTheory.AEStronglyMeasurable
      (fun t => steklov h (steklov h u) t - steklov h u t) MeasureTheory.volume :=
    ((continuous_steklov h hSloc).sub (continuous_steklov h hloc)).aestronglyMeasurable
  calc MeasureTheory.eLpNorm
        (fun t => (steklov h (steklov h u) t - steklov h u t) + (steklov h u t - u t)) 2
          MeasureTheory.volume
      ≤ MeasureTheory.eLpNorm (fun t => steklov h (steklov h u) t - steklov h u t) 2
            MeasureTheory.volume
          + MeasureTheory.eLpNorm (fun t => steklov h u t - u t) 2 MeasureTheory.volume :=
        MeasureTheory.eLpNorm_add_le one_le_two
    _ ≤ MeasureTheory.eLpNorm (fun t => steklov h u t - u t) 2 MeasureTheory.volume
          + MeasureTheory.eLpNorm (fun t => steklov h u t - u t) 2 MeasureTheory.volume := by
        gcongr
        simp only [heq]
        exact eLpNorm_steklov_le hh hd
    _ = 2 * MeasureTheory.eLpNorm (fun t => steklov h u t - u t) 2 MeasureTheory.volume := by
        rw [two_mul]

/-- `L²`-convergence of the *double* Steklov average. -/
theorem tendsto_eLpNorm_steklov2_sub {u : ℝ → E} (hu : MeasureTheory.MemLp u 2) :
    Filter.Tendsto
      (fun h => MeasureTheory.eLpNorm (fun t => steklov h (steklov h u) t - u t) 2
        MeasureTheory.volume) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hbase := tendsto_eLpNorm_steklov_sub hu
  have h2 : Filter.Tendsto
      (fun h => 2 * MeasureTheory.eLpNorm (fun t => steklov h u t - u t) 2 MeasureTheory.volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hbase
      (Or.inr (by exact ENNReal.ofNat_ne_top))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Filter.Eventually.of_forall fun h => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact eLpNorm_steklov2_sub_le hh hu

/-- `L²`-convergence of the double Steklov average, in the form `∫ ‖u_h − u‖² → 0`. -/
theorem tendsto_integral_norm_sq_steklov2 {u : ℝ → E} (hu : MeasureTheory.MemLp u 2) :
    Filter.Tendsto (fun h => ∫ τ, ‖steklov h (steklov h u) τ - u τ‖ ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hbase := tendsto_eLpNorm_steklov2_sub hu
  have htr : Filter.Tendsto
      (fun h => (MeasureTheory.eLpNorm (fun t => steklov h (steklov h u) t - u t) 2
        MeasureTheory.volume).toReal) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := (ENNReal.tendsto_toReal (by simp)).comp hbase
    simpa [Function.comp_def] using this
  have hsq := htr.pow 2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hsq
  refine hsq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (integral_norm_sq_eq ((memLp_steklov hh (memLp_steklov hh hu)).sub hu)).symm

end L2

/-- `L²`-membership of the double Steklov average. -/
theorem memLp_steklov2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ} (hh : 0 < h) {u : ℝ → E} (hu : MeasureTheory.MemLp u 2) :
    MeasureTheory.MemLp (steklov h (steklov h u)) 2 :=
  memLp_steklov hh (memLp_steklov hh hu)

/-- **The uniform Cauchy estimate in `L²` terms.**  The right-hand side tends to `0` as
`h, k → 0⁺` by `tendsto_integral_norm_sq_steklov2`, which is exactly the uniform Cauchy property
of the double Steklov averages on `[0,b]`. -/
theorem sup_bound_steklov_diff_L2 (G : GelfandTriple V H) {T : ℝ}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {c : StrongDual ℝ V}
    (hu2 : MeasureTheory.MemLp u 2 (μT T)) (hg2 : MeasureTheory.MemLp g 2 (μT T))
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ)
    {h k : ℝ} (hh : 0 < h) (hk : 0 < k) {b : ℝ} (hb : 0 < b)
    (hbh : b ≤ T - 2 * h) (hbk : b ≤ T - 2 * k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b) :
    ‖G.j (steklov h (steklov h (zext T u)) t - steklov k (steklov k (zext T u)) t)‖ ^ 2
      ≤ (1 / b) * ‖G.j‖ ^ 2
          * (∫ τ, ‖steklov h (steklov h (zext T u)) τ - steklov k (steklov k (zext T u)) τ‖ ^ 2)
        + ((∫ τ, ‖steklov h (steklov h (zext T g)) τ
              - steklov k (steklov k (zext T g)) τ‖ ^ 2)
          + ∫ τ, ‖steklov h (steklov h (zext T u)) τ
              - steklov k (steklov k (zext T u)) τ‖ ^ 2) := by
  have hu : MeasureTheory.Integrable u (μT T) := hu2.integrable one_le_two
  have hg : MeasureTheory.Integrable g (μT T) := hg2.integrable one_le_two
  refine RegPair.sup_bound_L2
    (((regPair_steklov_data G hu hg hc hh).mono hbh).sub
      ((regPair_steklov_data G hu hg hc hk).mono hbk)) hb ?_ ?_ ht
  · exact (memLp_steklov2 hh (memLp_zext hu2)).sub (memLp_steklov2 hk (memLp_zext hu2))
  · exact (memLp_steklov2 hh (memLp_zext hg2)).sub (memLp_steklov2 hk (memLp_zext hg2))

/-! ### Passage to the limit -/

section Limit

/-- The sequence of Steklov parameters `h_n = 1/(n+1)`. -/
def hseq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem hseq_pos (n : ℕ) : 0 < hseq n := by
  unfold hseq; positivity

theorem tendsto_hseq : Filter.Tendsto hseq Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    tendsto_one_div_add_atTop_nhds_zero_nat
    (Filter.Eventually.of_forall fun n => hseq_pos n)

theorem tendsto_hseq_nhds : Filter.Tendsto hseq Filter.atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

section Seq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `L²`-convergence of the double Steklov averages along the sequence `hseq`. -/
theorem tendsto_integral_norm_sq_hseq {u : ℝ → E} (hu : MeasureTheory.MemLp u 2) :
    Filter.Tendsto
      (fun n => ∫ τ, ‖steklov (hseq n) (steklov (hseq n) u) τ - u τ‖ ^ 2) Filter.atTop (nhds 0) :=
  (tendsto_integral_norm_sq_steklov2 hu).comp tendsto_hseq

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Triangle-type inequality for `∫ ‖·‖²`. -/
theorem integral_norm_sq_sub_le {f g w : ℝ → E} (hf : MeasureTheory.MemLp f 2)
    (hg : MeasureTheory.MemLp g 2) (hw : MeasureTheory.MemLp w 2) :
    (∫ τ, ‖f τ - g τ‖ ^ 2) ≤ 2 * (∫ τ, ‖f τ - w τ‖ ^ 2) + 2 * ∫ τ, ‖g τ - w τ‖ ^ 2 := by
  have h1 : MeasureTheory.Integrable (fun τ => ‖f τ - g τ‖ ^ 2) := integrable_norm_sq (hf.sub hg)
  have h2 : MeasureTheory.Integrable (fun τ => ‖f τ - w τ‖ ^ 2) := integrable_norm_sq (hf.sub hw)
  have h3 : MeasureTheory.Integrable (fun τ => ‖g τ - w τ‖ ^ 2) := integrable_norm_sq (hg.sub hw)
  have hptw : ∀ τ, ‖f τ - g τ‖ ^ 2 ≤ 2 * ‖f τ - w τ‖ ^ 2 + 2 * ‖g τ - w τ‖ ^ 2 := by
    intro τ
    have hsub : f τ - g τ = (f τ - w τ) - (g τ - w τ) := by abel
    have hn : ‖f τ - g τ‖ ≤ ‖f τ - w τ‖ + ‖g τ - w τ‖ := by
      rw [hsub]; exact norm_sub_le _ _
    nlinarith [norm_nonneg (f τ - g τ), norm_nonneg (f τ - w τ), norm_nonneg (g τ - w τ),
      sq_nonneg (‖f τ - w τ‖ - ‖g τ - w τ‖)]
  calc (∫ τ, ‖f τ - g τ‖ ^ 2)
      ≤ ∫ τ, (2 * ‖f τ - w τ‖ ^ 2 + 2 * ‖g τ - w τ‖ ^ 2) :=
        MeasureTheory.integral_mono h1 ((h2.const_mul 2).add (h3.const_mul 2)) hptw
    _ = 2 * (∫ τ, ‖f τ - w τ‖ ^ 2) + 2 * ∫ τ, ‖g τ - w τ‖ ^ 2 := by
        rw [MeasureTheory.integral_add (h2.const_mul 2) (h3.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

end Seq

/-- **(a) Uniform Cauchy property.**  The double Steklov averages `t ↦ G.j (u_{h_n} t)` form a
uniformly Cauchy sequence on `[0,b]` for every `b < T`. -/
theorem steklov_uniformCauchy (G : GelfandTriple V H) {T : ℝ}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {c : StrongDual ℝ V}
    (hu2 : MeasureTheory.MemLp u 2 (μT T)) (hg2 : MeasureTheory.MemLp g 2 (μT T))
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ)
    {b : ℝ} (hb : 0 < b) (hbT : b < T) :
    UniformCauchySeqOn (fun (n : ℕ) (t : ℝ) => G.j (steklov (hseq n) (steklov (hseq n)
      (zext T u)) t)) Filter.atTop (Set.Icc (0 : ℝ) b) := by
  have hub2 : MeasureTheory.MemLp (zext T u) 2 := memLp_zext hu2
  have hgb2 : MeasureTheory.MemLp (zext T g) 2 := memLp_zext hg2
  set A : ℕ → ℝ := fun n =>
    ∫ τ, ‖steklov (hseq n) (steklov (hseq n) (zext T u)) τ - zext T u τ‖ ^ 2 with hAdef
  set B : ℕ → ℝ := fun n =>
    ∫ τ, ‖steklov (hseq n) (steklov (hseq n) (zext T g)) τ - zext T g τ‖ ^ 2 with hBdef
  have hA : Filter.Tendsto A Filter.atTop (nhds 0) := tendsto_integral_norm_sq_hseq hub2
  have hB : Filter.Tendsto B Filter.atTop (nhds 0) := tendsto_integral_norm_sq_hseq hgb2
  have hTb : 0 < T - b := by linarith
  -- the averaging window fits into `(0,T]` for large `n`
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, b ≤ T - 2 * hseq n := by
    refine ⟨⌈2 / (T - b)⌉₊, fun n hn => ?_⟩
    have h1 : (2 : ℝ) / (T - b) ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 : 2 ≤ (n : ℝ) * (T - b) := (div_le_iff₀ hTb).1 h1
    have h4 : 2 * (1 / ((n : ℝ) + 1)) ≤ T - b := by
      rw [mul_one_div, div_le_iff₀ h2]
      nlinarith
    have : hseq n = 1 / ((n : ℝ) + 1) := rfl
    rw [this]; linarith
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  set K : ℝ := (1 / b) * ‖G.j‖ ^ 2 + 1 with hKdef
  have hK1 : (1 : ℝ) ≤ K := by
    have : (0 : ℝ) ≤ (1 / b) * ‖G.j‖ ^ 2 := by positivity
    linarith
  have hK0 : (0 : ℝ) < K := by linarith
  set δ : ℝ := ε ^ 2 / (4 * (K + 1)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; positivity
  have hδeq : 4 * δ * (K + 1) = ε ^ 2 := by
    rw [hδdef]; field_simp
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
    ((hA.eventually_lt_const hδpos).and (hB.eventually_lt_const hδpos))
  refine ⟨max N₀ N₁, fun m hm n hn t ht => ?_⟩
  have hm0 : N₀ ≤ m := le_trans (le_max_left _ _) hm
  have hn0 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hm1 : N₁ ≤ m := le_trans (le_max_right _ _) hm
  have hn1 : N₁ ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hAm, hBm⟩ := hN₁ m hm1
  obtain ⟨hAn, hBn⟩ := hN₁ n hn1
  have key := sup_bound_steklov_diff_L2 G hu2 hg2 hc (hseq_pos m) (hseq_pos n) hb
    (hN₀ m hm0) (hN₀ n hn0) ht
  set C : ℝ := ∫ τ, ‖steklov (hseq m) (steklov (hseq m) (zext T u)) τ
    - steklov (hseq n) (steklov (hseq n) (zext T u)) τ‖ ^ 2 with hCdef
  set D : ℝ := ∫ τ, ‖steklov (hseq m) (steklov (hseq m) (zext T g)) τ
    - steklov (hseq n) (steklov (hseq n) (zext T g)) τ‖ ^ 2 with hDdef
  have hCle : C ≤ 2 * A m + 2 * A n := by
    have := integral_norm_sq_sub_le (memLp_steklov2 (hseq_pos m) hub2)
      (memLp_steklov2 (hseq_pos n) hub2) hub2
    rw [hCdef, hAdef]; linarith [this]
  have hDle : D ≤ 2 * B m + 2 * B n := by
    have := integral_norm_sq_sub_le (memLp_steklov2 (hseq_pos m) hgb2)
      (memLp_steklov2 (hseq_pos n) hgb2) hgb2
    rw [hDdef, hBdef]; linarith [this]
  have hCnn : 0 ≤ C := MeasureTheory.integral_nonneg fun τ => by positivity
  have hfin : ‖G.j (steklov (hseq m) (steklov (hseq m) (zext T u)) t
      - steklov (hseq n) (steklov (hseq n) (zext T u)) t)‖ ^ 2 < ε ^ 2 := by
    have hKC : K * C ≤ K * (4 * δ) := by
      refine mul_le_mul_of_nonneg_left ?_ hK0.le
      linarith
    have hKC' : (1 / b) * ‖G.j‖ ^ 2 * C + (D + C) = K * C + D := by rw [hKdef]; ring
    have hDlt : D < 4 * δ := by linarith
    calc ‖G.j (steklov (hseq m) (steklov (hseq m) (zext T u)) t
          - steklov (hseq n) (steklov (hseq n) (zext T u)) t)‖ ^ 2
        ≤ (1 / b) * ‖G.j‖ ^ 2 * C + (D + C) := key
      _ = K * C + D := hKC'
      _ < K * (4 * δ) + 4 * δ := by linarith
      _ = ε ^ 2 := by rw [← hδeq]; ring
  rw [dist_eq_norm, ← map_sub]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hfin

/-- The candidate continuous representative: the pointwise limit of the double Steklov
averages. -/
def limRep (G : GelfandTriple V H) (T : ℝ) (u : ℝ → V) (t : ℝ) : H :=
  limUnder Filter.atTop fun n => G.j (steklov (hseq n) (steklov (hseq n) (zext T u)) t)

/-- **(b) Pointwise convergence.** -/
theorem tendsto_limRep (G : GelfandTriple V H) {T : ℝ}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {c : StrongDual ℝ V}
    (hu2 : MeasureTheory.MemLp u 2 (μT T)) (hg2 : MeasureTheory.MemLp g 2 (μT T))
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ)
    (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) :
    Filter.Tendsto (fun n => G.j (steklov (hseq n) (steklov (hseq n) (zext T u)) t))
      Filter.atTop (nhds (limRep G T u t)) := by
  have hb : 0 < (t + T) / 2 := by have := ht.1; linarith
  have hbT : (t + T) / 2 < T := by have := ht.2; linarith
  have hmem : t ∈ Set.Icc (0 : ℝ) ((t + T) / 2) := ⟨ht.1, by have := ht.2; linarith⟩
  have hcs : CauchySeq fun n => G.j (steklov (hseq n) (steklov (hseq n) (zext T u)) t) :=
    (steklov_uniformCauchy G hu2 hg2 hc hb hbT).cauchySeq hmem
  exact hcs.tendsto_limUnder

/-- Continuity of the approximating functions. -/
theorem continuous_steklov2_j (G : GelfandTriple V H) {T : ℝ} {u : ℝ → V}
    (hu : MeasureTheory.Integrable u (μT T)) (n : ℕ) :
    Continuous fun t => G.j (steklov (hseq n) (steklov (hseq n) (zext T u)) t) :=
  G.j.continuous.comp
    (continuous_steklov (hseq n)
      (locallyIntegrable_steklov (hseq n) (locallyIntegrable_zext hu)))

/-- **(b) Uniform convergence on `[0,b]`.** -/
theorem tendstoUniformlyOn_limRep (G : GelfandTriple V H) {T : ℝ}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {c : StrongDual ℝ V}
    (hu2 : MeasureTheory.MemLp u 2 (μT T)) (hg2 : MeasureTheory.MemLp g 2 (μT T))
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ)
    (hT : 0 < T) {b : ℝ} (hb : 0 < b) (hbT : b < T) :
    TendstoUniformlyOn
      (fun (n : ℕ) (t : ℝ) => G.j (steklov (hseq n) (steklov (hseq n) (zext T u)) t))
      (limRep G T u) Filter.atTop (Set.Icc (0 : ℝ) b) :=
  (steklov_uniformCauchy G hu2 hg2 hc hb hbT).tendstoUniformlyOn_of_tendsto fun _ ht =>
    tendsto_limRep G hu2 hg2 hc hT ⟨ht.1, lt_of_le_of_lt ht.2 hbT⟩

/-- **(b) The representative is continuous on `[0,T)`.** -/
theorem continuousOn_limRep (G : GelfandTriple V H) {T : ℝ}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {c : StrongDual ℝ V}
    (hu2 : MeasureTheory.MemLp u 2 (μT T)) (hg2 : MeasureTheory.MemLp g 2 (μT T))
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ)
    (hT : 0 < T) : ContinuousOn (limRep G T u) (Set.Ico (0 : ℝ) T) := by
  have hu : MeasureTheory.Integrable u (μT T) := hu2.integrable one_le_two
  intro t ht
  set b : ℝ := (t + T) / 2 with hbdef
  have hb : 0 < b := by rw [hbdef]; have := ht.1; have := ht.2; linarith
  have hbT : b < T := by rw [hbdef]; have := ht.2; linarith
  have htb : t < b := by rw [hbdef]; have := ht.2; linarith
  have hcont : ContinuousOn (limRep G T u) (Set.Icc (0 : ℝ) b) :=
    (tendstoUniformlyOn_limRep G hu2 hg2 hc hT hb hbT).continuousOn
      (Filter.Eventually.frequently
        (Filter.Eventually.of_forall fun n => (continuous_steklov2_j G hu n).continuousOn))
  refine (hcont t ⟨ht.1, htb.le⟩).mono_of_mem_nhdsWithin ?_
  have h1 : Set.Iio b ∈ nhds t := Iio_mem_nhds htb
  have h2 : Set.Ico (0 : ℝ) T ∩ Set.Iio b ∈ nhdsWithin t (Set.Ico (0 : ℝ) T) :=
    inter_mem_nhdsWithin _ h1
  refine Filter.mem_of_superset h2 ?_
  rintro x ⟨hx1, hx2⟩
  exact ⟨hx1.1, le_of_lt hx2⟩

section SteklovCont

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Sup bound for a Steklov average. -/
theorem norm_steklov_le {h C : ℝ} (hh : 0 < h) {f : ℝ → E} {t : ℝ}
    (hC : ∀ ρ ∈ Set.uIoc t (t + h), ‖f ρ‖ ≤ C) : ‖steklov h f t‖ ≤ C := by
  unfold steklov
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / h)]
  have h1 : ‖∫ τ in t..(t + h), f τ‖ ≤ C * |t + h - t| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hC
  have h2 : |t + h - t| = h := by rw [show t + h - t = h by ring, abs_of_pos hh]
  rw [h2] at h1
  calc 1 / h * ‖∫ τ in t..(t + h), f τ‖ ≤ 1 / h * (C * h) := by
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = C := by field_simp

/-- The double Steklov average of a continuous function converges pointwise. -/
theorem tendsto_steklov2_of_continuous {f : ℝ → E} (hf : Continuous f) (t : ℝ) :
    Filter.Tendsto (fun h => steklov h (steklov h f) t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (f t)) := by
  have hloc : MeasureTheory.LocallyIntegrable f := hf.locallyIntegrable
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hf.continuousAt (ε / 2) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < δ / 3 by positivity)] with h hmem
  obtain ⟨hh0, hhδ⟩ := hmem
  set F : ℝ → E := fun ρ => f ρ - f t with hFdef
  have hFloc : MeasureTheory.LocallyIntegrable F := hloc.sub (continuous_const.locallyIntegrable)
  have hFbd : ∀ ρ, |ρ - t| < δ → ‖F ρ‖ ≤ ε / 2 := by
    intro ρ hρ
    have : dist ρ t < δ := by rwa [Real.dist_eq]
    have := hδ' this
    rw [dist_eq_norm] at this
    exact this.le
  -- rewrite the difference as the double average of `F`
  have hF1 : ∀ σ, steklov h F σ = steklov h f σ - f t := by
    intro σ
    rw [hFdef, ← steklov_sub hloc (continuous_const.locallyIntegrable) σ, steklov_const hh0]
  have hFeq : steklov h F = fun σ => steklov h f σ - f t := funext hF1
  have hstep2 : steklov h (steklov h F) t = steklov h (steklov h f) t - f t := by
    rw [hFeq, ← steklov_sub (continuous_steklov h hloc).locallyIntegrable
      (continuous_const.locallyIntegrable) t, steklov_const hh0]
  -- bound the double average of `F`
  have hinner : ∀ σ ∈ Set.uIoc t (t + h), ‖steklov h F σ‖ ≤ ε / 2 := by
    intro σ hσ
    rw [Set.uIoc_of_le (by linarith)] at hσ
    refine norm_steklov_le hh0 fun ρ hρ => ?_
    rw [Set.uIoc_of_le (by linarith)] at hρ
    refine hFbd ρ ?_
    rw [abs_of_pos (by linarith [hσ.1, hρ.1])]
    linarith [hρ.2, hσ.2]
  have hbd : ‖steklov h (steklov h F) t‖ ≤ ε / 2 := norm_steklov_le hh0 hinner
  rw [dist_eq_norm, ← hstep2]
  linarith

end SteklovCont

theorem eventually_two_hseq_le {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in Filter.atTop, 2 * hseq n ≤ a := by
  have h : Filter.Tendsto (fun n => 2 * hseq n) Filter.atTop (nhds 0) := by
    simpa using tendsto_hseq_nhds.const_mul (2 : ℝ)
  exact (h.eventually_lt_const ha).mono fun n hn => hn.le

/-- The a.e. identification of the extended data with the `V'`-valued primitive. -/
theorem hae_flat_zext (G : GelfandTriple V H) {T : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    {c : StrongDual ℝ V}
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ) :
    ∀ᵐ τ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), τ ∈ Set.Ioc (0 : ℝ) T →
      G.flat (G.j (zext T u τ)) = c + ∫ ρ in (0 : ℝ)..τ, zext T g ρ := by
  have hc2 : ∀ᵐ τ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) T)),
      G.flat (G.j (u τ)) = c + ∫ ρ in (0 : ℝ)..τ, g ρ := hc
  have hc' := (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp hc2
  filter_upwards [hc'] with τ hτ hmem
  rw [zext, Set.indicator_of_mem hmem, hτ hmem]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with ρ hρ
  rw [Set.uIoc_of_le hmem.1.le] at hρ
  have hρ' : ρ ∈ Set.Ioc (0 : ℝ) T := ⟨hρ.1, le_trans hρ.2 hmem.2⟩
  rw [zext, Set.indicator_of_mem hρ']

omit [CompleteSpace V] in
/-- On `[0,T]` the truncated primitive agrees with the primitive of `g`. -/
theorem integral_zext_eq {T : ℝ} (g : ℝ → StrongDual ℝ V) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ ρ in (0 : ℝ)..t, zext T g ρ) = ∫ ρ in (0 : ℝ)..t, g ρ := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with ρ hρ
  rw [Set.uIoc_of_le ht.1] at hρ
  have hρ' : ρ ∈ Set.Ioc (0 : ℝ) T := ⟨hρ.1, le_trans hρ.2 ht.2⟩
  rw [zext, Set.indicator_of_mem hρ']

/-- The double Steklov average of `u` is identified in `V'` with the double Steklov average of
the primitive `w`. -/
theorem flat_j_steklov2_eq (G : GelfandTriple V H) {T : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    {c : StrongDual ℝ V} (hu : MeasureTheory.Integrable u (μT T))
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ)
    {h : ℝ} (hh : 0 < h) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (T - 2 * h)) :
    G.flat (G.j (steklov h (steklov h (zext T u)) t))
      = steklov h (steklov h fun σ => c + ∫ ρ in (0 : ℝ)..σ, zext T g ρ) t := by
  have hae := hae_flat_zext G hc
  have h1 : ∀ σ ∈ Set.Icc (0 : ℝ) (T - h), G.flat (G.j (steklov h (zext T u) σ))
      = steklov h (fun σ => c + ∫ ρ in (0 : ℝ)..σ, zext T g ρ) σ :=
    fun σ hσ => flat_j_steklov_eq G hh (locallyIntegrable_zext hu) hae hσ
  refine flat_j_steklov_eq G (T := T - h) hh
    (locallyIntegrable_steklov h (locallyIntegrable_zext hu)) ?_ ?_
  · filter_upwards with τ hτ
    exact h1 τ ⟨hτ.1.le, hτ.2⟩
  · exact ⟨ht.1, by linarith [ht.2]⟩

/-- **(e) The representative attains the `V'`-valued primitive.** -/
theorem flat_limRep (G : GelfandTriple V H) {T : ℝ}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {c : StrongDual ℝ V}
    (hu2 : MeasureTheory.MemLp u 2 (μT T)) (hg2 : MeasureTheory.MemLp g 2 (μT T))
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ)
    (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) :
    G.flat (limRep G T u t) = c + ∫ τ in (0 : ℝ)..t, g τ := by
  have hu : MeasureTheory.Integrable u (μT T) := hu2.integrable one_le_two
  have hg : MeasureTheory.Integrable g (μT T) := hg2.integrable one_le_two
  set w : ℝ → StrongDual ℝ V := fun σ => c + ∫ ρ in (0 : ℝ)..σ, zext T g ρ with hwdef
  have hwc : Continuous w := continuous_primitive_add_const (locallyIntegrable_zext hg) c
  have L1 : Filter.Tendsto
      (fun n => G.flat (G.j (steklov (hseq n) (steklov (hseq n) (zext T u)) t)))
      Filter.atTop (nhds (G.flat (limRep G T u t))) :=
    (G.flat.continuous.tendsto _).comp (tendsto_limRep G hu2 hg2 hc hT ht)
  have L2 : Filter.Tendsto (fun n => steklov (hseq n) (steklov (hseq n) w) t) Filter.atTop
      (nhds (w t)) := (tendsto_steklov2_of_continuous hwc t).comp tendsto_hseq
  have hev : ∀ᶠ n in Filter.atTop,
      G.flat (G.j (steklov (hseq n) (steklov (hseq n) (zext T u)) t))
        = steklov (hseq n) (steklov (hseq n) w) t := by
    filter_upwards [eventually_two_hseq_le (show (0 : ℝ) < T - t by linarith [ht.2])] with n hn
    exact flat_j_steklov2_eq G hu hc (hseq_pos n) ⟨ht.1, by linarith⟩
  have hlim := tendsto_nhds_unique (Filter.Tendsto.congr' hev L1) L2
  rw [hlim, hwdef]
  simp only
  rw [integral_zext_eq g ⟨ht.1, ht.2.le⟩]

/-- **(c) The limit is the given function almost everywhere.** -/
theorem limRep_ae_eq (G : GelfandTriple V H) {T : ℝ}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {c : StrongDual ℝ V}
    (hu2 : MeasureTheory.MemLp u 2 (μT T)) (hg2 : MeasureTheory.MemLp g 2 (μT T))
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ)
    (hT : 0 < T) : ∀ᵐ t ∂(μT T), limRep G T u t = G.j (u t) := by
  have hu : MeasureTheory.Integrable u (μT T) := hu2.integrable one_le_two
  have hub2 : MeasureTheory.MemLp (zext T u) 2 := memLp_zext hu2
  have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (steklov (hseq n) (steklov (hseq n) (zext T u))) MeasureTheory.volume := fun n =>
    (continuous_steklov (hseq n)
      (locallyIntegrable_steklov (hseq n) (locallyIntegrable_zext hu))).aestronglyMeasurable
  have hLp : Filter.Tendsto (fun n : ℕ => MeasureTheory.eLpNorm
      (steklov (hseq n) (steklov (hseq n) (zext T u)) - zext T u) 2 MeasureTheory.volume)
      Filter.atTop (nhds 0) := (tendsto_eLpNorm_steklov2_sub hub2).comp tendsto_hseq
  have htim : MeasureTheory.TendstoInMeasure MeasureTheory.volume
      (fun n : ℕ => steklov (hseq n) (steklov (hseq n) (zext T u))) Filter.atTop (zext T u) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hLp
  obtain ⟨ns, hns_mono, hns⟩ := htim.exists_seq_tendsto_ae
  rw [μT_eq_restrict_Ioo, MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hns] with t ht hmem
  have h1 : Filter.Tendsto
      (fun i => G.j (steklov (hseq (ns i)) (steklov (hseq (ns i)) (zext T u)) t))
      Filter.atTop (nhds (G.j (zext T u t))) := (G.j.continuous.tendsto _).comp ht
  have h2 : Filter.Tendsto
      (fun n => G.j (steklov (hseq n) (steklov (hseq n) (zext T u)) t))
      Filter.atTop (nhds (limRep G T u t)) :=
    tendsto_limRep G hu2 hg2 hc hT ⟨hmem.1.le, hmem.2⟩
  have h3 := h2.comp hns_mono.tendsto_atTop
  have h4 := tendsto_nhds_unique h3 h1
  have hmem' : t ∈ Set.Ioc (0 : ℝ) T := ⟨hmem.1, hmem.2.le⟩
  rw [h4, zext, Set.indicator_of_mem hmem']

/-- Cauchy–Schwarz for the product of the norms of two `L²` functions (possibly with different
codomains). -/
theorem integral_norm_mul_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : ℝ → E} {g : ℝ → F} (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.volume) :
    (∫ a, ‖f a‖ * ‖g a‖) ≤ Real.sqrt (∫ a, ‖f a‖ ^ 2) * Real.sqrt (∫ a, ‖g a‖ ^ 2) := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num
  have hfn : MeasureTheory.MemLp (fun a => ‖f a‖) (ENNReal.ofReal (2 : ℝ))
      MeasureTheory.volume := by rw [h2]; exact hf.norm
  have hgn : MeasureTheory.MemLp (fun a => ‖g a‖) (ENNReal.ofReal (2 : ℝ))
      MeasureTheory.volume := by rw [h2]; exact hg.norm
  have h := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hfn hgn
  simp only [norm_norm] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  convert h using 3 <;> norm_num

/-- The product of the norms of two `L²` functions is integrable. -/
theorem integrable_norm_mul {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : ℝ → E} {g : ℝ → F} (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.volume) :
    MeasureTheory.Integrable (fun a => ‖f a‖ * ‖g a‖) MeasureTheory.volume :=
  hf.norm.integrable_mul hg.norm

omit [CompleteSpace V] in
/-- The duality pairing of an `L²` functional with an `L²` function is integrable. -/
theorem integrable_pairing {γ : ℝ → StrongDual ℝ V} {v : ℝ → V}
    (hγ : MeasureTheory.MemLp γ 2 MeasureTheory.volume)
    (hv : MeasureTheory.MemLp v 2 MeasureTheory.volume) :
    MeasureTheory.Integrable (fun τ => γ τ (v τ)) MeasureTheory.volume := by
  refine MeasureTheory.Integrable.mono' (integrable_norm_mul hγ hv)
    (aestronglyMeasurable_apply hγ.aestronglyMeasurable hv.aestronglyMeasurable) ?_
  filter_upwards with τ
  exact (γ τ).le_opNorm (v τ)

omit [CompleteSpace V] in
/-- Stability of the pairing integral under `L²` perturbations. -/
theorem norm_integral_pairing_sub_le {γ γ' : ℝ → StrongDual ℝ V} {v v' : ℝ → V}
    (hγ : MeasureTheory.MemLp γ 2 MeasureTheory.volume)
    (hγ' : MeasureTheory.MemLp γ' 2 MeasureTheory.volume)
    (hv : MeasureTheory.MemLp v 2 MeasureTheory.volume)
    (hv' : MeasureTheory.MemLp v' 2 MeasureTheory.volume) (s t : ℝ) :
    ‖(∫ τ in s..t, γ τ (v τ)) - ∫ τ in s..t, γ' τ (v' τ)‖
      ≤ Real.sqrt (∫ τ, ‖γ τ‖ ^ 2) * Real.sqrt (∫ τ, ‖v τ - v' τ‖ ^ 2)
        + Real.sqrt (∫ τ, ‖γ τ - γ' τ‖ ^ 2) * Real.sqrt (∫ τ, ‖v' τ‖ ^ 2) := by
  have hP1 : MeasureTheory.Integrable (fun τ => γ τ (v τ)) := integrable_pairing hγ hv
  have hP2 : MeasureTheory.Integrable (fun τ => γ' τ (v' τ)) := integrable_pairing hγ' hv'
  have hR : MeasureTheory.Integrable
      (fun τ => ‖γ τ‖ * ‖v τ - v' τ‖ + ‖γ τ - γ' τ‖ * ‖v' τ‖) :=
    (integrable_norm_mul hγ (hv.sub hv')).add (integrable_norm_mul (hγ.sub hγ') hv')
  rw [← intervalIntegral.integral_sub hP1.intervalIntegrable hP2.intervalIntegrable]
  have hptw : ∀ τ, ‖γ τ (v τ) - γ' τ (v' τ)‖
      ≤ ‖γ τ‖ * ‖v τ - v' τ‖ + ‖γ τ - γ' τ‖ * ‖v' τ‖ := by
    intro τ
    have hsplit : γ τ (v τ) - γ' τ (v' τ) = γ τ (v τ - v' τ) + (γ τ - γ' τ) (v' τ) := by
      simp only [map_sub, sub_apply]; ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) (add_le_add ((γ τ).le_opNorm _) ?_)
    exact (γ τ - γ' τ).le_opNorm _
  calc ‖∫ τ in s..t, (γ τ (v τ) - γ' τ (v' τ))‖
      ≤ ∫ τ in Set.uIoc s t, ‖γ τ (v τ) - γ' τ (v' τ)‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ τ in Set.uIoc s t, (‖γ τ‖ * ‖v τ - v' τ‖ + ‖γ τ - γ' τ‖ * ‖v' τ‖) :=
        MeasureTheory.setIntegral_mono_on ((hP1.sub hP2).norm.integrableOn)
          hR.integrableOn measurableSet_uIoc fun τ _ => hptw τ
    _ ≤ ∫ τ, (‖γ τ‖ * ‖v τ - v' τ‖ + ‖γ τ - γ' τ‖ * ‖v' τ‖) :=
        MeasureTheory.setIntegral_le_integral hR
          (Filter.Eventually.of_forall fun τ => by positivity)
    _ = (∫ τ, ‖γ τ‖ * ‖v τ - v' τ‖) + ∫ τ, ‖γ τ - γ' τ‖ * ‖v' τ‖ :=
        MeasureTheory.integral_add (integrable_norm_mul hγ (hv.sub hv'))
          (integrable_norm_mul (hγ.sub hγ') hv')
    _ ≤ Real.sqrt (∫ τ, ‖γ τ‖ ^ 2) * Real.sqrt (∫ τ, ‖v τ - v' τ‖ ^ 2)
          + Real.sqrt (∫ τ, ‖γ τ - γ' τ‖ ^ 2) * Real.sqrt (∫ τ, ‖v' τ‖ ^ 2) :=
        add_le_add (integral_norm_mul_norm_le hγ (hv.sub hv'))
          (integral_norm_mul_norm_le (hγ.sub hγ') hv')

/-- **(d) Convergence of the pairing integrals.** -/
theorem tendsto_integral_pairing {T : ℝ} {u : ℝ → V}
    {g : ℝ → StrongDual ℝ V} (hu2 : MeasureTheory.MemLp u 2 (μT T))
    (hg2 : MeasureTheory.MemLp g 2 (μT T)) (s t : ℝ) :
    Filter.Tendsto (fun n : ℕ => ∫ τ in s..t,
        steklov (hseq n) (steklov (hseq n) (zext T g)) τ
          (steklov (hseq n) (steklov (hseq n) (zext T u)) τ)) Filter.atTop
      (nhds (∫ τ in s..t, zext T g τ (zext T u τ))) := by
  have hub2 : MeasureTheory.MemLp (zext T u) 2 := memLp_zext hu2
  have hgb2 : MeasureTheory.MemLp (zext T g) 2 := memLp_zext hg2
  set Mu : ℝ := Real.sqrt (∫ τ, ‖zext T u τ‖ ^ 2) with hMudef
  set Mg : ℝ := Real.sqrt (∫ τ, ‖zext T g τ‖ ^ 2) with hMgdef
  set A : ℕ → ℝ := fun n =>
    ∫ τ, ‖steklov (hseq n) (steklov (hseq n) (zext T u)) τ - zext T u τ‖ ^ 2 with hAdef
  set B : ℕ → ℝ := fun n =>
    ∫ τ, ‖steklov (hseq n) (steklov (hseq n) (zext T g)) τ - zext T g τ‖ ^ 2 with hBdef
  have hA : Filter.Tendsto A Filter.atTop (nhds 0) := tendsto_integral_norm_sq_hseq hub2
  have hB : Filter.Tendsto B Filter.atTop (nhds 0) := tendsto_integral_norm_sq_hseq hgb2
  -- the `L²`-norms of the averages are bounded by the `L²`-norm of `g`
  have hMg : ∀ n : ℕ,
      Real.sqrt (∫ τ, ‖steklov (hseq n) (steklov (hseq n) (zext T g)) τ‖ ^ 2) ≤ Mg := by
    intro n
    have hle : MeasureTheory.eLpNorm (steklov (hseq n) (steklov (hseq n) (zext T g))) 2
        MeasureTheory.volume ≤ MeasureTheory.eLpNorm (zext T g) 2 MeasureTheory.volume :=
      le_trans (eLpNorm_steklov_le (hseq_pos n) (memLp_steklov (hseq_pos n) hgb2))
        (eLpNorm_steklov_le (hseq_pos n) hgb2)
    have hreal : (MeasureTheory.eLpNorm (steklov (hseq n) (steklov (hseq n) (zext T g))) 2
        MeasureTheory.volume).toReal
        ≤ (MeasureTheory.eLpNorm (zext T g) 2 MeasureTheory.volume).toReal :=
      ENNReal.toReal_mono hgb2.ne hle
    rw [hMgdef, integral_norm_sq_eq (memLp_steklov2 (hseq_pos n) hgb2),
      integral_norm_sq_eq hgb2]
    exact Real.sqrt_le_sqrt (by nlinarith [ENNReal.toReal_nonneg (a :=
      MeasureTheory.eLpNorm (steklov (hseq n) (steklov (hseq n) (zext T g))) 2
        MeasureTheory.volume), ENNReal.toReal_nonneg (a :=
      MeasureTheory.eLpNorm (zext T g) 2 MeasureTheory.volume)])
  -- the quantitative bound
  have hbound : ∀ n : ℕ, ‖(∫ τ in s..t, steklov (hseq n) (steklov (hseq n) (zext T g)) τ
        (steklov (hseq n) (steklov (hseq n) (zext T u)) τ))
      - ∫ τ in s..t, zext T g τ (zext T u τ)‖ ≤ Mg * Real.sqrt (A n) + Real.sqrt (B n) * Mu := by
    intro n
    refine le_trans (norm_integral_pairing_sub_le (memLp_steklov2 (hseq_pos n) hgb2) hgb2
      (memLp_steklov2 (hseq_pos n) hub2) hub2 s t) ?_
    have h1 : Real.sqrt (∫ τ, ‖steklov (hseq n) (steklov (hseq n) (zext T g)) τ‖ ^ 2)
        * Real.sqrt (A n) ≤ Mg * Real.sqrt (A n) :=
      mul_le_mul_of_nonneg_right (hMg n) (Real.sqrt_nonneg _)
    rw [hAdef, hBdef]
    exact add_le_add h1 le_rfl
  -- the bound tends to zero
  have hsq1 : Filter.Tendsto (fun n => Real.sqrt (A n)) Filter.atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hA
    simpa [Function.comp_def] using this
  have hsq2 : Filter.Tendsto (fun n => Real.sqrt (B n)) Filter.atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hB
    simpa [Function.comp_def] using this
  have hlim : Filter.Tendsto (fun n => Mg * Real.sqrt (A n) + Real.sqrt (B n) * Mu)
      Filter.atTop (nhds 0) := by
    have h1 := hsq1.const_mul Mg
    have h2 := hsq2.mul_const Mu
    simpa using h1.add h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) hbound hlim

omit [CompleteSpace V] in
/-- On `[s,t] ⊆ [0,T)` the extended data can be replaced by the original data. -/
theorem integral_pairing_zext_eq {T : ℝ} (u : ℝ → V) (g : ℝ → StrongDual ℝ V) {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) T) (ht : t ∈ Set.Ico (0 : ℝ) T) :
    (∫ τ in s..t, zext T g τ (zext T u τ)) = ∫ τ in s..t, g τ (u τ) := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with τ hτ
  simp only [Set.uIoc, Set.mem_Ioc, min_def, max_def] at hτ
  rw [← min_def, ← max_def] at hτ
  have h0 : (0 : ℝ) < τ := lt_of_le_of_lt (le_min hs.1 ht.1) hτ.1
  have h1 : τ ≤ T := le_trans hτ.2 (le_of_lt (max_lt hs.2 ht.2))
  have hmem : τ ∈ Set.Ioc (0 : ℝ) T := ⟨h0, h1⟩
  rw [zext, zext, Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]

/-- **(d) The energy identity in the limit.** -/
theorem energy_limRep (G : GelfandTriple V H) {T : ℝ}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {c : StrongDual ℝ V}
    (hu2 : MeasureTheory.MemLp u 2 (μT T)) (hg2 : MeasureTheory.MemLp g 2 (μT T))
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ)
    (hT : 0 < T) {s t : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) T) (ht : t ∈ Set.Ico (0 : ℝ) T) :
    ‖limRep G T u t‖ ^ 2 - ‖limRep G T u s‖ ^ 2 = 2 * ∫ τ in s..t, g τ (u τ) := by
  have hu : MeasureTheory.Integrable u (μT T) := hu2.integrable one_le_two
  have hg : MeasureTheory.Integrable g (μT T) := hg2.integrable one_le_two
  have hLs := ((tendsto_limRep G hu2 hg2 hc hT hs).norm.pow 2)
  have hLt := ((tendsto_limRep G hu2 hg2 hc hT ht).norm.pow 2)
  have hL := hLt.sub hLs
  have hR := (tendsto_integral_pairing hu2 hg2 s t).const_mul (2 : ℝ)
  have hev : ∀ᶠ n in Filter.atTop,
      ‖G.j (steklov (hseq n) (steklov (hseq n) (zext T u)) t)‖ ^ 2
        - ‖G.j (steklov (hseq n) (steklov (hseq n) (zext T u)) s)‖ ^ 2
      = 2 * ∫ τ in s..t, steklov (hseq n) (steklov (hseq n) (zext T g)) τ
          (steklov (hseq n) (steklov (hseq n) (zext T u)) τ) := by
    have hpos : (0 : ℝ) < T - max s t := by
      have := max_lt hs.2 ht.2; linarith
    filter_upwards [eventually_two_hseq_le hpos] with n hn
    have hsb : s ≤ T - 2 * hseq n := by
      have : s ≤ max s t := le_max_left _ _
      linarith
    have htb : t ≤ T - 2 * hseq n := by
      have : t ≤ max s t := le_max_right _ _
      linarith
    exact energy_steklov_data G hu hg hc (hseq_pos n) ⟨hs.1, hsb⟩ ⟨ht.1, htb⟩
  have hkey := tendsto_nhds_unique (Filter.Tendsto.congr' hev hL) hR
  rw [hkey, integral_pairing_zext_eq u g hs ht]

end Limit

/-! ### The Lions–Magenes lemma -/

/-- **Construction of the continuous representative and passage to the limit.**

The representative is `limRep G T u`, the pointwise limit of the double Steklov averages
`u_h := steklov h (steklov h (zext T u))` along `h = hseq n = 1/(n+1)`:

* `regPair_steklov_data` : the averages form a `RegPair` on `[0, T − 2h]`, with
  `Γ_h := steklov h (steklov h (zext T g))`, whence the *exact* energy identity
  `energy_steklov_data`;
* `sup_bound_steklov_diff_L2` (from `RegPair.sub` and `RegPair.sup_bound_L2`) together with
  `tendsto_integral_norm_sq_steklov2` gives `steklov_uniformCauchy`: uniform Cauchyness on
  `[0,b]` for every `b < T`, hence `tendsto_limRep`, `tendstoUniformlyOn_limRep` and
  `continuousOn_limRep`;
* `limRep_ae_eq` : `limRep = G.j ∘ u` a.e. (an `L²`-convergent sequence has an a.e. convergent
  subsequence);
* `energy_limRep` : the energy identity passes to the limit, using the Cauchy–Schwarz bound
  `norm_integral_pairing_sub_le`;
* `flat_limRep` : the `V'`-identity, from `flat_j_steklov2_eq` and
  `tendsto_steklov2_of_continuous`. -/
theorem exists_continuous_representative (G : GelfandTriple V H) {T : ℝ} (hT : 0 < T)
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} (hu : MemW G T u g) {c : StrongDual ℝ V}
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, g τ) :
    ∃ ũ : ℝ → H, ContinuousOn ũ (Set.Ico 0 T) ∧ (∀ᵐ t ∂(μT T), ũ t = G.j (u t)) ∧
      (∀ t ∈ Set.Ico 0 T, G.flat (ũ t) = c + ∫ τ in (0 : ℝ)..t, g τ) ∧
      ∀ s ∈ Set.Ico 0 T, ∀ t ∈ Set.Ico 0 T,
        ‖ũ t‖ ^ 2 - ‖ũ s‖ ^ 2 = 2 * ∫ τ in s..t, g τ (u τ) :=
  ⟨limRep G T u, continuousOn_limRep G hu.memLp_u hu.memLp_g hc hT,
    limRep_ae_eq G hu.memLp_u hu.memLp_g hc hT,
    fun _ ht => flat_limRep G hu.memLp_u hu.memLp_g hc hT ht,
    fun _ hs _ ht => energy_limRep G hu.memLp_u hu.memLp_g hc hT hs ht⟩

/-- **Lions–Magenes.**  `u ∈ W(0,T)` has a representative `ũ ∈ C([0,T);H)` with the energy
identity `‖ũ(t)‖²_H − ‖ũ(s)‖²_H = 2 ∫_s^t ⟨g, u⟩` for all `s, t ∈ [0,T)`, and
`ũ(t)^♭ = c + ∫₀ᵗ g` for all `t ∈ [0,T)`. -/
theorem lions_magenes (G : GelfandTriple V H) {T : ℝ} (hT : 0 < T) {u : ℝ → V}
    {g : ℝ → StrongDual ℝ V} (hu : MemW G T u g) :
    ∃ (ũ : ℝ → H) (c : StrongDual ℝ V), ContinuousOn ũ (Set.Ico 0 T) ∧
      (∀ᵐ t ∂(μT T), ũ t = G.j (u t)) ∧
      (∀ t ∈ Set.Ico 0 T, G.flat (ũ t) = c + ∫ τ in (0 : ℝ)..t, g τ) ∧
      ∀ s ∈ Set.Ico 0 T, ∀ t ∈ Set.Ico 0 T,
        ‖ũ t‖ ^ 2 - ‖ũ s‖ ^ 2 = 2 * ∫ τ in s..t, g τ (u τ) := by
  have hui : MeasureTheory.Integrable u (μT T) := hu.memLp_u.integrable one_le_two
  have hgi : MeasureTheory.Integrable g (μT T) := hu.memLp_g.integrable one_le_two
  obtain ⟨c, hc⟩ := exists_ae_eq_const_add_integral G hT hui hgi hu.weak
  obtain ⟨ũ, h1, h2, h3, h4⟩ := exists_continuous_representative G hT hu hc
  exact ⟨ũ, c, h1, h2, h3, h4⟩

end LionsC12

end
