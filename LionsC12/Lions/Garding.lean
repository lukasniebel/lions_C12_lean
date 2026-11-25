module

public import LionsC12.Spaces.Time
public import LionsC12.Lions.Uniqueness

/-!
# Lions' theorem under a Gårding inequality

`LionsC12.lions_existence_bound` asks the forms to be coercive, `α ‖v‖² ≤ 𝔞(t)[v,v]`.  The
standard exponential shift removes this restriction: if only the Gårding inequality
`α ‖v‖² ≤ 𝔞(t)[v,v] + λ ‖j v‖_H²` holds and `ũ` solves the problem for the coercive forms
`𝔞(t) + λ (·,·)_H` with data `e^{-λt} f`, then `u = e^{λt} ũ` solves the original one.

* `GelfandTriple.pivotForm` — the form `(u, v) ↦ ⟪j u, j v⟫_H`;
* `IsVariationalSolution.exp_smul` — undoing the shift;
* `IsVariationalSolution.add_pivot` — a solution for `(𝔞, f)` solves the shifted problem with
  the data `f + λ ⟪j u, j ·⟫_H`;
* `lions_existence_garding` — existence, with the bound
  `‖u‖_{L²(0,T;V)} ≤ e^{λT} (‖f‖_{L²(0,T;V')} + ‖u₀‖_H) / min(1/2, α)`;
* `hasWeakDerivV'_of_variational_garding`, `const_eq_flat_of_variational_garding` — the weak
  derivative `u' = f - 𝒜u` and the initial value of a solution;
* `hasWeakDeriv_flat_of_hasWeakDerivV'` — the weak derivative in the sense of
  `LionsC12.HasWeakDerivV'` is the distributional derivative of `t ↦ ⟪j u(t), j ·⟫_H ∈ V'`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter LionsC12Challenge
open scoped InnerProductSpace ContDiff

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The pivot form `(u, v) ↦ ⟪j u, j v⟫_H` of a Gelfand triple. -/
def GelfandTriple.pivotForm (G : GelfandTriple V H) : V →L[ℝ] V →L[ℝ] ℝ := G.flat.comp G.j

@[simp] theorem GelfandTriple.pivotForm_apply (G : GelfandTriple V H) (u v : V) :
    G.pivotForm u v = ⟪G.j u, G.j v⟫_ℝ := rfl

variable {T : ℝ}

/-- Adding `λ (·,·)_H` to forms satisfying the Gårding inequality gives a coercive family. -/
theorem isFormFamily_add_pivot (G : GelfandTriple V H) {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ}
    {M α lam : ℝ} (hmeas : AEStronglyMeasurable A (μT T)) (hb : ∀ t, ‖A t‖ ≤ M)
    (hcoer : ∀ t v, α * ‖v‖ ^ 2 ≤ A t v v + lam * ‖G.j v‖ ^ 2) (hα : 0 < α) :
    IsFormFamily T (fun t => A t + lam • G.pivotForm) (M + |lam| * ‖G.pivotForm‖) α where
  meas := (isometry_add_right (lam • G.pivotForm)).continuous.comp_aestronglyMeasurable hmeas
  bound t := by
    have h := norm_add_le (A t) (lam • G.pivotForm)
    have h' := ContinuousLinearMap.opNorm_smul_le lam G.pivotForm
    rw [Real.norm_eq_abs] at h'
    linarith [hb t]
  coercive t v := by
    have h := hcoer t v
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, GelfandTriple.pivotForm_apply,
      smul_eq_mul, real_inner_self_eq_norm_sq]
    linarith
  α_pos := hα

omit [CompleteSpace V] in
/-- `t ↦ e^{λt} φ(t)` is a test function with `φ`. -/
theorem IsTestV.exp_smul {φ : ℝ → V} (hφ : IsTestV T φ) (lam : ℝ) :
    IsTestV T (fun t => Real.exp (lam * t) • φ t) :=
  ⟨(Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).smul hφ.1,
    fun t ht => by simp only [hφ.2 t ht, smul_zero]⟩

omit [CompleteSpace V] in
theorem IsTestV.deriv_exp_smul {φ : ℝ → V} (hφ : IsTestV T φ) (lam t : ℝ) :
    deriv (fun t => Real.exp (lam * t) • φ t) t
      = Real.exp (lam * t) • deriv φ t + (lam * Real.exp (lam * t)) • φ t := by
  have he : HasDerivAt (fun t => Real.exp (lam * t)) (Real.exp (lam * t) * lam) t := by
    have h1 : HasDerivAt (fun t => lam * t) lam t := by
      simpa using (hasDerivAt_id t).const_mul lam
    exact h1.exp
  have h := he.fun_smul ((hφ.1.differentiable one_ne_zero t).hasDerivAt)
  rw [h.deriv, mul_comm (Real.exp (lam * t)) lam]

/-- **Undoing the exponential shift**: if `ũ` solves the problem for the forms
`𝔞(t) + λ (·,·)_H` with data `e^{-λt} f`, then `e^{λt} ũ` solves the problem for `𝔞(t)` with
data `f`. -/
theorem IsVariationalSolution.exp_smul (G : GelfandTriple V H) {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ}
    {lam : ℝ} {f : ℝ → StrongDual ℝ V} {u₀ : H} {ũ : ℝ → V}
    (h : IsVariationalSolution G T (fun t => A t + lam • G.pivotForm)
      (fun t => Real.exp (-(lam * t)) • f t) u₀ ũ) :
    IsVariationalSolution G T A f u₀ (fun t => Real.exp (lam * t) • ũ t) := by
  obtain ⟨hL, hv⟩ := h
  refine ⟨?_, fun φ hφ => ?_⟩
  · refine hL.of_le_mul (c := Real.exp (|lam| * |T|))
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.smul
        hL.aestronglyMeasurable) ?_
    have hmem : ∀ᵐ t ∂(μT T), t ∈ Ioc 0 T := ae_restrict_mem measurableSet_Ioc
    filter_upwards [hmem] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    calc lam * t ≤ |lam * t| := le_abs_self _
      _ = |lam| * |t| := abs_mul _ _
      _ ≤ |lam| * |T| := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [abs_of_pos ht.1, abs_of_pos (ht.1.trans_le ht.2)]
          exact ht.2
  · have key := hv _ (hφ.exp_smul lam)
    have e0 : Real.exp (lam * 0) • φ 0 = φ 0 := by simp
    rw [e0] at key
    refine Eq.trans ?_ (key.trans ?_)
    · refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [hφ.deriv_exp_smul lam t, map_add, map_smul, inner_add_right,
        real_inner_smul_right, real_inner_smul_left, add_apply,
        FunLike.coe_smul, Pi.smul_apply, GelfandTriple.pivotForm_apply,
        smul_eq_mul]
      ring
    · congr 1
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [FunLike.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul]
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- A variational solution for `(𝔞, f)` is a variational solution for the shifted forms
`𝔞(t) + λ (·,·)_H` with the data `f + λ ⟪j u, j ·⟫_H`. -/
theorem IsVariationalSolution.add_pivot (G : GelfandTriple V H) (hT : 0 < T)
    {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α lam : ℝ}
    (hA : IsFormFamily T (fun t => A t + lam • G.pivotForm) M α) {f : ℝ → StrongDual ℝ V}
    (hf : MemLp f 2 (μT T)) {u₀ : H} {u : ℝ → V} (hu : IsVariationalSolution G T A f u₀ u) :
    IsVariationalSolution G T (fun t => A t + lam • G.pivotForm)
      (fun t => f t + lam • G.flat (G.j (u t))) u₀ u := by
  obtain ⟨hL, hv⟩ := hu
  refine ⟨hL, fun φ hφ => ?_⟩
  have hu1 : Integrable u (μT T) := hL.integrable one_le_two
  have hflat : Integrable (fun t => G.flat (G.j (u t))) (μT T) :=
    ContinuousLinearMap.integrable_comp (G.flat ∘L G.j) hu1
  have hY : IntervalIntegrable (fun t => lam * ⟪G.j (u t), G.j (φ t)⟫_ℝ) volume 0 T := by
    have := intervalIntegrable_of_integrable_μT hT.le
      (integrable_apply_of_continuous hflat hφ.continuous)
    simpa only [GelfandTriple.flat_apply] using this.const_mul lam
  have hX' := intervalIntegrable_variational G hT hA hL hφ
  have hX : IntervalIntegrable
      (fun t => -(⟪G.j (u t), G.j (deriv φ t)⟫_ℝ) + A t (u t) (φ t)) volume 0 T := by
    refine (hX'.sub hY).congr fun t _ => ?_
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      GelfandTriple.pivotForm_apply, smul_eq_mul]
    ring
  have hZ : IntervalIntegrable (fun t => f t (φ t)) volume 0 T :=
    intervalIntegrable_of_integrable_μT hT.le
      (integrable_apply_of_continuous (hf.integrable one_le_two) hφ.continuous)
  have e1 : ∫ t in (0 : ℝ)..T, (-(⟪G.j (u t), G.j (deriv φ t)⟫_ℝ)
        + (A t + lam • G.pivotForm) (u t) (φ t))
      = (∫ t in (0 : ℝ)..T, (-(⟪G.j (u t), G.j (deriv φ t)⟫_ℝ) + A t (u t) (φ t)))
        + ∫ t in (0 : ℝ)..T, lam * ⟪G.j (u t), G.j (φ t)⟫_ℝ := by
    rw [← intervalIntegral.integral_add hX hY]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      GelfandTriple.pivotForm_apply, smul_eq_mul]
    ring
  have e2 : ∫ t in (0 : ℝ)..T, (f t + lam • G.flat (G.j (u t))) (φ t)
      = (∫ t in (0 : ℝ)..T, f t (φ t)) + ∫ t in (0 : ℝ)..T, lam * ⟪G.j (u t), G.j (φ t)⟫_ℝ := by
    rw [← intervalIntegral.integral_add hZ hY]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      GelfandTriple.flat_apply, smul_eq_mul]
  rw [e1, e2, hv φ hφ]
  ring

/-- **Lions' theorem under a Gårding inequality**, existence part with the energy bound: for
a measurable bounded family of forms with `α ‖v‖² ≤ 𝔞(t)[v,v] + λ ‖j v‖²_H`, `λ ≥ 0`, there is
a variational solution `u` with
`‖u‖_{L²(0,T;V)} ≤ e^{λT} (‖f‖_{L²(0,T;V')} + ‖u₀‖) / min(1/2, α)`. -/
theorem lions_existence_garding (G : GelfandTriple V H) (hT : 0 < T)
    {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α lam : ℝ} (hmeas : AEStronglyMeasurable A (μT T))
    (hb : ∀ t, ‖A t‖ ≤ M) (hcoer : ∀ t v, α * ‖v‖ ^ 2 ≤ A t v v + lam * ‖G.j v‖ ^ 2)
    (hα : 0 < α) (hlam : 0 ≤ lam) {f : ℝ → StrongDual ℝ V} (hf : MemLp f 2 (μT T)) (u₀ : H) :
    ∃ u : ℝ → V, IsVariationalSolution G T A f u₀ u ∧
      (eLpNorm u 2 (μT T)).toReal
        ≤ Real.exp (lam * T) * (((eLpNorm f 2 (μT T)).toReal + ‖u₀‖) / min (1 / 2) α) := by
  have hA := isFormFamily_add_pivot G hmeas hb hcoer hα
  have hmem : ∀ᵐ t ∂(μT T), t ∈ Ioc 0 T := ae_restrict_mem measurableSet_Ioc
  set f' : ℝ → StrongDual ℝ V := fun t => Real.exp (-(lam * t)) • f t with hf'def
  have hle : ∀ᵐ t ∂(μT T), ‖f' t‖ ≤ 1 * ‖f t‖ := by
    filter_upwards [hmem] with t ht
    rw [hf'def, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    gcongr
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg hlam ht.1.le
  have hf'm : AEStronglyMeasurable f' (μT T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable.smul
      hf.aestronglyMeasurable
  have hf' : MemLp f' 2 (μT T) := hf.of_le_mul hf'm hle
  have hf'n : (eLpNorm f' 2 (μT T)).toReal ≤ (eLpNorm f 2 (μT T)).toReal := by
    have := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf'm hle 2
    rw [ENNReal.ofReal_one, one_mul] at this
    exact ENNReal.toReal_mono hf.eLpNorm_ne_top this
  obtain ⟨ũ, hũ, hbound⟩ := lions_existence_bound G hT hA hf' u₀
  refine ⟨fun t => Real.exp (lam * t) • ũ t, hũ.exp_smul G, ?_⟩
  have hle' : ∀ᵐ t ∂(μT T), ‖Real.exp (lam * t) • ũ t‖ ≤ Real.exp (lam * T) * ‖ũ t‖ := by
    filter_upwards [hmem] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    gcongr
    exact ht.2
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hũ.exp_smul G).1.aestronglyMeasurable hle' 2
  have h2 : (eLpNorm (fun t => Real.exp (lam * t) • ũ t) 2 (μT T)).toReal
      ≤ Real.exp (lam * T) * (eLpNorm ũ 2 (μT T)).toReal := by
    have hfin : ENNReal.ofReal (Real.exp (lam * T)) * eLpNorm ũ 2 (μT T) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hũ.1.eLpNorm_ne_top
    refine (ENNReal.toReal_mono hfin h1).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  refine h2.trans (mul_le_mul_of_nonneg_left (hbound.trans ?_) (Real.exp_pos _).le)
  gcongr

/-- The shifted data have the same `f - 𝒜u`. -/
theorem shift_sub_eq (G : GelfandTriple V H) (A : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (lam : ℝ)
    (f : ℝ → StrongDual ℝ V) (u : ℝ → V) :
    (fun t => (f t + lam • G.flat (G.j (u t))) - (A t + lam • G.pivotForm) (u t))
      = fun t => f t - A t (u t) := by
  funext t
  ext v
  simp only [sub_apply, add_apply,
    FunLike.coe_smul, Pi.smul_apply, GelfandTriple.pivotForm_apply,
    GelfandTriple.flat_apply, smul_eq_mul]
  ring

/-- The weak derivative `u' = f - 𝒜u ∈ L²(0,T;V')` of a variational solution, for forms
satisfying a Gårding inequality. -/
theorem hasWeakDerivV'_of_variational_garding (G : GelfandTriple V H) (hT : 0 < T)
    {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α lam : ℝ} (hmeas : AEStronglyMeasurable A (μT T))
    (hb : ∀ t, ‖A t‖ ≤ M) (hcoer : ∀ t v, α * ‖v‖ ^ 2 ≤ A t v v + lam * ‖G.j v‖ ^ 2)
    (hα : 0 < α) {f : ℝ → StrongDual ℝ V} (hf : MemLp f 2 (μT T)) {u₀ : H} {u : ℝ → V}
    (hu : IsVariationalSolution G T A f u₀ u) :
    HasWeakDerivV' G T u (fun t => f t - A t (u t)) ∧
      MemLp (fun t => f t - A t (u t)) 2 (μT T) := by
  have hA := isFormFamily_add_pivot G hmeas hb hcoer hα
  have hf' : MemLp (fun t => f t + lam • G.flat (G.j (u t))) 2 (μT T) :=
    memLp_add' hf (((G.flat.comp G.j).comp_memLp' hu.1).const_smul lam)
  have h := hasWeakDerivV'_of_variational G hT hA hf' (hu.add_pivot G hT hA hf)
  rwa [shift_sub_eq] at h

/-- The initial value of a variational solution, for forms satisfying a Gårding inequality: the
constant of the absolutely continuous representative of `t ↦ ⟪j u(t), j ·⟫_H` is `⟪u₀, j ·⟫_H`.
-/
theorem const_eq_flat_of_variational_garding (G : GelfandTriple V H) (hT : 0 < T)
    {A : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {M α lam : ℝ} (hmeas : AEStronglyMeasurable A (μT T))
    (hb : ∀ t, ‖A t‖ ≤ M) (hcoer : ∀ t v, α * ‖v‖ ^ 2 ≤ A t v v + lam * ‖G.j v‖ ^ 2)
    (hα : 0 < α) {f : ℝ → StrongDual ℝ V} (hf : MemLp f 2 (μT T)) {u₀ : H} {u : ℝ → V}
    (hu : IsVariationalSolution G T A f u₀ u) {c : StrongDual ℝ V}
    (hc : ∀ᵐ t ∂(μT T), G.flat (G.j (u t)) = c + ∫ τ in (0 : ℝ)..t, (f τ - A τ (u τ))) :
    c = G.flat u₀ := by
  have hA := isFormFamily_add_pivot G hmeas hb hcoer hα
  have hf' : MemLp (fun t => f t + lam • G.flat (G.j (u t))) 2 (μT T) :=
    memLp_add' hf (((G.flat.comp G.j).comp_memLp' hu.1).const_smul lam)
  refine const_eq_flat_of_variational G hT hA hf' (hu.add_pivot G hT hA hf) ?_
  rw [shift_sub_eq]
  exact hc

/-- The weak derivative of `LionsC12.HasWeakDerivV'` on `(0,1)` is the distributional derivative
of `t ↦ ⟪j u(t), j ·⟫_H ∈ V'`. -/
theorem hasWeakDeriv_flat_of_hasWeakDerivV' (G : GelfandTriple V H) {u : ℝ → V}
    {g : ℝ → StrongDual ℝ V} (hu : Integrable u (μT 1)) (hg : Integrable g (μT 1))
    (h : HasWeakDerivV' G 1 u g) :
    HasWeakDeriv (fun t => G.flat (G.j (u t))) g := by
  intro ψ hψ hψc hψs
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
  have hdc : Continuous (deriv ψ) := hψ1.continuous_deriv_one
  have hflat : IntegrableOn (fun t => G.flat (G.j (u t))) (Ioo 0 1) := by
    have h' := ContinuousLinearMap.integrable_comp (G.flat ∘L G.j) hu
    rwa [μT_one_eq_μ01] at h'
  have hg' : IntegrableOn g (Ioo 0 1) := by
    have h' := hg
    rwa [μT_one_eq_μ01] at h'
  have h1 : IntegrableOn (fun t => deriv ψ t • G.flat (G.j (u t))) (Ioo 0 1) :=
    integrableOn_smul_of_continuous hdc hψc.deriv hflat
  have h2 : IntegrableOn (fun t => ψ t • g t) (Ioo 0 1) :=
    integrableOn_smul_of_continuous hψ1.continuous hψc hg'
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.integral_apply h1, neg_apply,
    ContinuousLinearMap.integral_apply h2]
  have hsub : tsupport (fun t => ψ t • v) ⊆ tsupport ψ :=
    closure_mono fun x hx hc0 => hx (by simp only [Function.mem_support] at *; simp [hc0])
  have hφc : HasCompactSupport (fun t => ψ t • v) :=
    hψc.of_isClosed_subset isClosed_closure hsub
  have hφ1 : ContDiff ℝ 1 (fun t => ψ t • v) := hψ1.smul contDiff_const
  have hdφ : ∀ t, deriv (fun s => ψ s • v) t = deriv ψ t • v := fun t =>
    deriv_smul_const (hψ1.differentiable one_ne_zero t) v
  have ha := h (fun t => ψ t • v) hφ1 hφc (hsub.trans hψs)
  simp only [hdφ, map_smul, real_inner_smul_right] at ha
  rw [← setIntegral_Ioo_eq_intervalIntegral, ← setIntegral_Ioo_eq_intervalIntegral] at ha
  simp only [smul_apply, GelfandTriple.flat_apply, smul_eq_mul]
  exact ha

end LionsC12
