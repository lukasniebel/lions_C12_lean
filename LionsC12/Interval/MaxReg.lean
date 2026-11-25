module

public import LionsC12.Interval.MaxRegSpace
public import LionsC12.Interval.Truncation
public import LionsC12.Lions.Garding

/-!
# Maximal `L²`-regularity of the truncated problems

The remark *Growth of the maximal-regularity constant* of the paper: the truncated coefficients
`𝔞_N = 1 + ε ∑_{j ≤ N} β_j` are finite sums of smooth functions, hence the problems
`w' + 𝒜_N(t)w = g`, `w(0) = 0`, have maximal `L²`-regularity.  In `H = L²((0,π);ℂ)`,
`V = H¹₀((0,π);ℂ)`, for any coefficient `c` as in `IsC1Coeff` (`C¹` in `x`, `c, ∂ₓc` jointly
continuous, `0 < m ≤ c ≤ Λ`, `|∂ₓc| ≤ L`; no time regularity beyond continuity):

* `pairD₀`, `formD₀` — the realified pairing `h ↦ Re ⟨(I + A_{0,H})·, h⟩_H` of `H` with `D₀`
  and the forms `b(t)[u,v] = Re ⟨(I + A_{0,H})v, A(t)u⟩_H` on `D₀`, which satisfy a Gårding
  inequality in the Gelfand pair `D₀ ↪ V` (pivot `V`);
* `exists_D₀_solution` — Lions' theorem in `D₀ ⊂ V ⊂ D₀'`
  (`LionsC12.lions_existence_garding`) gives `u ∈ L²(0,1;D₀)` with `‖u‖ ≤ K ‖g‖`, whose
  distributional derivative in `H` is `g - A(t)u ∈ L²(0,1;H)`, and with `u(0) = 0`;
* `exists_lions_solution_of_C1` — `u` is a Lions solution in the sense of
  `LionsC12Challenge.IsLionsSolution`, with `∂ₜu, A_H u ∈ L²(0,1;H)` and
  `‖∂ₜu‖ + ‖A_H u‖ ≤ C ‖g‖`;
* `isMaxRegConstant_of_C1` — by uniqueness of the Lions solution and of distributional
  derivatives (`LionsC12.HasWeakDeriv.ae_eq`), `C` is a maximal-regularity constant
  (`IsMaxRegConstant`);
* `truncation_maximal_regularity` — for `0 ≤ ε ≤ 1` and every `N`, the truncated problem has
  maximal regularity: there is a finite `C` with `IsMaxRegConstant (aN D N ε) C`, and every
  `g ∈ L²(0,1;H)` has a Lions solution with `∂ₜw, A_{N,H}w ∈ L²(0,1;H)` and the estimate;
* `truncation_maxReg_growth` — existence and the lower bound together: the truncations have
  finite maximal-regularity constants, and every such constant `C_N` satisfies
  `√((πε²/1536)(log(N+2) - 1)) ≤ C_N √π C_f`;
* `optimalMaxRegConstant`, `truncation_optimalMaxRegConstant` — the optimal constant `C_N` of
  `𝔞_N` is attained, and satisfies the same lower bound.

No time regularity of the coefficient beyond continuity enters.  The constants depend on `N`
through `sup_{t,x} |∂ₓ𝔞_N(t,x)| ≤ ε ∑_{j ≤ N} j` (`abs_βxN_le`); for the full coefficient no
such bound holds, and `sup_t ‖A_H(t)‖_{L(D₀,H)} = ∞` (`LionsC12.not_uniform_bound_on_D₀`).
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped InnerProductSpace ComplexConjugate ContDiff

/-! ### The pairing of `H` with `D₀` and the forms on `D₀` -/

/-- The realified pairing `H → D₀'`, `h ↦ (v ↦ Re ⟨(I + A_{0,H})v, h⟩_H)`. -/
def pairD₀ : L2 Iπ →L[ℝ] StrongDual ℝ D₀ := reDual.comp ((ofHL D₀.shift).restrictScalars ℝ)

theorem pairD₀_apply (h : L2 Iπ) (v : D₀) : pairD₀ h v = (⟪D₀.shift v, h⟫_ℂ).re := rfl

theorem norm_pairD₀_apply_le (h : L2 Iπ) : ‖pairD₀ h‖ ≤ 2 * ‖h‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [pairD₀_apply, Real.norm_eq_abs]
  calc |(⟪D₀.shift v, h⟫_ℂ).re| ≤ ‖⟪D₀.shift v, h⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖D₀.shift v‖ * ‖h‖ := norm_inner_le_norm _ _
    _ ≤ 2 * ‖v‖ * ‖h‖ := by gcongr; exact D₀.norm_shift_le v
    _ = 2 * ‖h‖ * ‖v‖ := by ring

/-- `H → D₀'` is injective, since `I + A_{0,H} : D₀ → H` is onto. -/
theorem pairD₀_injective : Function.Injective pairD₀ := by
  intro h₁ h₂ he
  obtain ⟨v, hv⟩ := D₀.exists_shift_eq (h₁ - h₂)
  have e : pairD₀ h₁ v = pairD₀ h₂ v := by rw [he]
  rw [pairD₀_apply, pairD₀_apply] at e
  have h0 : (⟪D₀.shift v, h₁ - h₂⟫_ℂ).re = 0 := by
    rw [inner_sub_right, Complex.sub_re, e, sub_self]
  rw [hv] at h0
  have h0' : ‖h₁ - h₂‖ ^ 2 = 0 := by rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]; exact h0
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0'))

variable {c c' : ℝ → ℝ → ℝ} {m Λ L : ℝ}

/-- The real forms `b(t)[u,v] = Re ⟨(I + A_{0,H})v, A(t)u⟩_H` on `D₀`. -/
def formD₀ (hc : IsC1Coeff c c' m Λ L) (t : ℝ) : D₀ →L[ℝ] D₀ →L[ℝ] ℝ :=
  pairD₀.comp ((opA hc t).restrictScalars ℝ)

variable (hc : IsC1Coeff c c' m Λ L)

theorem formD₀_apply (t : ℝ) (u : D₀) : formD₀ hc t u = pairD₀ (opA hc t u) := rfl

theorem norm_formD₀_le (t : ℝ) : ‖formD₀ hc t‖ ≤ 2 * (Λ + L) := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (by have := hc.Λ_pos; have := hc.L_nonneg; positivity) fun u => ?_
  rw [formD₀_apply]
  calc _ ≤ 2 * ‖opA hc t u‖ := norm_pairD₀_apply_le _
    _ ≤ 2 * ((Λ + L) * ‖u‖) := by gcongr; exact norm_opA_apply_le hc t u
    _ = 2 * (Λ + L) * ‖u‖ := by ring

theorem continuous_formD₀ : Continuous (formD₀ hc) :=
  continuous_const.clm_comp ((ContinuousLinearMap.continuous_restrictScalars ℝ).comp
    (continuous_opA hc))

/-! ### Lions' theorem in `D₀ ⊂ V ⊂ D₀'` -/

theorem toReal_eLpNorm_le_mul {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure ℝ} {f : ℝ → E} {g : ℝ → F} (hf : AEStronglyMeasurable f μ) (hg : MemLp g 2 μ)
    {a : ℝ} (ha : 0 ≤ a) (h : ∀ᵐ t ∂μ, ‖f t‖ ≤ a * ‖g t‖) :
    (eLpNorm f 2 μ).toReal ≤ a * (eLpNorm g 2 μ).toReal := by
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf h 2
  have hfin : ENNReal.ofReal a * eLpNorm g 2 μ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top
  refine (ENNReal.toReal_mono hfin h1).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]

theorem aestronglyMeasurable_opA {u : ℝ → D₀} (hu : AEStronglyMeasurable u μ01) :
    AEStronglyMeasurable (fun t => opA hc t (u t)) μ01 :=
  (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := D₀) (F := L2 Iπ)).continuous.comp_aestronglyMeasurable
    ((continuous_opA hc).aestronglyMeasurable.prodMk hu)

theorem memLp_opA {u : ℝ → D₀} (hu : MemLp u 2 μ01) : MemLp (fun t => opA hc t (u t)) 2 μ01 :=
  hu.of_le_mul (aestronglyMeasurable_opA hc hu.aestronglyMeasurable)
    (Eventually.of_forall fun t => norm_opA_apply_le hc t (u t))

/-- **Lions' theorem in `D₀ ⊂ V ⊂ D₀'`.**  There is `K` such that for every `g ∈ L²(0,1;H)`
there is `u ∈ L²(0,1;D₀)` with `‖u‖_{L²(0,1;D₀)} ≤ K ‖g‖_{L²(0,1;H)}`, whose distributional
derivative in `H` is `g - A(t)u`, and with `u(t) = ∫₀ᵗ (g - A(τ)u)` for almost every `t`
(the initial value `u(0) = 0`).

The variational problem in the pivot `V` with the forms `b(t)[u,v] = Re ⟨(I + A_{0,H})v, A(t)u⟩`
and the data `v ↦ Re ⟨(I + A_{0,H})v, g(t)⟩` is solved by `LionsC12.lions_existence_garding`;
testing with `ψ(t) v`, `ψ ∈ C_c^∞(0,1)`, `v ∈ D₀`, and using that `I + A_{0,H}` is onto `H` gives
the distributional derivative. -/
theorem exists_D₀_solution :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ g : ℝ → L2 Iπ, MemLp g 2 μ01 →
      ∃ u : ℝ → D₀, MemLp u 2 μ01 ∧ (eLpNorm u 2 μ01).toReal ≤ K * (eLpNorm g 2 μ01).toReal ∧
        HasWeakDeriv (fun t => val Iπ (D₀.incl (u t))) (fun t => g t - opA hc t (u t)) ∧
        ∀ᵐ t ∂μ01, val Iπ (D₀.incl (u t)) = ∫ τ in (0 : ℝ)..t, (g τ - opA hc τ (u τ)) := by
  have hm := hc.pos
  set lam : ℝ := L ^ 2 / (2 * m) + m / 2
  have hlam0 : 0 ≤ lam := by positivity
  refine ⟨Real.exp (lam * 1) * (2 / min (1 / 2) (m / 2)), by positivity, fun g hg => ?_⟩
  let := InnerProductSpace.rclikeToReal ℂ D₀
  let := InnerProductSpace.rclikeToReal ℂ (H10 Iπ)
  set G := realTriple D₀.incl D₀.incl_injective D₀.denseRange_incl
  have hj : ∀ v, G.j v = D₀.incl v := fun v => rfl
  have hflat : ∀ x : D₀, G.flat (G.j x) = pairD₀ (val Iπ (D₀.incl x)) := by
    intro x
    ext v
    rw [GelfandTriple.flat_apply, real_inner_eq_re_inner, hj, hj, D₀.inner_incl, pairD₀_apply,
      ← inner_conj_symm, RCLike.conj_re]
    rfl
  have hmeas : AEStronglyMeasurable (formD₀ hc) (μT 1) :=
    (continuous_const.clm_comp (ContinuousLinearMap.continuous_restrictScalars ℝ)
      ).comp_aestronglyMeasurable (continuous_opA hc).aestronglyMeasurable
  have hcoer : ∀ t v, m / 2 * ‖v‖ ^ 2 ≤ formD₀ hc t v v + lam * ‖G.j v‖ ^ 2 := by
    intro t v
    rw [formD₀_apply, pairD₀_apply, ← inner_conj_symm, Complex.conj_re, hj]
    exact garding_opA hc t v
  set f : ℝ → StrongDual ℝ D₀ := fun t => pairD₀ (g t)
  have hf : MemLp f 2 (μT 1) := by rw [μT_one_eq_μ01]; exact pairD₀.comp_memLp' hg
  obtain ⟨u, hu, hbound⟩ := lions_existence_garding G one_pos hmeas (norm_formD₀_le hc) hcoer
    (by positivity) hlam0 hf 0
  obtain ⟨hweak, -⟩ := hasWeakDerivV'_of_variational_garding G one_pos hmeas (norm_formD₀_le hc)
    hcoer (by positivity) hf hu
  have hu2 : MemLp u 2 μ01 := by have := hu.1; rwa [μT_one_eq_μ01] at this
  have hAu := memLp_opA hc hu2
  set Y : ℝ → L2 Iπ := fun t => g t - opA hc t (u t) with hYdef
  have hY2 : MemLp Y 2 μ01 := hg.sub hAu
  have hFY : (fun t => f t - formD₀ hc t (u t)) = fun t => pairD₀ (Y t) := by
    funext t
    rw [hYdef, map_sub, formD₀_apply]
  set X : ℝ → L2 Iπ := fun t => val Iπ (D₀.incl (u t))
  have hX2 : MemLp X 2 μ01 := ((val Iπ).comp D₀.incl).comp_memLp' hu2
  have hXi : IntegrableOn X (Ioo 0 1) := hX2.integrable one_le_two
  have hYi : IntegrableOn Y (Ioo 0 1) := hY2.integrable one_le_two
  -- the distributional derivative in `H`
  have hder : HasWeakDeriv X Y := by
    have hFi : Integrable (fun t => f t - formD₀ hc t (u t)) (μT 1) := by
      rw [hFY, μT_one_eq_μ01]
      exact (pairD₀.comp_memLp' hY2).integrable one_le_two
    have h1 := hasWeakDeriv_flat_of_hasWeakDerivV' G (hu.1.integrable one_le_two) hFi hweak
    rw [hFY] at h1
    simp only [hflat] at h1
    exact HasWeakDeriv.of_map pairD₀ pairD₀_injective h1 hXi hYi
  refine ⟨u, hu2, ?_, hder, ?_⟩
  · -- the bound
    have hfn : (eLpNorm f 2 μ01).toReal ≤ 2 * (eLpNorm g 2 μ01).toReal :=
      toReal_eLpNorm_le_mul (pairD₀.comp_memLp' hg).aestronglyMeasurable hg (by norm_num)
        (Eventually.of_forall fun t => norm_pairD₀_apply_le (g t))
    rw [μT_one_eq_μ01, norm_zero, add_zero] at hbound
    calc _ ≤ _ := hbound
      _ ≤ Real.exp (lam * 1) * (2 * (eLpNorm g 2 μ01).toReal / min (1 / 2) (m / 2)) := by
          gcongr
      _ = _ := by ring
  · -- the initial value
    obtain ⟨c₀, hc₀⟩ := HasWeakDeriv.exists_ae_eq_const_add_integral hder hXi hYi
    have hc' : ∀ᵐ t ∂(μT 1), G.flat (G.j (u t))
        = pairD₀ c₀ + ∫ τ in (0 : ℝ)..t, (f τ - formD₀ hc τ (u τ)) := by
      rw [μT_one_eq_μ01]
      filter_upwards [hc₀, ae_restrict_mem measurableSet_Ioo] with t ht htI
      have hYt : IntervalIntegrable Y volume 0 t := by
        rw [intervalIntegrable_iff_integrableOn_Ioo_of_le htI.1.le]
        exact hYi.mono_set (Ioo_subset_Ioo_right htI.2.le)
      rw [hflat]
      change pairD₀ (X t) = _
      rw [ht, map_add, hFY, pairD₀.intervalIntegral_comp_comm hYt]
    have h0 := const_eq_flat_of_variational_garding G one_pos hmeas (norm_formD₀_le hc) hcoer
      (by positivity) hf hu hc'
    rw [map_zero, ← map_zero pairD₀] at h0
    have hc0 : c₀ = 0 := pairD₀_injective h0
    filter_upwards [hc₀] with t ht
    change X t = _
    rw [ht, hc0, zero_add]

/-! ### Lions solutions with maximal regularity -/

include hc in
/-- For a coefficient as in `IsC1Coeff`, every `g ∈ L²(0,1;H)` has a Lions solution `w` of
`w' + 𝒜(t)w = g`, `w(0) = 0`, whose distributional derivative `G` and elliptic part
`A_H(t)w(t)` lie in `L²(0,1;H)`, with `‖G‖ + ‖A_H w‖ ≤ C ‖g‖` for a `C` independent of `g`. -/
theorem exists_lions_solution_of_C1 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℝ → L2 Iπ, MemLp g 2 μ01 →
      ∃ (w : ℝ → H10 Iπ) (G Aw : ℝ → L2 Iπ), IsLionsSolution Iπ c g w ∧
        MemLp G 2 μ01 ∧ HasWeakDeriv (fun t => ofH10 Iπ (w t)) (fun t => ofL2 Iπ (G t)) ∧
        MemLp Aw 2 μ01 ∧ (∀ t, ∀ z : H10 Iπ, form Iπ c t (w t) z = ofL2 Iπ (Aw t) z) ∧
        (eLpNorm G 2 μ01).toReal + (eLpNorm Aw 2 μ01).toReal
          ≤ C * (eLpNorm g 2 μ01).toReal := by
  obtain ⟨K, hK, hsol⟩ := exists_D₀_solution hc
  have hΛL : 0 ≤ Λ + L := add_nonneg hc.Λ_pos.le hc.L_nonneg
  refine ⟨1 + 2 * ((Λ + L) * K), by positivity, fun g hg => ?_⟩
  obtain ⟨u, hu2, hbound, hder, hrep⟩ := hsol g hg
  set w : ℝ → H10 Iπ := fun t => D₀.incl (u t)
  set Aw : ℝ → L2 Iπ := fun t => opA hc t (u t)
  set G : ℝ → L2 Iπ := fun t => g t - Aw t with hGdef
  have hAw2 : MemLp Aw 2 μ01 := memLp_opA hc hu2
  have hG2 : MemLp G 2 μ01 := hg.sub hAw2
  have hw2 : MemLp w 2 μ01 := D₀.incl.comp_memLp' hu2
  have hGi : IntegrableOn G (Ioo 0 1) := hG2.integrable one_le_two
  have hvi : IntegrableOn (fun t => val Iπ (w t)) (Ioo 0 1) :=
    (((val Iπ).comp D₀.incl).comp_memLp' hu2).integrable one_le_two
  have hform : ∀ t, ∀ z : H10 Iπ, form Iπ c t (w t) z = ofL2 Iπ (Aw t) z :=
    fun t z => isRealisation_opA hc t (u t) z
  have hderV : HasWeakDeriv (fun t => ofH10 Iπ (w t)) (fun t => ofL2 Iπ (G t)) :=
    HasWeakDeriv.map hder hvi hGi ((ofHL (val Iπ)).restrictScalars ℝ)
  have hw'2 : MemLp (fun t => ofL2 Iπ (G t)) 2 μ01 := (ofHL (val Iπ)).comp_memLp' hG2
  -- the estimate
  have hAwn : (eLpNorm Aw 2 μ01).toReal ≤ (Λ + L) * (eLpNorm u 2 μ01).toReal :=
    toReal_eLpNorm_le_mul hAw2.aestronglyMeasurable hu2 hΛL
      (Eventually.of_forall fun t => norm_opA_apply_le hc t (u t))
  have hGn : (eLpNorm G 2 μ01).toReal
      ≤ (eLpNorm g 2 μ01).toReal + (eLpNorm Aw 2 μ01).toReal := by
    have h := eLpNorm_sub_le (f := g) (g := Aw) (μ := μ01) (p := 2) (by norm_num)
    rw [← ENNReal.toReal_add hg.eLpNorm_ne_top hAw2.eLpNorm_ne_top]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hg.eLpNorm_ne_top, hAw2.eLpNorm_ne_top⟩) h
  refine ⟨w, G, Aw, ⟨hw2, fun t => ofL2 Iπ (G t), hw'2, hderV,
    Eventually.of_forall fun t z => ?_, fun t => ofL2 Iπ (∫ τ in (0 : ℝ)..t, G τ), ?_, ?_, ?_⟩,
    hG2, hderV, hAw2, hform, ?_⟩
  · -- the equation `w' + 𝒜(t)w = g`
    rw [hform t z, ← add_apply, ← ofL2_add']
    simp only [hGdef, sub_add_cancel]
  · -- the continuous representative
    have hGI : IntegrableOn G (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one, integrableOn_Icc_iff_integrableOn_Ioo]
      exact hGi
    have h := intervalIntegral.continuousOn_primitive_interval hGI
    rw [uIcc_of_le zero_le_one] at h
    exact (ofHL (val Iπ)).continuous.comp_continuousOn h
  · filter_upwards [hrep] with t ht
    change ofL2 Iπ (∫ τ in (0 : ℝ)..t, G τ) = ofL2 Iπ (val Iπ (w t))
    rw [ht]
  · show ofL2 Iπ (∫ τ in (0 : ℝ)..0, G τ) = 0
    rw [intervalIntegral.integral_same, ofL2_eq_ofHL, map_zero]
  · calc _ ≤ (eLpNorm g 2 μ01).toReal + 2 * (eLpNorm Aw 2 μ01).toReal := by linarith
      _ ≤ (eLpNorm g 2 μ01).toReal + 2 * ((Λ + L) * (K * (eLpNorm g 2 μ01).toReal)) := by
          gcongr
          exact hAwn.trans (mul_le_mul_of_nonneg_left hbound hΛL)
      _ = _ := by ring

include hc in
/-- **Maximal `L²`-regularity for `C¹` coefficients**: for a coefficient as in `IsC1Coeff`
there is a finite maximal-regularity constant `C`, and every `g ∈ L²(0,1;H)` has a Lions
solution with `∂ₜw, A_H w ∈ L²(0,1;H)` and `‖∂ₜw‖ + ‖A_H w‖ ≤ C ‖g‖`. -/
theorem isMaxRegConstant_of_C1 :
    ∃ C : ℝ, 0 ≤ C ∧ IsMaxRegConstant c C ∧ ∀ g : ℝ → L2 Iπ, MemLp g 2 μ01 →
      ∃ (w : ℝ → H10 Iπ) (G Aw : ℝ → L2 Iπ), IsLionsSolution Iπ c g w ∧
        MemLp G 2 μ01 ∧ HasWeakDeriv (fun t => ofH10 Iπ (w t)) (fun t => ofL2 Iπ (G t)) ∧
        MemLp Aw 2 μ01 ∧ (∀ᵐ t ∂μ01, ∀ z, form Iπ c t (w t) z = ofL2 Iπ (Aw t) z) ∧
        (eLpNorm G 2 μ01).toReal + (eLpNorm Aw 2 μ01).toReal
          ≤ C * (eLpNorm g 2 μ01).toReal := by
  obtain ⟨C, hC, hex⟩ := exists_lions_solution_of_C1 hc
  refine ⟨C, hC, fun g w' G' Aw' hg hsol' hG' hder' hAw' hform' => ?_, fun g hg => ?_⟩
  · obtain ⟨w, G, Aw, hsol, hG2, hder, hAw2, hform, hest⟩ := hex g hg
    have huniq : ∀ᵐ t ∂μ01, w' t = w t :=
      isLionsSolution_unique isOpen_Ioo hc.isBoundedCoeff hc.nonneg hsol' hsol
    have hAeq : Aw' =ᵐ[μ01] Aw := by
      filter_upwards [hform', huniq] with t h1 h2
      apply ofL2_injective isOpen_Ioo
      ext z
      rw [← h1 z, h2, hform t z]
    have hGeq : G' =ᵐ[μ01] G := by
      have h := HasWeakDeriv.ae_eq hder' hder (huniq.mono fun t ht => by simp only [ht])
        (((ofHL (val Iπ)).comp_memLp' hG').integrable one_le_two)
        (((ofHL (val Iπ)).comp_memLp' hG2).integrable one_le_two)
      filter_upwards [h] with t ht
      exact ofL2_injective isOpen_Ioo ht
    rw [eLpNorm_congr_ae hGeq, eLpNorm_congr_ae hAeq]
    exact hest
  · obtain ⟨w, G, Aw, hsol, hG2, hder, hAw2, hform, hest⟩ := hex g hg
    exact ⟨w, G, Aw, hsol, hG2, hder, hAw2, Eventually.of_forall hform, hest⟩

/-! ### The truncated coefficients -/

/-- `|∂ₓβ^{(N)}(t,x)| ≤ ∑_{j ≤ N} j` for all `t, x`: the blocks `j ≤ N` have `M_j = j` modes. -/
theorem abs_βxN_le (D : Cutoffs) (N : ℕ) (t x : ℝ) :
    |βxN D N t x| ≤ ∑ j ∈ Finset.range (N + 1), (j : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ m ∈ Finset.Icc 1 (M j), |-(ηj D j t * Real.sin (θ j m t) * Real.sin (K j m * x))|
      ≤ ∑ m ∈ Finset.Icc 1 (M j), (1 : ℝ) := Finset.sum_le_sum fun m _ => by
        rw [abs_neg, abs_mul, abs_mul]
        have h1 := abs_ηj_le_one D j t
        have h2 := Real.abs_sin_le_one (θ j m t)
        have h3 := Real.abs_sin_le_one (K j m * x)
        calc |ηj D j t| * |Real.sin (θ j m t)| * |Real.sin (K j m * x)| ≤ 1 * 1 * 1 := by
              gcongr
          _ = 1 := by norm_num
    _ = j := by simp [M]

/-- For `0 ≤ ε ≤ 1` and every `N`, the truncated coefficient `𝔞_N` is a `C¹` coefficient with
`479/480 ≤ 𝔞_N ≤ 481/480` and `|∂ₓ𝔞_N| ≤ ∑_{j ≤ N} j`. -/
theorem isC1Coeff_aN (D : Cutoffs) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (N : ℕ) :
    IsC1Coeff (aN D N ε) (fun t x => ε * βxN D N t x) (479 / 480) (481 / 480)
      (∑ j ∈ Finset.range (N + 1), (j : ℝ)) where
  hasDerivAt t x := hasDerivAt_aN_x D N ε t x
  continuous := continuous_aN D N ε
  continuous_deriv := continuous_const.mul (continuous_βxN D N)
  pos := by norm_num
  ge t x := by
    have := abs_le.1 (abs_aN_sub_one_le D hε0 N t x)
    linarith
  le t x := by
    have := abs_le.1 (abs_aN_sub_one_le D hε0 N t x)
    linarith
  abs_deriv_le t x := by
    rw [abs_mul, abs_of_nonneg hε0]
    calc ε * |βxN D N t x| ≤ 1 * |βxN D N t x| := by gcongr
      _ ≤ _ := by rw [one_mul]; exact abs_βxN_le D N t x

/-- **The truncated problems have maximal `L²`-regularity** (the remark *Growth of the
maximal-regularity constant*: "these functions are finite sums of smooth functions, hence the
problem associated with `𝒜_N` has maximal `L²`-regularity").  For `0 ≤ ε ≤ 1` and every `N`
there is a finite maximal-regularity constant `C` for `𝔞_N = 1 + ε ∑_{j ≤ N} β_j`, and every
`g ∈ L²(0,1;H)` has a Lions solution `w` of `w' + 𝒜_N(t)w = g`, `w(0) = 0`, with
distributional derivative `G ∈ L²(0,1;H)` and elliptic part `A_{N,H}w ∈ L²(0,1;H)`, and
`‖G‖_{L²(0,1;H)} + ‖A_{N,H}w‖_{L²(0,1;H)} ≤ C ‖g‖_{L²(0,1;H)}`. -/
theorem truncation_maximal_regularity (D : Cutoffs) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ IsMaxRegConstant (aN D N ε) C ∧
      ∀ g : ℝ → L2 Iπ, MemLp g 2 μ01 →
        ∃ (w : ℝ → H10 Iπ) (G Aw : ℝ → L2 Iπ), IsLionsSolution Iπ (aN D N ε) g w ∧
          MemLp G 2 μ01 ∧ HasWeakDeriv (fun t => ofH10 Iπ (w t)) (fun t => ofL2 Iπ (G t)) ∧
          MemLp Aw 2 μ01 ∧ (∀ᵐ t ∂μ01, ∀ z, form Iπ (aN D N ε) t (w t) z = ofL2 Iπ (Aw t) z) ∧
          (eLpNorm G 2 μ01).toReal + (eLpNorm Aw 2 μ01).toReal
            ≤ C * (eLpNorm g 2 μ01).toReal :=
  isMaxRegConstant_of_C1 (isC1Coeff_aN D hε0 hε1 N)

/-- **The remark on the growth of the maximal-regularity constant**, existence and lower bound
together: for `0 ≤ ε ≤ 1` and every `N`, the truncated problem has a finite maximal-regularity
constant, and every maximal-regularity constant `C ≥ 0` of `𝔞_N` satisfies
`√((πε²/1536)(log(N+2) - 1)) ≤ C √π C_f`, i.e. `C_N ≳ ε √(log N)`. -/
theorem truncation_maxReg_growth (D : Cutoffs) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (N : ℕ) :
    (∃ C : ℝ, 0 ≤ C ∧ IsMaxRegConstant (aN D N ε) C) ∧
    ∀ C : ℝ, 0 ≤ C → IsMaxRegConstant (aN D N ε) C →
      Real.sqrt (π * ε ^ 2 / 1536 * (Real.log ((N : ℝ) + 2) - 1)) ≤ C * (Real.sqrt π * Cf D) :=
  ⟨let ⟨C, hC, hmax, _⟩ := truncation_maximal_regularity D hε0 hε1 N; ⟨C, hC, hmax⟩,
    (maxRegConstant_growth D hε0 hε1 N).2.2.2.2.2.2.2.2.2⟩

/-! ### The optimal constant -/

/-- The optimal maximal-regularity constant of `𝔞`: the infimum of the maximal-regularity
constants `C ≥ 0` (`0` if there is none). -/
def optimalMaxRegConstant (𝔞 : ℝ → ℝ → ℝ) : ℝ := sInf {C : ℝ | 0 ≤ C ∧ IsMaxRegConstant 𝔞 C}

/-- If `𝔞` has a maximal-regularity constant, the infimum of the constants is attained: it is
itself a maximal-regularity constant, the least one. -/
theorem isMaxRegConstant_optimal {𝔞 : ℝ → ℝ → ℝ} (h : ∃ C : ℝ, 0 ≤ C ∧ IsMaxRegConstant 𝔞 C) :
    0 ≤ optimalMaxRegConstant 𝔞 ∧ IsMaxRegConstant 𝔞 (optimalMaxRegConstant 𝔞) ∧
      ∀ C : ℝ, 0 ≤ C → IsMaxRegConstant 𝔞 C → optimalMaxRegConstant 𝔞 ≤ C := by
  have hbdd : BddBelow {C : ℝ | 0 ≤ C ∧ IsMaxRegConstant 𝔞 C} := ⟨0, fun C hC => hC.1⟩
  refine ⟨le_csInf h fun C hC => hC.1, fun g w G Aw hg hsol hG hder hAw hform => ?_,
    fun C hC hmax => csInf_le hbdd ⟨hC, hmax⟩⟩
  set X := (eLpNorm G 2 μ01).toReal + (eLpNorm Aw 2 μ01).toReal
  have hX : ∀ C ∈ {C : ℝ | 0 ≤ C ∧ IsMaxRegConstant 𝔞 C}, X ≤ C * (eLpNorm g 2 μ01).toReal :=
    fun C hC => hC.2 g w G Aw hg hsol hG hder hAw hform
  rcases (ENNReal.toReal_nonneg (a := eLpNorm g 2 μ01)).eq_or_lt with h0 | hpos
  · obtain ⟨C, hC⟩ := h
    have := hX C hC
    rw [← h0, mul_zero] at this ⊢
    exact this
  · have hle : X / (eLpNorm g 2 μ01).toReal ≤ optimalMaxRegConstant 𝔞 :=
      le_csInf h fun C hC => (div_le_iff₀ hpos).2 (hX C hC)
    exact (div_le_iff₀ hpos).1 hle

/-- **The optimal maximal-regularity constant of the truncated problems** grows like
`√(log N)`: for `0 ≤ ε ≤ 1` and every `N`, the optimal constant `C_N` of `𝔞_N` is finite and is
itself a maximal-regularity constant, and `√((πε²/1536)(log(N+2) - 1)) ≤ C_N √π C_f`. -/
theorem truncation_optimalMaxRegConstant (D : Cutoffs) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (N : ℕ) :
    0 ≤ optimalMaxRegConstant (aN D N ε) ∧
    IsMaxRegConstant (aN D N ε) (optimalMaxRegConstant (aN D N ε)) ∧
    (∀ C : ℝ, 0 ≤ C → IsMaxRegConstant (aN D N ε) C → optimalMaxRegConstant (aN D N ε) ≤ C) ∧
    Real.sqrt (π * ε ^ 2 / 1536 * (Real.log ((N : ℝ) + 2) - 1))
      ≤ optimalMaxRegConstant (aN D N ε) * (Real.sqrt π * Cf D) := by
  obtain ⟨hex, hlow⟩ := truncation_maxReg_growth D hε0 hε1 N
  obtain ⟨h0, hmax, hleast⟩ := isMaxRegConstant_optimal hex
  exact ⟨h0, hmax, hleast, hlow _ h0 hmax⟩

end LionsC12
