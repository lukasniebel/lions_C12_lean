module

public import LionsC12.Interval.Elements

/-!
# Dual norms in `H⁻¹((0,π);ℂ)` from estimates against `C¹` test functions

The estimates of `LionsC12.Solution.Bochner` for `u ∈ C¹([0,1];V')` are stated against real
`C¹` functions `w` vanishing at `0` and `π` (`IsTest`), normalised by `‖w'‖_{L²}`.  This file
shows that such an estimate controls the norm in the anti-dual of `H¹₀((0,π);ℂ)`:

* `testGraphSubmodule`, `pair_mem_closure_testGraph` — the test graphs form a subspace of
  `L² × L²`, so `H¹₀(U)` is the closure of the *set* of test graphs, and closed conditions
  extend from test graphs to `H¹₀(U)` (`forall_H10_of_closed`);
* `isTest_re`, `isTest_im` — real and imaginary parts of complex test functions on `(0,π)`;
* `norm_ofL2_toL2c_le` — `|∫₀^π g w| ≤ C ‖w'‖` for all `w ∈ IsTest` implies `‖g‖_{H⁻¹} ≤ 2C`
  (real and imaginary parts of a complex test function are real test functions).
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped InnerProductSpace ComplexConjugate

variable {U : Set ℝ}

/-- The test graphs form a subspace of `L²(U) × L²(U)`. -/
def testGraphSubmodule (U : Set ℝ) : Submodule ℂ (WithLp 2 (L2 U × L2 U)) where
  carrier := testGraph U
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, by simp, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict U)] with x hx
      simpa using hx
    · filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict U)] with x hx
      simpa using hx
  add_mem' := by
    rintro p q ⟨φ, hφ, hφc, hφs, hp1, hp2⟩ ⟨ψ, hψ, hψc, hψs, hq1, hq2⟩
    refine ⟨φ + ψ, hφ.add hψ, hφc.add hψc, (tsupport_add φ ψ).trans (union_subset hφs hψs), ?_,
      ?_⟩
    · filter_upwards [Lp.coeFn_add (WithLp.ofLp p).1 (WithLp.ofLp q).1, hp1, hq1] with x h h1 h2
      simp only [WithLp.ofLp_add, Prod.fst_add, Pi.add_apply]
      rw [h, Pi.add_apply, h1, h2]
    · filter_upwards [Lp.coeFn_add (WithLp.ofLp p).2 (WithLp.ofLp q).2, hp2, hq2] with x h h1 h2
      simp only [WithLp.ofLp_add, Prod.snd_add]
      rw [h, Pi.add_apply, h1, h2, deriv_add (hφ.differentiable one_ne_zero x)
        (hψ.differentiable one_ne_zero x)]
  smul_mem' := by
    rintro c p ⟨φ, hφ, hφc, hφs, hp1, hp2⟩
    refine ⟨c • φ, contDiff_const.smul hφ, hφc.smul_left,
      (tsupport_smul_subset_right (fun _ : ℝ => c) φ).trans hφs, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_smul c (WithLp.ofLp p).1, hp1] with x h h1
      simp only [WithLp.ofLp_smul, Prod.smul_fst]
      rw [h, Pi.smul_apply, h1, Pi.smul_apply]
    · filter_upwards [Lp.coeFn_smul c (WithLp.ofLp p).2, hp2] with x h h1
      simp only [WithLp.ofLp_smul, Prod.smul_snd]
      rw [h, Pi.smul_apply, h1, deriv_const_smul c (hφ.differentiable one_ne_zero x)]

/-- Every element of `H¹₀(U)` is a limit of test graphs. -/
theorem pair_mem_closure_testGraph (v : H10 U) : H10.pair v ∈ closure (testGraph U) := by
  have h1 : H10.pair v ∈ H10Graph U := H10.pair_mem v
  have h2 : H10Graph U ≤ (testGraphSubmodule U).topologicalClosure :=
    Submodule.topologicalClosure_mono (Submodule.span_le.2 fun _ hp => hp)
  have h3 := h2 h1
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at h3
  exact h3

/-- A closed condition on the graphs that holds on the test graphs holds on `H¹₀(U)`. -/
theorem forall_H10_of_closed {P : WithLp 2 (L2 U × L2 U) → Prop} (hP : IsClosed {p | P p})
    (h : ∀ p ∈ testGraph U, P p) (v : H10 U) : P (H10.pair v) :=
  closure_minimal (fun p hp => h p hp) hP (pair_mem_closure_testGraph v)

/-- The real part of a complex test function on `(0,π)` is a real test function. -/
theorem isTest_re {φ : ℝ → ℂ} (hφ : IsTestFun Iπ φ) :
    IsTest (fun x => (φ x).re) (fun x => (deriv φ x).re) where
  hasDerivAt x := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hφ.hasDerivAt x)
    exact this
  cont' := Complex.continuous_re.comp hφ.continuous_deriv
  zero_left := by rw [hφ.eq_zero_of_notMem (by simp), Complex.zero_re]
  zero_right := by rw [hφ.eq_zero_of_notMem (by simp), Complex.zero_re]

/-- The imaginary part of a complex test function on `(0,π)` is a real test function. -/
theorem isTest_im {φ : ℝ → ℂ} (hφ : IsTestFun Iπ φ) :
    IsTest (fun x => (φ x).im) (fun x => (deriv φ x).im) where
  hasDerivAt x := by
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hφ.hasDerivAt x)
    exact this
  cont' := Complex.continuous_im.comp hφ.continuous_deriv
  zero_left := by rw [hφ.eq_zero_of_notMem (by simp), Complex.zero_im]
  zero_right := by rw [hφ.eq_zero_of_notMem (by simp), Complex.zero_im]

theorem normSq_re_deriv_le {φ : ℝ → ℂ} (hφ : IsTestFun Iπ φ) :
    normSq (fun x => (deriv φ x).re) ≤ ‖toL2 Iπ (deriv φ) hφ.memLp_deriv‖ ^ 2 := by
  rw [norm_toL2_sq, normSq, ← integral_Iπ_eq]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) ?_
    (Eventually.of_forall fun x => ?_)
  · exact ((hφ.continuous_deriv.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
      ).mono_set Ioo_subset_Icc_self
  · simp only
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

theorem normSq_im_deriv_le {φ : ℝ → ℂ} (hφ : IsTestFun Iπ φ) :
    normSq (fun x => (deriv φ x).im) ≤ ‖toL2 Iπ (deriv φ) hφ.memLp_deriv‖ ^ 2 := by
  rw [norm_toL2_sq, normSq, ← integral_Iπ_eq]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) ?_
    (Eventually.of_forall fun x => ?_)
  · exact ((hφ.continuous_deriv.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
      ).mono_set Ioo_subset_Icc_self
  · simp only
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2

/-- **Dual norms from `C¹` test functions**: if `|∫₀^π g w| ≤ C ‖w'‖_{L²}` for every real `C¹`
function `w` vanishing at `0` and `π`, then `‖g‖_{H⁻¹((0,π))} ≤ 2C`. -/
theorem norm_ofL2_toL2c_le {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ w w' : ℝ → ℝ, IsTest w w' → |inner g w| ≤ C * Real.sqrt (normSq w')) :
    ‖ofL2 Iπ (toL2c g hg)‖ ≤ 2 * C := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  have key : ∀ p ∈ testGraph Iπ,
      ‖⟪(WithLp.ofLp p).1, toL2c g hg⟫_ℂ‖ ≤ 2 * C * ‖(WithLp.ofLp p).2‖ := by
    rintro p ⟨φ, hc, hcs, hsub, h1, h2⟩
    have hφ : IsTestFun Iπ φ := ⟨hc, hcs, hsub⟩
    have hp2 : (WithLp.ofLp p).2 = toL2 Iπ (deriv φ) hφ.memLp_deriv := by
      apply Lp.ext
      filter_upwards [h2, coe_toL2 (deriv φ) hφ.memLp_deriv] with x hx hx'
      rw [hx, hx']
    have hint : ⟪(WithLp.ofLp p).1, toL2c g hg⟫_ℂ
        = ((inner g fun x => (φ x).re : ℝ) : ℂ)
          - Complex.I * ((inner g fun x => (φ x).im : ℝ) : ℂ) := by
      rw [inner_L2_eq, inner, inner, ← intervalIntegral.integral_ofReal,
        ← intervalIntegral.integral_ofReal, ← integral_Iπ_eq_complex, ← integral_Iπ_eq_complex,
        ← integral_const_mul, ← integral_sub]
      · refine integral_congr_ae ?_
        filter_upwards [h1, coe_toL2c hg] with x hx hx'
        rw [hx, hx']
        apply Complex.ext <;> simp <;> ring
      · exact ((continuous_cplx (hg.mul (Complex.continuous_re.comp hφ.continuous))
          ).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
      · exact ((continuous_const.mul (continuous_cplx (hg.mul (Complex.continuous_im.comp
          hφ.continuous)))).continuousOn.integrableOn_compact isCompact_Icc).mono_set
          Ioo_subset_Icc_self
    rw [hint, hp2]
    have hr := h _ _ (isTest_re hφ)
    have hi := h _ _ (isTest_im hφ)
    have hr' : Real.sqrt (normSq fun x => (deriv φ x).re) ≤ ‖toL2 Iπ (deriv φ) hφ.memLp_deriv‖ :=
      (Real.sqrt_le_sqrt (normSq_re_deriv_le hφ)).trans (Real.sqrt_sq (norm_nonneg _)).le
    have hi' : Real.sqrt (normSq fun x => (deriv φ x).im) ≤ ‖toL2 Iπ (deriv φ) hφ.memLp_deriv‖ :=
      (Real.sqrt_le_sqrt (normSq_im_deriv_le hφ)).trans (Real.sqrt_sq (norm_nonneg _)).le
    calc ‖((inner g fun x => (φ x).re : ℝ) : ℂ) - Complex.I * ((inner g fun x => (φ x).im : ℝ) : ℂ)‖
        ≤ |inner g fun x => (φ x).re| + |inner g fun x => (φ x).im| := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ C * ‖toL2 Iπ (deriv φ) hφ.memLp_deriv‖ + C * ‖toL2 Iπ (deriv φ) hφ.memLp_deriv‖ := by
          gcongr
          · exact hr.trans (by gcongr)
          · exact hi.trans (by gcongr)
      _ = 2 * C * ‖toL2 Iπ (deriv φ) hφ.memLp_deriv‖ := by ring
  have hclosed : IsClosed {p : WithLp 2 (L2 Iπ × L2 Iπ) |
      ‖⟪(WithLp.ofLp p).1, toL2c g hg⟫_ℂ‖ ≤ 2 * C * ‖(WithLp.ofLp p).2‖} := by
    refine isClosed_le ?_ ?_
    · exact (((WithLp.fstL 2 ℂ (L2 Iπ) (L2 Iπ)).continuous).inner continuous_const).norm
    · exact continuous_const.mul ((WithLp.sndL 2 ℂ (L2 Iπ) (L2 Iπ)).continuous).norm
  have hz := forall_H10_of_closed hclosed key z
  calc ‖ofL2 Iπ (toL2c g hg) z‖ = ‖⟪val Iπ z, toL2c g hg⟫_ℂ‖ := rfl
    _ ≤ 2 * C * ‖dx Iπ z‖ := hz
    _ ≤ 2 * C * ‖z‖ := by gcongr; exact norm_dx_le z

end LionsC12
