module

public import LionsC12.Lions.Uniqueness
public import LionsC12.Spaces.Time

/-!
# Lions' theory on complex Gelfand triples: uniqueness of the variational solution

The paper works with complex Hilbert spaces `V ↪ H ↪ V'`, `V'` the anti-dual of `V`.  The
abstract theory of `LionsC12/Lions/` is written for real Gelfand triples.  A complex Hilbert space
is a real one for the inner product `Re ⟪·,·⟫` (`InnerProductSpace.rclikeToReal`), and an
anti-linear functional `ℓ` is determined by its real part `Re ∘ ℓ`, an element of the real dual
(`reDual`).  Through this realification the Lions–Magenes energy identity applies to the complex
problem, and gives:

* `IsLionsSol.ae_eq` — **uniqueness of the Lions variational solution**: two solutions of
  `w' + 𝒜(t)w = f` with zero initial value, for a family of forms with `Re 𝔞(t)[v,v] ≥ 0`,
  agree almost everywhere on `(0,1)`.

Here `IsLionsSol j a f w` is the class of Lions solutions of the Challenge statement
(`LionsC12Challenge.IsLionsSolution`), for an abstract complex Gelfand triple `j : V ↪ H`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge
open scoped InnerProductSpace ComplexConjugate

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The embedding `H ↪ V'` of a complex Gelfand triple `j : V ↪ H`: `h ↦ ⟨h, ·⟩ = ⟪j ·, h⟫`. -/
def ofHL (j : V →L[ℂ] H) : H →L[ℂ] (V →L⋆[ℂ] ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun h => (innerSLFlip ℂ h).comp j
      map_add' := fun h h' => by ext v; simp
      map_smul' := fun c h => by ext v; simp }
    ‖j‖ (fun h => by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_comp,
        Function.comp_apply, innerSLFlip_apply_apply]
      calc ‖⟪j v, h⟫_ℂ‖ ≤ ‖j v‖ * ‖h‖ := norm_inner_le_norm _ _
        _ ≤ ‖j‖ * ‖v‖ * ‖h‖ := by gcongr; exact j.le_opNorm v
        _ = ‖j‖ * ‖h‖ * ‖v‖ := by ring)

@[simp] theorem ofHL_apply (j : V →L[ℂ] H) (h : H) (v : V) : ofHL j h v = ⟪j v, h⟫_ℂ := rfl

/-- The class of **Lions variational solutions** of `w' + 𝒜(t)w = f` in `V'` on `(0,1)` with
`w(0) = 0`, for a complex Gelfand triple `j : V ↪ H` and a family of forms `a(t)`:
`w ∈ L²(0,1;V)`, its distributional derivative `w'` as a `V'`-valued function lies in
`L²(0,1;V')`, the equation holds a.e., and the continuous `V'`-representative vanishes at `0`.
For `j = val U`, `a = form U 𝔞` this is `LionsC12Challenge.IsLionsSolution`
(`isLionsSolution_iff`). -/
def IsLionsSol (j : V →L[ℂ] H) (a : ℝ → V → V → ℂ) (f : ℝ → H) (w : ℝ → V) : Prop :=
  MemLp w 2 μ01 ∧
  ∃ w' : ℝ → (V →L⋆[ℂ] ℂ), MemLp w' 2 μ01 ∧
    HasWeakDeriv (fun t => ofHL j (j (w t))) w' ∧
    (∀ᵐ t ∂μ01, ∀ z : V, w' t z + a t (w t) z = ofHL j (f t) z) ∧
    ∃ w₀ : ℝ → (V →L⋆[ℂ] ℂ), ContinuousOn w₀ (Icc 0 1) ∧
      (∀ᵐ t ∂μ01, w₀ t = ofHL j (j (w t))) ∧ w₀ 0 = 0

/-! ### Realification -/

/-- The real part `Re ∘ ℓ` of an anti-linear functional, as an element of the real dual. -/
def reDualFun (ℓ : V →L⋆[ℂ] ℂ) : StrongDual ℝ V :=
  LinearMap.mkContinuous
    { toFun := fun v => (ℓ v).re
      map_add' := fun v w => by simp
      map_smul' := fun r v => by
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r v, ContinuousLinearMap.map_smulₛₗ]
        simp }
    ‖ℓ‖ (fun v => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (ℓ.le_opNorm v))

@[simp] theorem reDualFun_apply (ℓ : V →L⋆[ℂ] ℂ) (v : V) : reDualFun ℓ v = (ℓ v).re := rfl

/-- `ℓ ↦ Re ∘ ℓ` as a bounded real-linear map `V' → StrongDual ℝ V`. -/
def reDual : (V →L⋆[ℂ] ℂ) →L[ℝ] StrongDual ℝ V :=
  LinearMap.mkContinuous
    { toFun := reDualFun
      map_add' := fun ℓ ℓ' => by ext v; simp
      map_smul' := fun r ℓ => by
        ext v
        simp }
    1 (fun ℓ : V →L⋆[ℂ] ℂ => by
      rw [one_mul]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, reDualFun_apply, Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (ℓ.le_opNorm v))

@[simp] theorem reDual_apply (ℓ : V →L⋆[ℂ] ℂ) (v : V) : reDual ℓ v = (ℓ v).re := rfl

/-- An anti-linear functional is determined by its real part. -/
theorem reDual_injective : Function.Injective (reDual : (V →L⋆[ℂ] ℂ) → StrongDual ℝ V) := by
  intro ℓ ℓ' h
  ext v
  have hre : ∀ w, (ℓ w).re = (ℓ' w).re := fun w => by
    have := congrArg (fun L : StrongDual ℝ V => L w) h
    simpa using this
  apply Complex.ext (hre v)
  have h1 := hre (Complex.I • v)
  simp only [ContinuousLinearMap.map_smulₛₗ, Complex.conj_I, smul_eq_mul, neg_mul,
    Complex.neg_re, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_sub,
    neg_neg] at h1
  exact h1

/-- The real Gelfand triple underlying a complex one. -/
def realTriple [CompleteSpace V] [CompleteSpace H] (j : V →L[ℂ] H) (hj : Function.Injective j)
    (hd : DenseRange j) :
    letI := InnerProductSpace.rclikeToReal ℂ V
    letI := InnerProductSpace.rclikeToReal ℂ H
    GelfandTriple V H :=
  letI := InnerProductSpace.rclikeToReal ℂ V
  letI := InnerProductSpace.rclikeToReal ℂ H
  ⟨j.restrictScalars ℝ, hj, hd⟩

theorem realTriple_flat [CompleteSpace V] [CompleteSpace H] (j : V →L[ℂ] H)
    (hj : Function.Injective j) (hd : DenseRange j) (h : H) :
    letI := InnerProductSpace.rclikeToReal ℂ V
    letI := InnerProductSpace.rclikeToReal ℂ H
    (realTriple j hj hd).flat h = reDual (ofHL j h) := by
  let := InnerProductSpace.rclikeToReal ℂ V
  let := InnerProductSpace.rclikeToReal ℂ H
  ext v
  rw [GelfandTriple.flat_apply, reDual_apply, ofHL_apply, real_inner_eq_re_inner,
    ← inner_conj_symm, RCLike.conj_re]
  rfl

/-! ### Uniqueness -/

/-- **Uniqueness of the Lions variational solution.**  Let `j : V ↪ H` be a complex Gelfand
triple and `a(t)` a family of forms, additive in the first argument, with `Re a(t)[v,v] ≥ 0`.
Two Lions solutions of `w' + 𝒜(t)w = f`, `w(0) = 0`, agree almost everywhere on `(0,1)`.

The difference `w` solves the homogeneous problem; the Lions–Magenes identity, applied to the
realified triple, gives a representative `w̃ ∈ C([0,1);H)` with
`‖w̃(t)‖² = ‖w̃(0)‖² + 2 ∫₀ᵗ Re ⟨w', w⟩ = -2 ∫₀ᵗ Re a(τ)[w,w] ≤ 0`, and `w̃(0) = 0` because the
continuous `V'`-representative of `w` vanishes at `0`. -/
theorem IsLionsSol.ae_eq [CompleteSpace V] [CompleteSpace H] {j : V →L[ℂ] H}
    (hj : Function.Injective j) (hd : DenseRange j)
    {a : ℝ → V → V → ℂ} (ha_sub : ∀ t v₁ v₂ z, a t (v₁ - v₂) z = a t v₁ z - a t v₂ z)
    (ha : ∀ t v, 0 ≤ (a t v v).re) {f : ℝ → H} {w₁ w₂ : ℝ → V}
    (h₁ : IsLionsSol j a f w₁) (h₂ : IsLionsSol j a f w₂) : ∀ᵐ t ∂μ01, w₁ t = w₂ t := by
  obtain ⟨hw₁, w₁', hw₁', hd₁, he₁, w₁₀, hc₁, hae₁, h0₁⟩ := h₁
  obtain ⟨hw₂, w₂', hw₂', hd₂, he₂, w₂₀, hc₂, hae₂, h0₂⟩ := h₂
  set D : V →L[ℂ] (V →L⋆[ℂ] ℂ) := (ofHL j).comp j with hDdef
  set w : ℝ → V := fun t => w₁ t - w₂ t with hwdef
  set w' : ℝ → (V →L⋆[ℂ] ℂ) := fun t => w₁' t - w₂' t with hw'def
  have hw : MemLp w 2 μ01 := hw₁.sub hw₂
  have hw' : MemLp w' 2 μ01 := hw₁'.sub hw₂'
  have hDi : ∀ {u : ℝ → V}, MemLp u 2 μ01 → IntegrableOn (fun t => D (u t)) (Ioo 0 1) :=
    fun hu => ((D.restrictScalars ℝ).integrable_comp (hu.integrable one_le_two))
  have hder : HasWeakDeriv (fun t => D (w t)) w' := by
    have := HasWeakDeriv.sub hd₁ hd₂ (hDi hw₁) (hDi hw₂) (hw₁'.integrable one_le_two)
      (hw₂'.integrable one_le_two)
    simpa [hwdef, hw'def, hDdef, map_sub] using this
  have heq : ∀ᵐ t ∂μ01, ∀ z, w' t z + a t (w t) z = 0 := by
    filter_upwards [he₁, he₂] with t ht₁ ht₂ z
    have e₁ := ht₁ z
    have e₂ := ht₂ z
    simp only [hw'def, hwdef, sub_apply, ha_sub]
    linear_combination e₁ - e₂
  -- the absolutely continuous representative of `D ∘ w`
  obtain ⟨c, hc⟩ := HasWeakDeriv.exists_ae_eq_const_add_integral hder (hDi hw)
    (hw'.integrable one_le_two)
  -- realification
  let := InnerProductSpace.rclikeToReal ℂ V
  let := InnerProductSpace.rclikeToReal ℂ H
  set G := realTriple j hj hd with hGdef
  have hflat : ∀ v, G.flat (G.j v) = reDual (D v) := fun v => realTriple_flat j hj hd (j v)
  set g : ℝ → StrongDual ℝ V := fun t => reDual (w' t) with hgdef
  have hg2 : MemLp g 2 (μT 1) := by
    rw [μT_one_eq_μ01]; exact reDual.comp_memLp' hw'
  have hu2 : MemLp w 2 (μT 1) := by rw [μT_one_eq_μ01]; exact hw
  have hw'i : IntegrableOn w' (Ioo 0 1) := hw'.integrable one_le_two
  have hprim : ∀ t ∈ Icc (0 : ℝ) 1,
      reDual (∫ τ in (0 : ℝ)..t, w' τ) = ∫ τ in (0 : ℝ)..t, g τ := by
    intro t ht
    refine (reDual.intervalIntegral_comp_comm ?_).symm
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
    exact hw'i.mono_set (Ioo_subset_Ioo_right ht.2)
  have hcR : ∀ᵐ t ∂(μT 1), G.flat (G.j (w t)) = reDual c + ∫ τ in (0 : ℝ)..t, g τ := by
    rw [μT_one_eq_μ01]
    filter_upwards [hc, ae_restrict_mem measurableSet_Ioo] with t ht htmem
    rw [hflat, ht, map_add, hprim t (Ioo_subset_Icc_self htmem)]
  -- the continuous representative vanishes at `0`
  have hc0 : reDual c = 0 := by
    have hcont₀ : ContinuousOn (fun t => reDual (w₁₀ t - w₂₀ t)) (Icc 0 1) :=
      reDual.continuous.comp_continuousOn (hc₁.sub hc₂)
    have hgI : IntegrableOn g (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one]
      have : IntegrableOn g (Ioo 0 1) := (reDual.integrable_comp hw'i)
      exact this.congr_set_ae Ioo_ae_eq_Icc.symm
    have hcont₁ : ContinuousOn (fun t => reDual c + ∫ τ in (0 : ℝ)..t, g τ) (Icc 0 1) := by
      have := intervalIntegral.continuousOn_primitive_interval hgI
      rw [uIcc_of_le zero_le_one] at this
      exact continuousOn_const.add this
    have hae : (fun t => reDual (w₁₀ t - w₂₀ t)) =ᵐ[volume.restrict (Icc 0 1)]
        (fun t => reDual c + ∫ τ in (0 : ℝ)..t, g τ) := by
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc.symm]
      filter_upwards [hae₁, hae₂, hcR.filter_mono (by rw [μT_one_eq_μ01])] with t ht₁ ht₂ ht
      rw [ht₁, ht₂, ← map_sub, ← ht, hflat]
      simp [hwdef, hDdef]
    have := Measure.eqOn_Icc_of_ae_eq volume (zero_ne_one) hae hcont₀ hcont₁
      (left_mem_Icc.2 zero_le_one)
    simpa [h0₁, h0₂] using this.symm
  have hrep0 : limRep G 1 w 0 = 0 := by
    apply G.flat_injective
    rw [flat_limRep G hu2 hg2 hcR one_pos (left_mem_Ico.2 one_pos), hc0, map_zero]
    simp
  -- the energy is non-increasing, hence zero
  have hneg : ∀ᵐ τ ∂μ01, g τ (w τ) ≤ 0 := by
    filter_upwards [heq] with τ hτ
    have := hτ (w τ)
    rw [hgdef]
    simp only [reDual_apply]
    have hre : (w' τ (w τ)).re = -(a τ (w τ) (w τ)).re := by
      rw [eq_neg_of_add_eq_zero_left this, Complex.neg_re]
    rw [hre]
    exact neg_nonpos.2 (ha τ (w τ))
  have hzero : ∀ t ∈ Ico (0 : ℝ) 1, limRep G 1 w t = 0 := by
    intro t ht
    have hE := energy_limRep G hu2 hg2 hcR one_pos (left_mem_Ico.2 one_pos) ht
    rw [hrep0, norm_zero] at hE
    have hint : ∫ τ in (0 : ℝ)..t, g τ (w τ) ≤ 0 := by
      rw [intervalIntegral.integral_of_le ht.1]
      refine integral_nonpos_of_ae ?_
      exact ae_restrict_of_ae_restrict_of_subset
        (fun τ (hτ : τ ∈ Ioc 0 t) => (⟨hτ.1, lt_of_le_of_lt hτ.2 ht.2⟩ : τ ∈ Ioo (0 : ℝ) 1)) hneg
    have : ‖limRep G 1 w t‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg (limRep G 1 w t)])
  have hlim := limRep_ae_eq G hu2 hg2 hcR one_pos
  rw [μT_one_eq_μ01] at hlim
  filter_upwards [hlim, ae_restrict_mem measurableSet_Ioo] with t ht htmem
  have h0 : G.j (w t) = 0 := by rw [← ht]; exact hzero t ⟨htmem.1.le, htmem.2⟩
  have : w t = 0 := G.injective (by rw [h0, map_zero])
  exact sub_eq_zero.1 this

end LionsC12
