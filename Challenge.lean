module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Lions' maximal regularity problem: failure at the ½-Hölder endpoint

L. Niebel, *Lions' maximal regularity problem for divergence-form differential operators:
failure at the ½-Hölder endpoint*, arXiv:2608.11194v2, Theorem 1.1 and Corollary 1.2.

For the non-autonomous Dirichlet problem `∂ₜu - ∂ₓ(𝔞(t,·)∂ₓu) = f` on `(0,1) × (0,π)` with
`u(0) = 0`, Lions' variational theory gives a unique solution in `L²(0,1;H¹₀) ∩ H¹(0,1;H⁻¹)`.
The theorems assert that `½`-Hölder continuity of the coefficient in time, with values in
`L^∞`, does not give maximal `L²`-regularity `∂ₜu ∈ L²(0,1;L²)`, even for coefficients
arbitrarily close to `1`, on an interval and on every bounded domain of every dimension.

## Conventions

* All spaces are complex, as in the paper; Lebesgue measure throughout.  `L2 U` is
  `L²(U;ℂ) = Lp ℂ 2 (volume.restrict U)`.
* `H10 U` is `H¹₀(U;ℂ)`: the closure of the graphs `(φ, φ')`, `φ ∈ C¹_c(U;ℂ)`, in
  `L²(U;ℂ) × L²(U;ℂ)` with the norm `(‖v‖² + ‖v'‖²)^{1/2}` (Brezis, §8.3); `val` and `dx` are the
  two components.  `Hm1 U` is its anti-dual, the continuous conjugate-linear functionals, and
  `ofL2`, `ofH10` are the embeddings `L² ↪ H⁻¹`, `H¹₀ ↪ H⁻¹`, `h ↦ ∫ h conj(·)`.
* `form U 𝔞 t v w = ∫_U 𝔞(t,x) ∂ₓv conj(∂ₓw) dx` is `⟨𝒜(t)v, w⟩` for `𝒜(t) = -∂ₓ(𝔞(t,·)∂ₓ)`.
* On `Ω ⊆ ℝ^d = EuclideanSpace ℝ (Fin d)` the same with the gradient (`H10Ω`, `formΩ`, …).
* Time derivatives: `HasDerivWithinAt … (Icc 0 1)` for `C¹([0,1];V')`; `HasWeakDeriv` for
  distributional derivatives on `(0,1)`, with `C_c^∞((0,1))` test functions.
* `IsLionsSolution` is the class of Lions variational solutions with zero initial value.
-/

@[expose] public section

noncomputable section

namespace LionsC12Challenge

open MeasureTheory Set
open scoped ENNReal InnerProductSpace ContDiff

/-- `L²(U;ℂ)` for a set `U ⊆ ℝ`, with Lebesgue measure. -/
abbrev L2 (U : Set ℝ) : Type := Lp ℂ 2 (volume.restrict U)

/-- The graphs `(φ, φ')` of the test functions `φ ∈ C¹_c(U;ℂ)` (continuously differentiable,
compactly supported in `U`), as elements of `L²(U;ℂ) × L²(U;ℂ)` with the Hilbert norm
`(‖v‖² + ‖g‖²)^{1/2}`. -/
def testGraph (U : Set ℝ) : Set (WithLp 2 (L2 U × L2 U)) :=
  {p | ∃ φ : ℝ → ℂ, ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
    ⇑(WithLp.ofLp p).1 =ᵐ[volume.restrict U] φ ∧
    ⇑(WithLp.ofLp p).2 =ᵐ[volume.restrict U] deriv φ}

/-- The closure of the test graphs in `L²(U;ℂ) × L²(U;ℂ)`: the graph of `∂ₓ` on `H¹₀(U;ℂ)`. -/
def H10Graph (U : Set ℝ) : Submodule ℂ (WithLp 2 (L2 U × L2 U)) :=
  (Submodule.span ℂ (testGraph U)).topologicalClosure

/-- `H¹₀(U;ℂ)`: the closure of `C¹_c(U;ℂ)` in `H¹(U;ℂ)`, realised as the closure of the
graphs `(φ, φ')` in `L²(U;ℂ) × L²(U;ℂ)` (Brezis, *Functional Analysis*, §8.3).  An element is a
pair `(v, ∂ₓv)`; its norm is `(‖v‖² + ‖∂ₓv‖²)^{1/2}`. -/
def H10 (U : Set ℝ) : Type := H10Graph U

/-- The Hilbert norm `(‖v‖² + ‖∂ₓv‖²)^{1/2}` of `H¹₀(U;ℂ)`. -/
instance instNormedAddCommGroupH10 (U : Set ℝ) : NormedAddCommGroup (H10 U) :=
  inferInstanceAs (NormedAddCommGroup (H10Graph U))

/-- The inner product `⟨v, w⟩ + ⟨∂ₓv, ∂ₓw⟩` of `H¹₀(U;ℂ)`. -/
instance instInnerProductSpaceH10 (U : Set ℝ) : InnerProductSpace ℂ (H10 U) :=
  inferInstanceAs (InnerProductSpace ℂ (H10Graph U))

/-- The embedding `H¹₀(U;ℂ) ↪ L²(U;ℂ)`, `v ↦ v`. -/
def val (U : Set ℝ) : H10 U →L[ℂ] L2 U :=
  (WithLp.fstL 2 ℂ (L2 U) (L2 U)).comp (H10Graph U).subtypeL

/-- The weak derivative `∂ₓ : H¹₀(U;ℂ) → L²(U;ℂ)`. -/
def dx (U : Set ℝ) : H10 U →L[ℂ] L2 U :=
  (WithLp.sndL 2 ℂ (L2 U) (L2 U)).comp (H10Graph U).subtypeL

/-- `H⁻¹(U;ℂ)`: the anti-dual of `H¹₀(U;ℂ)`, the continuous conjugate-linear functionals. -/
abbrev Hm1 (U : Set ℝ) : Type := H10 U →L⋆[ℂ] ℂ

/-- The embedding `L²(U;ℂ) ↪ H⁻¹(U;ℂ)`: `h` acts by `w ↦ ⟨h, w⟩ = ∫_U h conj(w)`. -/
def ofL2 (U : Set ℝ) (h : L2 U) : Hm1 U := (innerSLFlip ℂ h).comp (val U)

/-- The embedding `H¹₀(U;ℂ) ↪ H⁻¹(U;ℂ)`, through `L²(U;ℂ)`. -/
def ofH10 (U : Set ℝ) (v : H10 U) : Hm1 U := ofL2 U (val U v)

/-- The sesquilinear form `𝔞(t)[v,w] = ∫_U 𝔞(t,x) ∂ₓv(x) conj(∂ₓw(x)) dx` of the operator
`𝒜(t) = -∂ₓ(𝔞(t,·) ∂ₓ) : H¹₀ → H⁻¹`, that is `⟨𝒜(t)v, w⟩ = 𝔞(t)[v,w]`. -/
def form (U : Set ℝ) (𝔞 : ℝ → ℝ → ℝ) (t : ℝ) (v w : H10 U) : ℂ :=
  ∫ x in U, (𝔞 t x : ℂ) * dx U v x * (starRingEnd ℂ) (dx U w x)

/-- `g` is the distributional derivative of `u : ℝ → E` on the time interval `(0,1)`:
`∫₀¹ φ'(t) u(t) dt = -∫₀¹ φ(t) g(t) dt` for every `φ ∈ C_c^∞((0,1);ℝ)`. -/
def HasWeakDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u g : ℝ → E) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 1 →
    ∫ t in Ioo 0 1, deriv φ t • u t = -∫ t in Ioo 0 1, φ t • g t

/-- `w` is a Lions variational solution of `w' + 𝒜(t)w = f` in `H⁻¹(U)` on `(0,1)` with
`w(0) = 0`: `w ∈ L²(0,1;H¹₀)`, its distributional derivative `w'` (as an `H⁻¹`-valued function)
lies in `L²(0,1;H⁻¹)`, `w'(t) + 𝒜(t)w(t) = f(t)` for almost every `t`, and the continuous
`H⁻¹`-valued representative of `w` vanishes at `t = 0`. -/
def IsLionsSolution (U : Set ℝ) (𝔞 : ℝ → ℝ → ℝ) (f : ℝ → L2 U) (w : ℝ → H10 U) : Prop :=
  MemLp w 2 (volume.restrict (Ioo 0 1)) ∧
  ∃ w' : ℝ → Hm1 U, MemLp w' 2 (volume.restrict (Ioo 0 1)) ∧
    HasWeakDeriv (fun t => ofH10 U (w t)) w' ∧
    (∀ᵐ t ∂(volume.restrict (Ioo 0 1)),
      ∀ z : H10 U, w' t z + form U 𝔞 t (w t) z = ofL2 U (f t) z) ∧
    ∃ w₀ : ℝ → Hm1 U, ContinuousOn w₀ (Icc 0 1) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo 0 1)), w₀ t = ofH10 U (w t)) ∧ w₀ 0 = 0

/-- `L²(Ω;ℂ)` for a set `Ω ⊆ ℝ^d`, with Lebesgue measure. -/
abbrev L2Ω (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) : Type :=
  Lp ℂ 2 (volume.restrict Ω)

/-- `L²(Ω;ℂ^d)`, the space of the gradients. -/
abbrev L2Ωvec (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) : Type :=
  Lp (EuclideanSpace ℂ (Fin d)) 2 (volume.restrict Ω)

/-- The gradient `∇φ(x) = (∂₁φ(x), …, ∂_dφ(x)) ∈ ℂ^d` of `φ : ℝ^d → ℂ`. -/
def grad {d : ℕ} (φ : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun i => fderiv ℝ φ x (EuclideanSpace.single i 1)

/-- The graphs `(φ, ∇φ)` of the test functions `φ ∈ C¹_c(Ω;ℂ)`, in `L²(Ω;ℂ) × L²(Ω;ℂ^d)`. -/
def testGraphΩ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    Set (WithLp 2 (L2Ω d Ω × L2Ωvec d Ω)) :=
  {p | ∃ φ : EuclideanSpace ℝ (Fin d) → ℂ, ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ Ω ∧ ⇑(WithLp.ofLp p).1 =ᵐ[volume.restrict Ω] φ ∧
    ⇑(WithLp.ofLp p).2 =ᵐ[volume.restrict Ω] grad φ}

/-- The closure of the test graphs in `L²(Ω;ℂ) × L²(Ω;ℂ^d)`: the graph of `∇` on `H¹₀(Ω;ℂ)`. -/
def H10ΩGraph (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    Submodule ℂ (WithLp 2 (L2Ω d Ω × L2Ωvec d Ω)) :=
  (Submodule.span ℂ (testGraphΩ d Ω)).topologicalClosure

/-- `H¹₀(Ω;ℂ)`: the closure of `C¹_c(Ω;ℂ)` in `H¹(Ω;ℂ)`, realised as the closure of the
graphs `(φ, ∇φ)` in `L²(Ω;ℂ) × L²(Ω;ℂ^d)`; the norm is `(‖v‖² + ‖∇v‖²)^{1/2}`. -/
def H10Ω (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) : Type := H10ΩGraph d Ω

/-- The Hilbert norm `(‖v‖² + ‖∇v‖²)^{1/2}` of `H¹₀(Ω;ℂ)`. -/
instance instNormedAddCommGroupH10Ω (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    NormedAddCommGroup (H10Ω d Ω) :=
  inferInstanceAs (NormedAddCommGroup (H10ΩGraph d Ω))

/-- The inner product `⟨v, w⟩ + ⟨∇v, ∇w⟩` of `H¹₀(Ω;ℂ)`. -/
instance instInnerProductSpaceH10Ω (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    InnerProductSpace ℂ (H10Ω d Ω) :=
  inferInstanceAs (InnerProductSpace ℂ (H10ΩGraph d Ω))

/-- The embedding `H¹₀(Ω;ℂ) ↪ L²(Ω;ℂ)`. -/
def valΩ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) : H10Ω d Ω →L[ℂ] L2Ω d Ω :=
  (WithLp.fstL 2 ℂ (L2Ω d Ω) (L2Ωvec d Ω)).comp (H10ΩGraph d Ω).subtypeL

/-- The weak gradient `∇ : H¹₀(Ω;ℂ) → L²(Ω;ℂ^d)`. -/
def gradΩ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) : H10Ω d Ω →L[ℂ] L2Ωvec d Ω :=
  (WithLp.sndL 2 ℂ (L2Ω d Ω) (L2Ωvec d Ω)).comp (H10ΩGraph d Ω).subtypeL

/-- `H⁻¹(Ω;ℂ)`: the anti-dual of `H¹₀(Ω;ℂ)`. -/
abbrev Hm1Ω (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) : Type := H10Ω d Ω →L⋆[ℂ] ℂ

/-- The embedding `L²(Ω;ℂ) ↪ H⁻¹(Ω;ℂ)`: `h` acts by `w ↦ ∫_Ω h conj(w)`. -/
def ofL2Ω (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (h : L2Ω d Ω) : Hm1Ω d Ω :=
  (innerSLFlip ℂ h).comp (valΩ d Ω)

/-- The embedding `H¹₀(Ω;ℂ) ↪ H⁻¹(Ω;ℂ)`, through `L²(Ω;ℂ)`. -/
def ofH10Ω (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (v : H10Ω d Ω) : Hm1Ω d Ω :=
  ofL2Ω d Ω (valΩ d Ω v)

/-- The isotropic coefficient matrix `𝔅(t,x) = 𝔟(t,x) Id_d`, as a linear map of `ℝ^d`; its
norm is the operator norm. -/
def isoCoeff {d : ℕ} (𝔟 : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  𝔟 t x • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))

/-- The form `∫_Ω 𝔅(t,x)∇v(x) · conj(∇w(x)) dx = ∫_Ω 𝔟(t,x) ∇v(x) · conj(∇w(x)) dx` of the
operator `-div(𝔅(t,·)∇) : H¹₀(Ω) → H⁻¹(Ω)` with `𝔅 = 𝔟 Id_d` (`isoCoeff 𝔟`). -/
def formΩ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (𝔟 : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (v w : H10Ω d Ω) : ℂ :=
  ∫ x in Ω, (𝔟 t x : ℂ) * ⟪gradΩ d Ω w x, gradΩ d Ω v x⟫_ℂ

/-- `w` is a Lions variational solution of `w' - div(𝔟 Id_d ∇w) = F` in `H⁻¹(Ω)` on `(0,1)`
with `w(0) = 0` (as `IsLionsSolution`, on `Ω`). -/
def IsLionsSolutionΩ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (𝔟 : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (F : ℝ → L2Ω d Ω) (w : ℝ → H10Ω d Ω) : Prop :=
  MemLp w 2 (volume.restrict (Ioo 0 1)) ∧
  ∃ w' : ℝ → Hm1Ω d Ω, MemLp w' 2 (volume.restrict (Ioo 0 1)) ∧
    HasWeakDeriv (fun t => ofH10Ω d Ω (w t)) w' ∧
    (∀ᵐ t ∂(volume.restrict (Ioo 0 1)),
      ∀ z : H10Ω d Ω, w' t z + formΩ d Ω 𝔟 t (w t) z = ofL2Ω d Ω (F t) z) ∧
    ∃ w₀ : ℝ → Hm1Ω d Ω, ContinuousOn w₀ (Icc 0 1) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo 0 1)), w₀ t = ofH10Ω d Ω (w t)) ∧ w₀ 0 = 0


/-- **Theorem 1.1 of Niebel, arXiv:2608.11194v2 (counterexample on an interval).**  Let `δ > 0`,
`H = L²((0,π);ℂ)`, `V = H¹₀((0,π);ℂ)`, `V' = H⁻¹((0,π);ℂ)`.  There are a bounded, uniformly
elliptic, real coefficient `𝔞` with `𝔞 ∈ C^{0,1/2}([0,1];L^∞(0,π))` and
`‖𝔞 - 1‖_{C^{0,1/2}([0,1];L^∞(0,π))} < δ`, but `𝔞 ∉ C^{0,α}([0,1];L^∞(0,π))` for every
`1/2 < α < 1`, a real forcing `f ∈ C([0,1];H) ∩ L²(0,1;H)` and a real function
`u ∈ C([0,1];V) ∩ C¹([0,1];V') ∩ W^{1,1}(0,1;H)` (with derivative `u'`) such that `u(0) = 0`,
`u'(t) + 𝒜(t)u(t) = f(t)` in `V'` for every `t ∈ [0,1]`, and `u` is the unique Lions variational
solution; moreover `u(t) ∈ D(A_H(t))` for every `t ∈ [0,1]`,
`A_H(·)u(·) ∈ L¹(0,1;H) ∖ L²(0,1;H)`, and `∂ₜu ∉ L²(0,1;H)`.

Reading of the clauses.  The `C^{0,1/2}` norm is
`sup_t ‖g(t)‖ + sup_{s≠t} ‖g(t) - g(s)‖/|t-s|^{1/2}`, so `‖𝔞 - 1‖ < δ` is the existence of bounds
`A ≥ 0` for the first and `B ≥ 0` for the second supremum with `A + B < δ`; `L^∞(0,π)` norms are
`eLpNorm · ∞` on `(0,π)`.  `𝒜(t)` acts through the form `form`; `D(A_H(t))` is the set of
`v ∈ V` with `𝒜(t)v ∈ H`.  "`A_H(·)u(·) ∉ L²`" is asserted of every `g` with
`𝒜(t)u(t) = g(t)` for all `t`, and "`∂ₜu ∉ L²(0,1;H)`" says that no `g ∈ L²(0,1;H)` represents
`u'` almost everywhere.  Real-valuedness of an element of `L²` is the vanishing of its imaginary
part almost everywhere. -/
theorem lions_counterexample_interval (δ : ℝ) (hδ : 0 < δ) :
    ∃ (𝔞 : ℝ → ℝ → ℝ) (f : ℝ → L2 (Ioo 0 Real.pi)) (u : ℝ → H10 (Ioo 0 Real.pi))
      (u' : ℝ → Hm1 (Ioo 0 Real.pi)),
      Measurable (Function.uncurry 𝔞) ∧
      (∃ lam Λ : ℝ, 0 < lam ∧ ∀ t x, lam ≤ 𝔞 t x ∧ 𝔞 t x ≤ Λ) ∧
      (∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ A + B < δ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, eLpNorm (fun x => 𝔞 t x - 1) ∞ (volume.restrict (Ioo 0 Real.pi))
          ≤ ENNReal.ofReal A) ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          eLpNorm (fun x => 𝔞 t x - 𝔞 s x) ∞ (volume.restrict (Ioo 0 Real.pi))
            ≤ ENNReal.ofReal (B * |t - s| ^ (1 / 2 : ℝ))) ∧
      (∀ α : ℝ, 1 / 2 < α → α < 1 → ¬ ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          eLpNorm (fun x => 𝔞 t x - 𝔞 s x) ∞ (volume.restrict (Ioo 0 Real.pi))
            ≤ ENNReal.ofReal (C * |t - s| ^ α)) ∧
      ContinuousOn f (Icc 0 1) ∧ MemLp f 2 (volume.restrict (Ioo 0 1)) ∧
      (∀ t, ∀ᵐ x ∂(volume.restrict (Ioo 0 Real.pi)), (f t x).im = 0) ∧
      ContinuousOn u (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun s => ofH10 (Ioo 0 Real.pi) (u s)) (u' t) (Icc 0 1) t) ∧
      ContinuousOn u' (Icc 0 1) ∧
      IntegrableOn (fun t => val (Ioo 0 Real.pi) (u t)) (Ioo 0 1) ∧
      (∃ g : ℝ → L2 (Ioo 0 Real.pi), IntegrableOn g (Ioo 0 1) ∧
        HasWeakDeriv (fun t => val (Ioo 0 Real.pi) (u t)) g) ∧
      (∀ t, ∀ᵐ x ∂(volume.restrict (Ioo 0 Real.pi)), (val (Ioo 0 Real.pi) (u t) x).im = 0) ∧
      u 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ w : H10 (Ioo 0 Real.pi),
        u' t w + form (Ioo 0 Real.pi) 𝔞 t (u t) w = ofL2 (Ioo 0 Real.pi) (f t) w) ∧
      IsLionsSolution (Ioo 0 Real.pi) 𝔞 f u ∧
      (∀ w : ℝ → H10 (Ioo 0 Real.pi), IsLionsSolution (Ioo 0 Real.pi) 𝔞 f w →
        ∀ᵐ t ∂(volume.restrict (Ioo 0 1)), w t = u t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∃ h : L2 (Ioo 0 Real.pi), ∀ w : H10 (Ioo 0 Real.pi),
        form (Ioo 0 Real.pi) 𝔞 t (u t) w = ofL2 (Ioo 0 Real.pi) h w) ∧
      (∀ g : ℝ → L2 (Ioo 0 Real.pi), (∀ t ∈ Icc (0 : ℝ) 1, ∀ w : H10 (Ioo 0 Real.pi),
          form (Ioo 0 Real.pi) 𝔞 t (u t) w = ofL2 (Ioo 0 Real.pi) (g t) w) →
        IntegrableOn g (Ioo 0 1) ∧ ¬ MemLp g 2 (volume.restrict (Ioo 0 1))) ∧
      ¬ ∃ g : ℝ → L2 (Ioo 0 Real.pi), MemLp g 2 (volume.restrict (Ioo 0 1)) ∧
        ∀ᵐ t ∂(volume.restrict (Ioo 0 1)), u' t = ofL2 (Ioo 0 Real.pi) (g t) := by
  sorry

/-- **Corollary 1.2 of Niebel, arXiv:2608.11194v2 (counterexamples on arbitrary bounded
domains).**  Let `d ≥ 1`, `Ω ⊆ ℝ^d` a bounded nonempty open set, `δ > 0`,
`H_Ω = L²(Ω;ℂ)`, `V_Ω = H¹₀(Ω;ℂ)`, `V_Ω' = H⁻¹(Ω;ℂ)`.  There is a bounded real scalar
coefficient `𝔟` such that the isotropic matrix `𝔅 = 𝔟 Id_d` (`isoCoeff 𝔟`) is real symmetric
and uniformly elliptic, `𝔅 ∈ C^{0,1/2}([0,1];L^∞(Ω;ℝ^{d×d}))` with
`‖𝔅 - Id_d‖_{C^{0,1/2}} < δ`, and `𝔅 ∉ C^{0,α}([0,1];L^∞(Ω;ℝ^{d×d}))` for `1/2 < α < 1`; and
there are a real forcing `F ∈ C([0,1];H_Ω) ∩ L²(0,1;H_Ω)` and a real function
`U ∈ C([0,1];V_Ω) ∩ C¹([0,1];V_Ω') ∩ W^{1,1}(0,1;H_Ω)` such that `U(0) = 0`,
`U'(t) - div(𝔅(t)∇U(t)) = F(t)` in `V_Ω'` for every `t ∈ [0,1]`, `U` is the unique Lions
variational solution (in particular `U ∈ L²(0,1;V_Ω) ∩ H¹(0,1;V_Ω')`), but
`U' ∉ L²(0,1;H_Ω)` and `-div(𝔅∇U) ∉ L²(0,1;H_Ω)`.

The matrix norm is the operator norm of `ℝ^d`; the clauses are read as in
`lions_counterexample_interval`.  The domain is not required to be connected. -/
theorem lions_counterexample_domain (d : ℕ) (hd : 1 ≤ d) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (𝔟 : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (F : ℝ → L2Ω d Ω) (U : ℝ → H10Ω d Ω)
      (U' : ℝ → Hm1Ω d Ω),
      Measurable (Function.uncurry 𝔟) ∧
      (∃ lam Λ : ℝ, 0 < lam ∧ ∀ t x, lam ≤ 𝔟 t x ∧ 𝔟 t x ≤ Λ) ∧
      (∀ t x, IsSelfAdjoint (isoCoeff 𝔟 t x)) ∧
      (∃ lam : ℝ, 0 < lam ∧ ∀ t x (ξ : EuclideanSpace ℝ (Fin d)),
        lam * ‖ξ‖ ^ 2 ≤ ⟪isoCoeff 𝔟 t x ξ, ξ⟫_ℝ) ∧
      (∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ A + B < δ ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          eLpNorm (fun x => isoCoeff 𝔟 t x - ContinuousLinearMap.id ℝ _) ∞ (volume.restrict Ω)
            ≤ ENNReal.ofReal A) ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          eLpNorm (fun x => isoCoeff 𝔟 t x - isoCoeff 𝔟 s x) ∞ (volume.restrict Ω)
            ≤ ENNReal.ofReal (B * |t - s| ^ (1 / 2 : ℝ))) ∧
      (∀ α : ℝ, 1 / 2 < α → α < 1 → ¬ ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          eLpNorm (fun x => isoCoeff 𝔟 t x - isoCoeff 𝔟 s x) ∞ (volume.restrict Ω)
            ≤ ENNReal.ofReal (C * |t - s| ^ α)) ∧
      ContinuousOn F (Icc 0 1) ∧ MemLp F 2 (volume.restrict (Ioo 0 1)) ∧
      (∀ t, ∀ᵐ x ∂(volume.restrict Ω), (F t x).im = 0) ∧
      ContinuousOn U (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s => ofH10Ω d Ω (U s)) (U' t) (Icc 0 1) t) ∧
      ContinuousOn U' (Icc 0 1) ∧
      IntegrableOn (fun t => valΩ d Ω (U t)) (Ioo 0 1) ∧
      (∃ g : ℝ → L2Ω d Ω, IntegrableOn g (Ioo 0 1) ∧
        HasWeakDeriv (fun t => valΩ d Ω (U t)) g) ∧
      (∀ t, ∀ᵐ x ∂(volume.restrict Ω), (valΩ d Ω (U t) x).im = 0) ∧
      U 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ w : H10Ω d Ω,
        U' t w + formΩ d Ω 𝔟 t (U t) w = ofL2Ω d Ω (F t) w) ∧
      IsLionsSolutionΩ d Ω 𝔟 F U ∧
      (∀ W : ℝ → H10Ω d Ω, IsLionsSolutionΩ d Ω 𝔟 F W →
        ∀ᵐ t ∂(volume.restrict (Ioo 0 1)), W t = U t) ∧
      (¬ ∃ g : ℝ → L2Ω d Ω, MemLp g 2 (volume.restrict (Ioo 0 1)) ∧
        ∀ᵐ t ∂(volume.restrict (Ioo 0 1)), U' t = ofL2Ω d Ω (g t)) ∧
      ¬ ∃ g : ℝ → L2Ω d Ω, MemLp g 2 (volume.restrict (Ioo 0 1)) ∧
        ∀ᵐ t ∂(volume.restrict (Ioo 0 1)), ∀ w : H10Ω d Ω,
          formΩ d Ω 𝔟 t (U t) w = ofL2Ω d Ω (g t) w := by
  sorry

end LionsC12Challenge
