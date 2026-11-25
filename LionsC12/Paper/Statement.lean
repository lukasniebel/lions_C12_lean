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
# The statement layer: the function spaces of the paper

The definitions of `Challenge.lean`, repeated character for character (the release gate checks
this with `scripts/check-challenge-text.py`).  They express the objects of Theorem 1.1 and
Corollary 1.2 of L. Niebel, *Lions' maximal regularity problem for divergence-form differential
operators: failure at the ½-Hölder endpoint*, arXiv:2608.11194v2, in terms of mathlib:

* on a set `U ⊆ ℝ` (for Theorem 1.1, `U = (0,π)`): `H = L²(U;ℂ)` (`L2`), `V = H¹₀(U;ℂ)`
  (`H10`, the closure `H10Graph` of `C¹_c(U;ℂ)` in the graph norm, as a type), its anti-dual `V' = H⁻¹(U;ℂ)` (`Hm1`),
  the embeddings `H ↪ V'` (`ofL2`) and `V ↪ V'` (`ofH10`), and the form
  `𝔞(t)[v,w] = ∫_U 𝔞(t,x) ∂ₓv conj(∂ₓw)` of `𝒜(t) = -∂ₓ(𝔞(t,·)∂ₓ)` (`form`);
* on a set `Ω ⊆ ℝ^d` (for Corollary 1.2): the same with the gradient (`L2Ω`, `H10Ω`, `Hm1Ω`,
  `ofL2Ω`, `ofH10Ω`, `formΩ`) and the isotropic coefficient matrix `𝔟 Id_d` (`isoCoeff`);
* in time: the distributional derivative on `(0,1)` (`HasWeakDeriv`) and the class of Lions
  variational solutions with zero initial value (`IsLionsSolution`, `IsLionsSolutionΩ`).
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

end LionsC12Challenge
