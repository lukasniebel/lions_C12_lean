module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Lions' maximal regularity problem: the ½-Hölder counterexample

This file collects the *definitions* of the objects appearing in

> L. Niebel, *Lions' Maximal Regularity Problem for Divergence-Form Differential
> Operators: Failure at the ½-Hölder Endpoint* (2026).

Everything is formalised concretely: functions are real-valued functions of the
time variable `t : ℝ` and the space variable `x : ℝ`, spatial derivatives are
classical derivatives, and `L²(0,π)`-quantities are interval integrals over `0..π`.

## Conventions

* Block indices `j : ℕ` with `j ≥ 1` and mode indices `m` with `1 ≤ m ≤ M j = j`.
  For `j = 0` all block quantities vanish (by the Lean conventions `1/0 = 0` and
  `Finset.Icc 1 0 = ∅`), so sums over all `j : ℕ` agree with the sums over `j ≥ 1`
  in the paper.
* The infinite sums over blocks are *pointwise finite* (at each time at most one
  block is active).  They are formalised with `finsum` (`∑ᶠ`), which needs no
  summability hypotheses and equals the finite sum over the support.
* The cutoff functions `η` and `ρ` of the paper are fixed once and for all.  We
  record the properties actually used in the proofs in the structure `Cutoffs`
  (see its docstring).  Existence of such cutoffs is a separate statement.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open Real

/-! ## Spatial oscillatory modes (Section 2 of the paper) -/

/-- The profile `φ(x) = sin² x`. -/
def φ (x : ℝ) : ℝ := sin x ^ 2

/-- `φ'(x) = sin (2x)`. -/
def φ' (x : ℝ) : ℝ := sin (2 * x)

/-- `φ''(x) = 2 cos (2x)`. -/
def φ'' (x : ℝ) : ℝ := 2 * cos (2 * x)

/-- The oscillatory mode `p_K(x) = sin(Kx) sin(2x)`. -/
def p (K : ℕ) (x : ℝ) : ℝ := sin (K * x) * sin (2 * x)

/-- The companion mode `c_K(x) = cos(Kx) cos(2x)`. -/
def c (K : ℕ) (x : ℝ) : ℝ := cos (K * x) * cos (2 * x)

/-- `p_K'(x) = K cos(Kx) sin(2x) + 2 sin(Kx) cos(2x)`. -/
def p' (K : ℕ) (x : ℝ) : ℝ := K * cos (K * x) * sin (2 * x) + 2 * sin (K * x) * cos (2 * x)

/-- `p_K''(x) = -(K²+4) p_K(x) + 4K c_K(x)`, i.e. `A_{0,H} p_K = (K²+4) p_K - 4K c_K`
(equation (2.6) of the paper). -/
def p'' (K : ℕ) (x : ℝ) : ℝ := -((K : ℝ) ^ 2 + 4) * p K x + 4 * K * c K x

/-- The real `L²(0,π)` inner product `∫₀^π g h dx`. -/
def inner (g h : ℝ → ℝ) : ℝ := ∫ x in (0 : ℝ)..π, g x * h x

/-- The squared `L²(0,π)`-norm `∫₀^π g² dx`. -/
def normSq (g : ℝ → ℝ) : ℝ := ∫ x in (0 : ℝ)..π, g x ^ 2

/-! ## Time blocks and lacunary frequencies (Section 3 of the paper) -/

/-- `τ_j = 5/16 - 1/(16 j)`. -/
def τ (j : ℕ) : ℝ := 5 / 16 - 1 / (16 * j)

/-- `ℓ_j = 1/(16 j (j+1))`, the length of the `j`-th block `I_j = (τ_j, τ_{j+1})`. -/
def ℓ (j : ℕ) : ℝ := 1 / (16 * j * (j + 1))

/-- `M_j = j`, the number of active modes on block `j`. -/
def M (j : ℕ) : ℕ := j

/-- The integer frequencies `K_{j,m} = 16^m ℓ_j⁻¹ = 16^{m+1} j (j+1)`. -/
def K (j m : ℕ) : ℕ := 16 ^ (m + 1) * j * (j + 1)

/-- The phase `θ_{j,m}(t) = K_{j,m}² (t - τ_j)`. -/
def θ (j m : ℕ) (t : ℝ) : ℝ := (K j m : ℝ) ^ 2 * (t - τ j)

/-- The open block `I_j = (τ_j, τ_{j+1})`. -/
def I (j : ℕ) : Set ℝ := Set.Ioo (τ j) (τ (j + 1))

/-- The middle third `J_j = [τ_j + ℓ_j/3, τ_j + 2ℓ_j/3]` of the block `I_j`. -/
def J (j : ℕ) : Set ℝ := Set.Icc (τ j + ℓ j / 3) (τ j + 2 * ℓ j / 3)

/-- `S_j = ∑_{m=1}^{M_j} K_{j,m}⁻¹`. -/
def S (j : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹

/-! ## The cutoff functions -/

/-- The data of the two cutoff functions `η, ρ ∈ C_c^∞(0,1)` used in the paper, together
with derivatives `η', ρ'` and the properties used in the proofs:

* `η` takes values in `[0,1]`, is supported in `(1/10, 9/10)` and equals `1` on `[1/3, 2/3]`;
* `ρ` takes values in `[0,1]`, is supported in `(1/8, 7/8)` and equals `1` on `[1/4, 1/2]`;
* both are continuously differentiable with bounded derivatives.

Only `C¹`-regularity is needed.  The derivative fields are recorded explicitly to avoid
one-sided derivative arguments at the boundary of the supports. -/
structure Cutoffs where
  /-- The cutoff `η`, supported in `(1/10, 9/10)` and equal to `1` on `[1/3, 2/3]`. -/
  η : ℝ → ℝ
  /-- The derivative `η'` of `η`. -/
  η' : ℝ → ℝ
  η_hasDerivAt : ∀ t, HasDerivAt η (η' t) t
  η'_continuous : Continuous η'
  η_nonneg : ∀ t, 0 ≤ η t
  η_le_one : ∀ t, η t ≤ 1
  η_supp : ∀ t, η t ≠ 0 → t ∈ Set.Ioo (1 / 10 : ℝ) (9 / 10)
  η'_supp : ∀ t, η' t ≠ 0 → t ∈ Set.Ioo (1 / 10 : ℝ) (9 / 10)
  η_one : ∀ t ∈ Set.Icc (1 / 3 : ℝ) (2 / 3), η t = 1
  η'_zero : ∀ t ∈ Set.Icc (1 / 3 : ℝ) (2 / 3), η' t = 0
  /-- A bound for `|η'|`. -/
  Cη : ℝ
  Cη_nonneg : 0 ≤ Cη
  η'_bound : ∀ t, |η' t| ≤ Cη
  /-- The cutoff `ρ`, supported in `(1/8, 7/8)` and equal to `1` on `[1/4, 1/2]`. -/
  ρ : ℝ → ℝ
  /-- The derivative `ρ'` of `ρ`. -/
  ρ' : ℝ → ℝ
  ρ_hasDerivAt : ∀ t, HasDerivAt ρ (ρ' t) t
  ρ'_continuous : Continuous ρ'
  ρ_nonneg : ∀ t, 0 ≤ ρ t
  ρ_le_one : ∀ t, ρ t ≤ 1
  ρ_supp : ∀ t, ρ t ≠ 0 → t ∈ Set.Ioo (1 / 8 : ℝ) (7 / 8)
  ρ'_supp : ∀ t, ρ' t ≠ 0 → t ∈ Set.Ioo (1 / 8 : ℝ) (7 / 8)
  ρ_one : ∀ t ∈ Set.Icc (1 / 4 : ℝ) (1 / 2), ρ t = 1
  ρ'_zero : ∀ t ∈ Set.Icc (1 / 4 : ℝ) (1 / 2), ρ' t = 0
  /-- A bound for `|ρ'|`. -/
  Cρ : ℝ
  Cρ_nonneg : 0 ≤ Cρ
  ρ'_bound : ∀ t, |ρ' t| ≤ Cρ

variable (D : Cutoffs)

/-- The rescaled cutoff `η_j(t) = η((t - τ_j)/ℓ_j)`. -/
def ηj (j : ℕ) (t : ℝ) : ℝ := D.η ((t - τ j) / ℓ j)

/-- The derivative `η_j'(t) = η'((t - τ_j)/ℓ_j) / ℓ_j` of `η_j`. -/
def ηj' (j : ℕ) (t : ℝ) : ℝ := D.η' ((t - τ j) / ℓ j) / ℓ j

/-! ## The coefficient (equations (3.5), (3.6) of the paper) -/

/-- One mode of the perturbation: `η_j(t) K_{j,m}⁻¹ sin θ_{j,m}(t) cos(K_{j,m} x)`. -/
def βmode (j m : ℕ) (t x : ℝ) : ℝ :=
  ηj D j t * ((K j m : ℝ))⁻¹ * sin (θ j m t) * cos (K j m * x)

/-- The `j`-th block `β_j` of the perturbation (zero outside `I_j` in time). -/
def βblock (j : ℕ) (t x : ℝ) : ℝ := ∑ m ∈ Finset.Icc 1 (M j), βmode D j m t x

/-- The perturbation `β(t,x) = ∑_j β_j(t,x)`; at each time at most one block is nonzero. -/
def β (t x : ℝ) : ℝ := ∑ᶠ j, βblock D j t x

/-- The spatial derivative `∂_x β_j` of the block `β_j`:
`∂_x (K⁻¹ cos(Kx)) = -sin(Kx)`. -/
def βxblock (j : ℕ) (t x : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (M j), -(ηj D j t * sin (θ j m t) * sin (K j m * x))

/-- The spatial derivative `∂_x β`. -/
def βx (t x : ℝ) : ℝ := ∑ᶠ j, βxblock D j t x

/-- The diffusion coefficient `𝔞(t,x) = 1 + ε β(t,x)`. -/
def a (ε : ℝ) (t x : ℝ) : ℝ := 1 + ε * β D t x

/-! ## The candidate solution (Section 4 of the paper) -/

/-- `y_{j,m}(t) = -(ε/(2K²)) η_j(t) (sin θ_{j,m}(t) - cos θ_{j,m}(t))`, equation (4.1). -/
def y (ε : ℝ) (j m : ℕ) (t : ℝ) : ℝ :=
  -(ε / (2 * (K j m : ℝ) ^ 2)) * ηj D j t * (sin (θ j m t) - cos (θ j m t))

/-- The time derivative `y_{j,m}'` of `y_{j,m}`. -/
def y' (ε : ℝ) (j m : ℕ) (t : ℝ) : ℝ :=
  -(ε / (2 * (K j m : ℝ) ^ 2)) *
    (ηj' D j t * (sin (θ j m t) - cos (θ j m t)) +
      ηj D j t * (K j m : ℝ) ^ 2 * (cos (θ j m t) + sin (θ j m t)))

/-- The remainder `r_{j,m} = -(ε/(2K²)) η_j' (sin θ - cos θ)`, equation (4.3). -/
def r (ε : ℝ) (j m : ℕ) (t : ℝ) : ℝ :=
  -(ε / (2 * (K j m : ℝ) ^ 2)) * ηj' D j t * (sin (θ j m t) - cos (θ j m t))

/-- The `j`-th block `v_j = ∑_m y_{j,m} p_{K_{j,m}}` of the oscillatory part. -/
def vblock (ε : ℝ) (j : ℕ) (t x : ℝ) : ℝ := ∑ m ∈ Finset.Icc 1 (M j), y D ε j m t * p (K j m) x

/-- The oscillatory part `v = ∑_j v_j`. -/
def v (ε : ℝ) (t x : ℝ) : ℝ := ∑ᶠ j, vblock D ε j t x

/-- Time derivative of the block `v_j`. -/
def vtblock (ε : ℝ) (j : ℕ) (t x : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (M j), y' D ε j m t * p (K j m) x

/-- Time derivative `∂_t v`. -/
def vt (ε : ℝ) (t x : ℝ) : ℝ := ∑ᶠ j, vtblock D ε j t x

/-- Spatial derivative of the block `v_j`. -/
def vxblock (ε : ℝ) (j : ℕ) (t x : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (M j), y D ε j m t * p' (K j m) x

/-- Spatial derivative `∂_x v`. -/
def vx (ε : ℝ) (t x : ℝ) : ℝ := ∑ᶠ j, vxblock D ε j t x

/-- Second spatial derivative of the block `v_j`. -/
def vxxblock (ε : ℝ) (j : ℕ) (t x : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (M j), y D ε j m t * p'' (K j m) x

/-- Second spatial derivative `∂_x² v`. -/
def vxx (ε : ℝ) (t x : ℝ) : ℝ := ∑ᶠ j, vxxblock D ε j t x

/-- The candidate solution `u(t,x) = ρ(t) φ(x) + v(t,x)`, equation (4.4). -/
def u (ε : ℝ) (t x : ℝ) : ℝ := D.ρ t * φ x + v D ε t x

/-- `∂_t u = ρ' φ + ∂_t v`. -/
def ut (ε : ℝ) (t x : ℝ) : ℝ := D.ρ' t * φ x + vt D ε t x

/-- `∂_x u = ρ φ' + ∂_x v`. -/
def ux (ε : ℝ) (t x : ℝ) : ℝ := D.ρ t * φ' x + vx D ε t x

/-- `∂_x² u = ρ φ'' + ∂_x² v`. -/
def uxx (ε : ℝ) (t x : ℝ) : ℝ := D.ρ t * φ'' x + vxx D ε t x

/-- The realisation of the divergence-form operator on the candidate solution:
`(𝒜(t)u)(t,x) = -∂_x(𝔞 ∂_x u) = -(∂_x 𝔞)(∂_x u) - 𝔞 ∂_x² u`, with `∂_x 𝔞 = ε ∂_x β`. -/
def Au (ε : ℝ) (t x : ℝ) : ℝ := -(ε * βx D t x * ux D ε t x) - a D ε t x * uxx D ε t x

/-- The squared `H = L²(0,π)`-norm of `∂_t u(t)`, i.e. `t ↦ ‖∂_t u(t)‖_H²`. -/
def utNormSq (ε : ℝ) (t : ℝ) : ℝ := normSq (ut D ε t)

/-! ## The forcing (Section 5 of the paper) -/

/-- `f_0(t) = ρ'(t) φ + ρ(t) A_{0,H} φ`, with `A_{0,H} φ = -φ'' = -2 cos(2x)`. -/
def f0 (t x : ℝ) : ℝ := D.ρ' t * φ x - D.ρ t * φ'' x

/-- The mode remainder `E_{j,m} = (r_{j,m} + 4 y_{j,m}) p_K - 2 ε η_j K⁻¹ cos θ_{j,m} c_K`,
equation (5.1). -/
def E (ε : ℝ) (j m : ℕ) (t x : ℝ) : ℝ :=
  (r D ε j m t + 4 * y D ε j m t) * p (K j m) x
    - 2 * ε * ηj D j t * ((K j m : ℝ))⁻¹ * cos (θ j m t) * c (K j m) x

/-- The block remainder `R_j = ∑_m E_{j,m}`. -/
def Rblock (ε : ℝ) (j : ℕ) (t x : ℝ) : ℝ := ∑ m ∈ Finset.Icc 1 (M j), E D ε j m t x

/-- The remainder `R = ∑_j R_j`. -/
def R (ε : ℝ) (t x : ℝ) : ℝ := ∑ᶠ j, Rblock D ε j t x

/-- `L_β v = -∂_x(β ∂_x v) = -(∂_x β)(∂_x v) - β ∂_x² v`. -/
def Lβv (ε : ℝ) (t x : ℝ) : ℝ := -(βx D t x * vx D ε t x) - β D t x * vxx D ε t x

/-- The forcing `f = f_0 + R + ε L_β v`, cf. equation (5.3) of the paper.  The main
identity `∂_t u + 𝒜(t) u = f` is proved in `LionsC12.Forcing.Cancellation`. -/
def f (ε : ℝ) (t x : ℝ) : ℝ := f0 D t x + R D ε t x + ε * Lβv D ε t x

end LionsC12

end
