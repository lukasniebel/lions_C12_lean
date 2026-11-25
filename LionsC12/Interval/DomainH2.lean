module

public import LionsC12.Spaces.Sobolev
public import LionsC12.Interval.FrozenDomain

/-!
# `D(A_{0,H}) = H²(0,π) ∩ H¹₀(0,π)`: Proposition 3.4 with the paper's `D₀`

`LionsC12.Interval.FrozenDomain` defines `D₀ = D(A_{0,H})` as the domain of the realisation in
`H = L²((0,π);ℂ)` of the form of the constant coefficient `1` (`IsRealisation one 0`), and proves
`D(A_H(t)) = D₀` (`domain_eq`).  This file identifies `D₀` with `H²(0,π) ∩ H¹₀(0,π)`, the
Sobolev space of the weak derivatives (`LionsC12.Spaces.Sobolev`):

* `MemH2 U v` — `v ∈ H²(U)`: `v` has weak derivatives `v', v'' ∈ L²(U)`; for `v ∈ H¹₀(U)`,
  `U` open, `v' = ∂ₓv` (`memH2_val_iff`);
* `forall_inner_dx_iff` — on an open `U ⊆ ℝ`: `⟨∂ₓv, ∂ₓw⟩ = ⟨h, w⟩` for all `w ∈ H¹₀(U)` iff
  `-h` is the weak derivative of `∂ₓv`;
* `isRealisation_one_iff` — `A_{0,H}v = h` iff `∂ₓv` has the weak derivative `-h`, that is
  `A_{0,H} = -∂ₓ²` on its domain;
* `domain_one_eq_H2` — `D(A_{0,H}) = H²(0,π) ∩ H¹₀(0,π)`;
* `domain_eq_H2` — Proposition 3.4, first part: `D(A_H(t)) = H²(0,π) ∩ H¹₀(0,π)` for every `t`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set LionsC12Challenge
open scoped InnerProductSpace

variable {U : Set ℝ}

/-- `v ∈ H²(U)`: `v ∈ L²(U)` has a weak derivative `v' ∈ L²(U)`, which has a weak derivative
`v'' ∈ L²(U)`. -/
def MemH2 (U : Set ℝ) (v : L2 U) : Prop :=
  ∃ v' v'' : L2 U, HasWeakDerivL2 U v v' ∧ HasWeakDerivL2 U v' v''

/-- `v ∈ H¹₀(U)` lies in `H²(U)` iff `∂ₓv` has a weak derivative in `L²(U)`, `U` open. -/
theorem memH2_val_iff (hU : IsOpen U) (v : H10 U) :
    MemH2 U (val U v) ↔ ∃ g, HasWeakDerivL2 U (dx U v) g := by
  constructor
  · rintro ⟨v', v'', h1, h2⟩
    rw [hasWeakDerivL2_unique hU h1 (hasWeakDerivL2_dx v)] at h2
    exact ⟨v'', h2⟩
  · rintro ⟨g, hg⟩
    exact ⟨dx U v, g, hasWeakDerivL2_dx v, hg⟩

/-- On an open `U ⊆ ℝ`: `⟨∂ₓw, ∂ₓv⟩ = ⟨w, h⟩` for every `w ∈ H¹₀(U)` iff `-h` is the weak
derivative of `∂ₓv`. -/
theorem forall_inner_dx_iff (hU : IsOpen U) (v : H10 U) (h : L2 U) :
    (∀ w : H10 U, ⟪dx U w, dx U v⟫_ℂ = ⟪val U w, h⟫_ℂ) ↔ HasWeakDerivL2 U (dx U v) (-h) := by
  rw [hasWeakDerivL2_iff_forall_H10 hU]
  simp only [inner_neg_right, neg_neg]

/-- **`A_{0,H} = -∂ₓ²`**: `v ∈ H¹₀((0,π))` lies in `D(A_{0,H})` with `A_{0,H}v = h` iff `-h` is the
weak derivative of `∂ₓv`. -/
theorem isRealisation_one_iff (v : H10 Iπ) (h : L2 Iπ) :
    IsRealisation one 0 v h ↔ HasWeakDerivL2 Iπ (dx Iπ v) (-h) := by
  rw [← forall_inner_dx_iff isOpen_Ioo]
  refine forall_congr' fun w => ?_
  rw [formH_one_eq]
  rfl

/-- **`D₀ = D(A_{0,H}) = H²(0,π) ∩ H¹₀(0,π)`.** -/
theorem domain_one_eq_H2 (v : H10 Iπ) :
    (∃ h, IsRealisation one 0 v h) ↔ MemH2 Iπ (val Iπ v) := by
  rw [memH2_val_iff isOpen_Ioo]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨-h, (isRealisation_one_iff v h).1 hh⟩
  · rintro ⟨g, hg⟩
    refine ⟨-g, (isRealisation_one_iff v (-g)).2 ?_⟩
    rwa [neg_neg]

/-- **Proposition 3.4, first part**, with the paper's `D₀ = H²(0,π) ∩ H¹₀(0,π)`:
`D(A_H(t)) = H²(0,π) ∩ H¹₀(0,π)` for every `t`. -/
theorem domain_eq_H2 (D : Cutoffs) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : ℝ) (v : H10 Iπ) :
    (∃ h, IsRealisation (a D ε) t v h) ↔ MemH2 Iπ (val Iπ v) :=
  (domain_eq D hε0 hε1 t v).trans (domain_one_eq_H2 v)

end LionsC12
