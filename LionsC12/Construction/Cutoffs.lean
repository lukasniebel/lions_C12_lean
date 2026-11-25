module

public import LionsC12.Construction.Defs
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Existence of the cutoff data

This file proves `Cutoffs.nonempty : Nonempty Cutoffs`, i.e. that the structure `Cutoffs` of
`LionsC12.Construction.Defs` (recording the two cutoffs `η`, `ρ` and their properties) is inhabited.

Both cutoffs are built from Mathlib's smooth bump functions `ContDiffBump` on `ℝ` (available
since `ℝ` is an inner product space over itself), centered at `1/2`:

* `η` comes from radii `rIn = 1/5`, `rOut = 3/8`: it is `1` on `closedBall (1/2) (1/5) ⊇ [1/3,2/3]`
  and supported in `ball (1/2) (3/8) = (1/8,7/8) ⊆ (1/10,9/10)`.
* `ρ` comes from radii `rIn = 27/100`, `rOut = 3/10`: it is `1` on
  `closedBall (1/2) (27/100) ⊇ [1/4,1/2]` and supported in
  `ball (1/2) (3/10) = (1/5,4/5) ⊆ (1/8,7/8)`.

  (The paper's suggested radius `rIn = 1/4` for `ρ` would put the endpoint `1/4` of the required
  plateau `[1/4,1/2]` exactly on the boundary of the inner ball, where the "locally constant near a
  point of the open ball" argument for `ρ' = 0` does not directly apply; we use
  `27/100 ∈ (1/4,3/10)` instead so that `[1/4,1/2]` is compactly contained in the *open* inner
  ball.)

The auxiliary lemma `exists_cutoff` packages the whole construction (smoothness, derivative,
bounds `[0,1]`, support, plateau, derivative bound) generically in terms of the center, the two
radii, and the two target intervals, and is instantiated twice.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open Real Set Metric Function

variable (D : Cutoffs)

/-- Generic construction of one cutoff function from a `ContDiffBump` centered at `c` with
`0 < rIn < rOut`, provided:

* the plateau `Icc a b` is compactly contained in the open inner ball `ball c rIn`
  (this gives both `g = 1` and `g' = 0` on `Icc a b`);
* the closed outer ball `closedBall c rOut` is contained in `Ioo lo hi`
  (this gives the support conditions for `g` and `g'`).

The output bundles exactly the fields needed for one half (`η` or `ρ`) of `Cutoffs`. -/
theorem exists_cutoff (c rIn rOut lo hi a b : ℝ) (hrIn : 0 < rIn) (hlt : rIn < rOut)
    (hone : c - rIn < a) (hone' : b < c + rIn) (hsupp : lo < c - rOut) (hsupp' : c + rOut < hi) :
    ∃ g g' : ℝ → ℝ,
      (∀ t, HasDerivAt g (g' t) t) ∧
      Continuous g' ∧
      (∀ t, 0 ≤ g t) ∧
      (∀ t, g t ≤ 1) ∧
      (∀ t, g t ≠ 0 → t ∈ Ioo lo hi) ∧
      (∀ t, g' t ≠ 0 → t ∈ Ioo lo hi) ∧
      (∀ t ∈ Icc a b, g t = 1) ∧
      (∀ t ∈ Icc a b, g' t = 0) ∧
      ∃ C, 0 ≤ C ∧ ∀ t, |g' t| ≤ C := by
  let f : ContDiffBump c := ⟨rIn, rOut, hrIn, hlt⟩
  -- The two set inclusions we need, phrased via `Real.ball_eq_Ioo` / `Real.closedBall_eq_Icc`.
  have houter : closedBall c rOut ⊆ Ioo lo hi := by
    rw [Real.closedBall_eq_Icc]
    exact Icc_subset_Ioo hsupp hsupp'
  have hinner : Icc a b ⊆ closedBall c rIn := by
    rw [Real.closedBall_eq_Icc]
    exact Icc_subset_Icc hone.le hone'.le
  have hinner' : Icc a b ⊆ ball c rIn := by
    rw [Real.ball_eq_Ioo]
    exact Icc_subset_Ioo hone hone'
  -- `f` is (at least) `C¹`.
  have hC1 : ContDiff ℝ 1 (f : ℝ → ℝ) := f.contDiff
  refine ⟨(f : ℝ → ℝ), deriv (f : ℝ → ℝ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `HasDerivAt`
    intro t
    exact (hC1.differentiable_one.differentiableAt).hasDerivAt
  · -- continuity of the derivative
    exact hC1.continuous_deriv_one
  · -- nonnegativity
    intro t; exact f.nonneg' t
  · -- `≤ 1`
    intro t; exact f.le_one
  · -- support of `f`
    intro t ht
    have hmem : t ∈ Function.support (f : ℝ → ℝ) := Function.mem_support.mpr ht
    rw [f.support_eq] at hmem
    exact houter (ball_subset_closedBall hmem)
  · -- support of `deriv f`
    intro t ht
    have hmem : t ∈ Function.support (deriv (f : ℝ → ℝ)) := Function.mem_support.mpr ht
    have hsub : t ∈ tsupport (f : ℝ → ℝ) := support_deriv_subset hmem
    rw [f.tsupport_eq] at hsub
    exact houter hsub
  · -- `f = 1` on the plateau
    intro t ht
    exact f.one_of_mem_closedBall (hinner ht)
  · -- `deriv f = 0` on the plateau
    intro t ht
    have heq : (f : ℝ → ℝ) =ᶠ[nhds t] (1 : ℝ → ℝ) := f.eventuallyEq_one_of_mem_ball (hinner' ht)
    simp [heq.deriv_eq]
  · -- boundedness of the derivative
    obtain ⟨C, hC⟩ :=
      hC1.continuous_deriv_one.bounded_above_of_compact_support (f.hasCompactSupport.deriv)
    refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
    rw [← Real.norm_eq_abs]
    exact (hC t).trans (le_max_left _ _)

/-- The structure `Cutoffs` is inhabited: construct `η` from a bump at `1/2` with
`rIn = 1/5`, `rOut = 3/8`, and `ρ` from a bump at `1/2` with `rIn = 27/100`, `rOut = 3/10`. -/
theorem Cutoffs.nonempty : Nonempty Cutoffs := by
  obtain ⟨η, η', hη_deriv, hη'_cont, hη_nonneg, hη_le_one, hη_supp, hη'_supp, hη_one, hη'_zero,
      Cη, hCη_nonneg, hη'_bound⟩ :=
    exists_cutoff (1 / 2) (1 / 5) (3 / 8) (1 / 10) (9 / 10) (1 / 3) (2 / 3)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨ρ, ρ', hρ_deriv, hρ'_cont, hρ_nonneg, hρ_le_one, hρ_supp, hρ'_supp, hρ_one, hρ'_zero,
      Cρ, hCρ_nonneg, hρ'_bound⟩ :=
    exists_cutoff (1 / 2) (27 / 100) (3 / 10) (1 / 8) (7 / 8) (1 / 4) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨{
    η := η
    η' := η'
    η_hasDerivAt := hη_deriv
    η'_continuous := hη'_cont
    η_nonneg := hη_nonneg
    η_le_one := hη_le_one
    η_supp := hη_supp
    η'_supp := hη'_supp
    η_one := hη_one
    η'_zero := hη'_zero
    Cη := Cη
    Cη_nonneg := hCη_nonneg
    η'_bound := hη'_bound
    ρ := ρ
    ρ' := ρ'
    ρ_hasDerivAt := hρ_deriv
    ρ'_continuous := hρ'_cont
    ρ_nonneg := hρ_nonneg
    ρ_le_one := hρ_le_one
    ρ_supp := hρ_supp
    ρ'_supp := hρ'_supp
    ρ_one := hρ_one
    ρ'_zero := hρ'_zero
    Cρ := Cρ
    Cρ_nonneg := hCρ_nonneg
    ρ'_bound := hρ'_bound }⟩

end LionsC12

end
