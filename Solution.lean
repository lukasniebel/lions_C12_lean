module

public import LionsC12

/-!
# Theorem 1.1 and Corollary 1.2: the proof of the Challenge statement

The theorems `LionsC12Challenge.lions_counterexample_interval` and
`LionsC12Challenge.lions_counterexample_domain` of `Challenge.lean`, with the same statements and
docstrings, proved by `LionsC12.lions_counterexample_interval` (`LionsC12/Interval/Theorem.lean`)
and `LionsC12.lions_counterexample_domain` (`LionsC12/Domains/`).  The definitions the statements
use are those of `LionsC12/Paper/Statement.lean`, which repeats the definitions of
`Challenge.lean` character for character; `scripts/check-challenge-text.py` checks both textual
identities.
-/

@[expose] public section

noncomputable section

namespace LionsC12Challenge

open MeasureTheory Set
open scoped ENNReal InnerProductSpace ContDiff

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
        ∀ᵐ t ∂(volume.restrict (Ioo 0 1)), u' t = ofL2 (Ioo 0 Real.pi) (g t) :=
  LionsC12.lions_counterexample_interval δ hδ

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
          formΩ d Ω 𝔟 t (U t) w = ofL2Ω d Ω (g t) w :=
  LionsC12.lions_counterexample_domain d hd Ω hΩ hΩb hΩne δ hδ

end LionsC12Challenge
