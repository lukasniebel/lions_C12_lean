# Deviations of the formalisation from the paper

This document lists every respect in which the Lean statements and the Lean arguments of this
repository differ from the paper *Lions' maximal regularity problem for divergence-form
differential operators: failure at the ½-Hölder endpoint* (L. Niebel, arXiv:2608.11194v2).  The
paper is cited by its printed numbers and its LaTeX labels (`thm:main`, `eq:reciprocal-sums`,
…).  Lean names are given without the `LionsC12.` namespace prefix where this is unambiguous;
the definitions of the statement layer live in the namespace `LionsC12Challenge`.  Every file
path is relative to the repository root.

**How to read an entry.**  Each entry has an identifier (A1, B3, C3.2, …), a title and the paper
label(s) concerned, then **Paper:** what the paper states or does, **Lean:** what the
formalisation states or does, and **Effect:** one of

* **stronger** — the Lean statement implies the paper's (more clauses, weaker hypotheses, an
  explicit value where the paper asserts existence);
* **weaker** / **narrower** — the Lean statement proves less, or for a smaller class;
* **different form** — an equivalent formulation, or the same words read in a different model;
* **different route** — the same statement, proved by a different argument;
* **not formalised** — no Lean counterpart;
* **choice** — the Lean fixes something the paper leaves free.

Part A lists the conventions that affect how *every* statement is read.  Part B goes through
Theorem 1.1 and Corollary 1.2 clause by clause, in the form of the Challenge statement.  Part C
goes through Sections 2–7.  Part D lists what is not formalised.  Part E lists material of the
formalisation that the paper does not contain.  A statement of the paper with no entry here is
formalised as stated, up to the conventions of Part A.  The blueprint repeats each deviation in
a paragraph **Lean form** after the node concerned.

## Part A. Standing conventions

**A1. The Sobolev spaces** (§1, the spaces `H`, `V`, `V'`; Corollary 1.2, `H_Ω`, `V_Ω`, `V_Ω'`).
*Paper:* `V = H¹₀((0,π);ℂ)`, `V' = H⁻¹((0,π);ℂ)` the anti-dual, and the same on `Ω ⊆ ℝ^d`.
*Lean:* Mathlib has no Sobolev spaces.  `H10 U` (`LionsC12/Paper/Statement.lean`) is the closure
in `WithLp 2 (L2 U × L2 U)` of the graphs `(φ, φ')` of `φ ∈ C¹_c(ℝ;ℂ)` with `tsupport φ ⊆ U`
(Brezis' definition of `H¹₀`); `H10Ω d Ω` is the same with `(φ, ∇φ) ∈ L²(Ω;ℂ) × L²(Ω;ℂ^d)`.  The
norm is the graph norm `(‖v‖²_H + ‖∂ₓv‖²_H)^{1/2}`.  `Hm1 U = H10 U →L⋆[ℂ] ℂ` is the anti-dual
with the operator norm, and `H ↪ V'` is `h ↦ ⟨h, ·⟩_H`.  The equivalence with the definitions
through weak derivatives is formalised, for `U ⊆ ℝ` and `Ω ⊆ ℝ^d` open, in
`LionsC12/Spaces/Sobolev.lean` and `LionsC12/Domains/Sobolev.lean`, and is not used by the main
theorems: `W12Graph U` (`W12ΩGraph d Ω`) is the closed subspace of `L² × L²` of the pairs `(v, g)`
with `g` the weak derivative (gradient) of `v`, tested against real `C_c^∞` functions, that is
`W^{1,2}` with its norm; `H10Graph U ≤ W12Graph U` (`H10Graph_le_W12Graph`), and `H10Graph U` is the
closure of the graphs of the `C_c^∞(U)` functions (`H10Graph_eq_closure_smoothGraph`), so that the
isometric inclusion `H10 U ↪ W12Graph U` has for range the closure of `C_c^∞(U)` in `W^{1,2}(U)`
(`range_H10toW12`), the textbook `H¹₀(U)`; the same on `Ω` (`H10ΩGraph_le_W12ΩGraph`,
`H10ΩGraph_eq_closure_smoothGraphΩ`, `range_H10ΩtoW12Ω`).  *Effect:* different form.  `H10 U` is a
type synonym of a submodule with its instances declared explicitly, because Mathlib's instance
search for the anti-dual of a submodule does not terminate.

**A2. Bochner spaces and time regularity** (Theorem 1.1, Corollary 1.2).
*Paper:* `C([0,1];X)`, `C¹([0,1];X)`, `L^p(0,1;X)`, `W^{1,1}(0,1;H)`.
*Lean:* `ContinuousOn · (Icc 0 1)`; `C¹([0,1];V')` is a derivative `u'` continuous on `[0,1]` with
`HasDerivWithinAt · (u' t) (Icc 0 1) t` at every `t ∈ [0,1]`; `L^p(0,1;X)` is
`MemLp · p (volume.restrict (Ioo 0 1))` (Mathlib's Bochner spaces); `W^{1,1}(0,1;H)` is
integrability on `(0,1)` together with an integrable distributional derivative.  The distributional
derivative `HasWeakDeriv u g` is tested against real `φ ∈ C^∞_c(ℝ)` with `tsupport φ ⊆ (0,1)`.
*Effect:* different form.

**A3. Lions solutions** (Theorem 1.1: "the unique Lions variational solution").
*Paper:* the solution in `W(0,1) = L²(0,1;V) ∩ H¹(0,1;V')` with zero initial value, by Lions'
theorem.
*Lean:* `IsLionsSolution U 𝔞 f w`: `w ∈ L²(0,1;V)`, a `V'`-valued distributional derivative
`w' ∈ L²(0,1;V')` of `t ↦ w(t) ∈ V'`, the equation `w'(t) + 𝒜(t)w(t) = f(t)` in `V'` for almost
every `t`, and a representative `w₀`, continuous on `[0,1]` into `V'` and equal to `w` almost
everywhere, with `w₀(0) = 0`.  The paper's initial condition refers to the continuous
`H`-valued representative of `w ∈ W(0,1)`; its image in `V'` is the continuous `V'`-valued
representative, so the two conditions agree.  *Effect:* different form.

**A4. Negative clauses** (Theorem 1.1: `∂ₜu ∉ L²(0,1;H)`, `A_H(·)u(·) ∉ L²(0,1;H)`).
*Lean:* "`∂ₜu ∉ L²(0,1;H)`" is: no `g ∈ L²(0,1;H)` satisfies `u'(t) = g(t)` in `V'` for almost
every `t`.  "`A_H(·)u(·) ∉ L²`" is asserted of *every* `g` with `𝒜(t)u(t) = g(t)` in `V'` for all
`t ∈ [0,1]`.  These formulations do not depend on a choice of representative.  *Effect:* different
form.

**A5. Real-valuedness.**  *Lean:* an element of `L²(U;ℂ)` is real-valued if its imaginary part
vanishes almost everywhere; the coefficients are real functions.  *Effect:* different form.

**A6. The `C^{0,1/2}` norm** (Theorem 1.1, Corollary 1.2).
*Paper:* `‖𝔞 − 1‖_{C^{0,1/2}([0,1];L^∞)} < δ`.
*Lean:* the norm is `sup_t ‖g(t)‖ + sup_{s≠t} ‖g(t) − g(s)‖/|t − s|^{1/2}`; the clause is the
existence of bounds `A ≥ 0` for the first and `B ≥ 0` for the second supremum with `A + B < δ`.  `L^∞`
norms are `eLpNorm · ∞` with respect to `volume.restrict (Ioo 0 π)` (resp. `Ω`).  Membership in
`C^{0,α}` is the existence of a constant `C` with `‖g(t) − g(s)‖ ≤ C|t − s|^α` on `[0,1]`.
*Effect:* different form.

**A7. Coefficients.**  *Lean:* the coefficient is a function `ℝ → ℝ → ℝ` of `(t,x)`, jointly
measurable, and bounded and uniformly elliptic at *every* point.  *Effect:* stronger.

**A8. The cutoffs** (Sections 3, 4: `η`, `ρ`).  *Lean:* the two cutoffs are the fields of the
structure `Cutoffs` (`LionsC12/Construction/Defs.lean`) with the properties the proofs use; the
theorems hold for every `D : Cutoffs`, and `Cutoffs.nonempty` (`LionsC12/Construction/Cutoffs.lean`)
constructs one from Mathlib's smooth bump functions.  Theorem 1.1 uses
`Classical.choice Cutoffs.nonempty`.  *Effect:* choice.

**A9. Lions' theorem** (Theorem 1.1, Corollary 1.2: "Lions' theorem identifies `u`").
*Paper:* uniqueness by Lions' theorem, under uniform coercivity.
*Lean:* uniqueness is proved directly for every Lions solution, by realification of the complex
Gelfand triple and the Lions–Magenes energy identity (`IsLionsSol.ae_eq`,
`LionsC12/Lions/Complex.lean`), under the hypotheses that the coefficient is measurable, bounded
and *non-negative* (`isLionsSolution_unique`, `isLionsSolutionΩ_unique`).  Existence is not
needed: the solution is exhibited.  *Effect:* stronger (weaker hypotheses for uniqueness).

## Part B. Theorem 1.1 and Corollary 1.2

**B1. Theorem 1.1, the choice of `ε`** (`thm:main`, proof).  *Paper:* `ε` sufficiently small.
*Lean:* `ε = min 1 (δ / (2 (1 + 2 C_β)))`, `A = ε/480`, `B = 2 ε C_β`, ellipticity constants
`1 − ε/480` and `1 + ε/480`.  *Effect:* choice.

**B2. Theorem 1.1, the time derivative** (`thm:main`, `u ∈ C¹([0,1];V')`).  *Lean:* `u` is
continuous into `V` and `t ↦ u(t) ∈ V'` is differentiable, with continuous derivative, on all of
`ℝ` (`continuous_uV`, `hasDerivAt_ofH10_uV`, `continuous_uV'`); the statement asserts the
one-sided form on `[0,1]`.  *Effect:* stronger (in the library), the paper's form (in the
statement).

**B3. Theorem 1.1, the equation** (`thm:main`, "in `V'` for every `t ∈ [0,1]`").  *Lean:* the
equation holds in `V'` for every `t ∈ ℝ` (`equation_uV`), and the elliptic part is represented by
`-∂ₓ(𝔞∂ₓu)(t) ∈ H` for every `t` (`form_uV`).  *Effect:* stronger.

**B4. Theorem 1.1, `u` is the Lions solution** (`thm:main`).  *Lean:* the statement contains both
`IsLionsSolution … u` and uniqueness in that class (A3, A9).  *Effect:* as stated.

**B5. Corollary 1.2, the domain** (`cor:bounded-domains`).  *Paper:* a bounded domain `Ω ⊂ ℝ^d`.
*Lean:* the statement assumes a bounded non-empty open set (connectedness is dropped); the proof
uses neither boundedness nor connectedness: `lions_counterexample_open`
(`LionsC12/Domains/Corollary.lean`) proves the conclusion for every non-empty open `Ω ⊆ ℝ^d`.
*Effect:* stronger.

**B6. Corollary 1.2, the matrix norm** (`cor:bounded-domains`).  *Lean:* `𝔅(t,x) = 𝔟(t,x) Id_d` is
`isoCoeff 𝔟 t x`, a continuous linear map of `EuclideanSpace ℝ (Fin d)`, and
`L^∞(Ω;ℝ^{d×d})` is `eLpNorm · ∞` of the operator norm; "real symmetric" is `IsSelfAdjoint` and
uniform ellipticity is `λ‖ξ‖² ≤ ⟨𝔅ξ, ξ⟩`.  All norms on `ℝ^{d×d}` give the same space; for
`𝔟 Id_d − 𝔟' Id_d` the operator norm is `|𝔟 − 𝔟'|`.  *Effect:* different form.

**B7. Corollary 1.2, the localisation** (proof of `cor:bounded-domains`).  *Paper:*
`χ ∈ C_c^∞((−1,1)^{d−1})`, `x₀ + rK ⋐ Ω` with `K = [0,π] × \overline{Q'}`, and the case `d = 1`
treated separately.  *Lean:* `χ` is a smooth bump of Mathlib on `ℝ^{d−1}` supported in the closed
unit ball (`bumpE`); `x₀ = p` is the centre of a ball `B(p,ρ) ⊆ Ω`, `r = min(1, ρ/(2(π+1)))`, and
the support set is `closedBall(p, r(π+1))`; `d = 1` is `d = n + 1` with `n = 0`, where `ℝ^0` is a
point, `χ ≡ 1` and `Δ'χ = 0`.  `ε = min(1, δr/(2(1 + 2C_β)))`, with the ½-Hölder constant
`B = 2εC_β/r` and `A = ε/480`.  *Effect:* choice.

**B8. Corollary 1.2, `U ∈ C¹([0,1];V_Ω')`** (proof of `cor:bounded-domains`).  *Paper:*
`W ∈ C(ℝ;H¹(ℝ^d))`, `∂ₛW = G + div(𝔅_d∇W) ∈ C(ℝ;H⁻¹(ℝ^d))`, and the boundedness of the dilation
and restriction maps.  *Lean:* `U'(t) := F(t) − 𝒜(t)U(t)` (`dU'`, `LionsC12/Domains/Equation.lean`),
continuous into `V_Ω'` because `t ↦ 𝔟∇U(t)` is continuous in `L²(Ω;ℂ^d)`; it equals `∂ₜU(t) ∈ H_Ω`
by the spatial weak formulation at fixed `t` (`dU'_eq`), and the derivative at the accumulation
time `5r²/16` comes from the fundamental theorem of calculus (continuity, differentiability off a
countable set, a continuous derivative; `hasDerivAt_ofH10_dU`).  *Effect:* different route.

**B9. Corollary 1.2, failure of `α`-Hölder continuity** (proof of `cor:bounded-domains`).
*Lean:* `𝔟` is evaluated at `p ∈ Ω`, where the rescaled first coordinate is `0`, and the essential
supremum over the open set `Ω` dominates the value at `p` of the continuous `𝔟(t,·)`
(`not_holder_dB`, `LionsC12/Domains/Main.lean`).  *Effect:* different route (as C3.2).

## Part C. Sections 2–7

### Section 2

**C2.1. Lemma 2.1, the constant** (`lem:oscillatory-modes`).  *Paper:* `‖p_K‖_{V'} ≤ C K⁻¹`.
*Lean:* `‖p_K‖_{V'} ≤ 6/K` (`norm_p_Hm1_le`, `LionsC12/Interval/Modes.lean`).  *Effect:* stronger
(explicit constant).

**C2.2. Lemma 2.1, `A_{0,H}p_K`** (`eq:oscillatory-mode-laplacian`).  *Lean:* stated as
`IsRealisation one 0 (pV K) g`: `⟨∂ₓp_K, ∂ₓw⟩_H = ⟨g, w⟩_H` for all `w ∈ V`, the realisation in
`H` of the form operator of the coefficient `1`, which is `-∂ₓ²` on `D(A_{0,H}) = H² ∩ H¹₀`
(`isRealisation_one_iff`, `domain_one_eq_H2`; C3.4).  *Effect:* different form.

### Section 3

**C3.1. Proposition 3.2, explicit constants** (`prop:coefficient`).  *Paper:*
`‖𝔞 − 1‖_{L^∞} ≤ Cε` and `‖𝔞(t) − 𝔞(s)‖_{L^∞} ≤ Cε|t − s|^{1/2}`.  *Lean:* pointwise at every
`(t,x)`: `|𝔞 − 1| ≤ ε/480` (`abs_a_sub_one_le`) and `|𝔞(t,x) − 𝔞(s,x)| ≤ 2εC_β|t − s|^{1/2}`
(`abs_a_sub_le`, `LionsC12/Coefficient/Holder.lean`), with `C_β` depending only on the cutoff;
the `L^∞` forms are `eLpNorm_a_sub_one_le`, `eLpNorm_a_sub_le`.  *Effect:* stronger.

**C3.2. Proposition 3.3, the route** (`prop:holder-sharp`).  *Paper:* tests the increment against
the Fourier coefficient `Λ_K`.  *Lean:* evaluates at `x = 0`, where `cos(K·0) = 1` for every mode
(`not_holder`, `LionsC12/Coefficient/Sharpness.lean`), and passes to the essential supremum by
continuity of `𝔞(t,·)` (`not_holder_Linfty`).  *Effect:* different route.

**C3.3. Remark 3.1** (*Choice of the frequencies*).  Not formalised (Part D).

**C3.4. Proposition 3.4, the domains** (`prop:frozen-domains`).  *Paper:*
`D(A_H(t)) = D₀ = H²(0,π) ∩ H¹₀(0,π)` and `sup_t ‖A_H(t)‖_{L(D₀,H)} = ∞`.  *Lean:* `D(A_H(t))` and
`D₀ = D(A_{0,H})` are the domains of the realisations in `H` of the forms of `𝔞(t)` and of `1`
(`IsRealisation`, `LionsC12/Interval/FrozenDomain.lean`), and `domain_eq` proves their equality
for every `t`.  `domain_one_eq_H2` identifies `D(A_{0,H})` with `H²(0,π) ∩ H¹₀(0,π)`, the
definition of `D₀` in the paper, where `v ∈ H²` means that `v` and its weak derivative have weak
derivatives in `L²` (`MemH2`, `LionsC12/Interval/DomainH2.lean`), and `domain_eq_H2` states
`D(A_H(t)) = H²(0,π) ∩ H¹₀(0,π)` for every `t`.  `‖A_H(t)‖_{L(D₀,H)} < ∞` for each `t` is `exists_bound_on_D₀` and the
unboundedness is `not_uniform_bound_on_D₀`, with the graph norm `‖v‖_V + ‖A_{0,H}v‖_H`, equivalent
to the paper's `‖v‖_H + ‖A_{0,H}v‖_H` on `D₀`.  *Effect:* different form.

### Section 4

**C4.1. Lemma 4.1** (`lem:solution-regularity`).  *Lean:* the clauses are those of Theorem 1.1
(B2, A2, A4); `∫₀¹ ‖∂ₜu‖²_H = ∞` is `not_integrableOn_utNormSq` in the concrete form and
`not_exists_L2_rep_uV'` in the paper's spaces.  *Effect:* as stated.

### Section 5

**C5.1. Proposition 5.1** (`prop:forcing`).  *Lean:* `f` is jointly continuous on `ℝ²`
(`LionsC12/Forcing/Continuity.lean`), and `C([0,1];H)` follows (`continuous_fH`); the equation
holds for every `t ∈ ℝ` (B3).  *Effect:* stronger.

**C5.2. The remark on the growth of the maximal-regularity constant** (Remark 5.2).  *Paper:*
`𝔞_N` has maximal `L²`-regularity, and its constant satisfies `C_N ≥ cε√log(N+1)`.  *Lean:*
`maxRegConstant_growth` (`LionsC12/Interval/Truncation.lean`): the bounds on `𝔞_N` uniform in
`N`, `u_N` a Lions solution with `∂ₜu_N, A_{N,H}u_N ∈ C([0,1];H)`,
`‖f_N‖²_{L²(0,1;H)} ≤ π C_f²`, `‖∂ₜu_N‖²_{L²(0,1;H)} ≥ (πε²/1536)(log(N+2) − 1)`, and every
maximal-regularity constant `C ≥ 0` of `𝔞_N` (`IsMaxRegConstant`) is at least
`√((πε²/1536)(log(N+2) − 1)) / (√π C_f)`.  That `𝔞_N` *has* maximal regularity is
`truncation_maximal_regularity` (`LionsC12/Interval/MaxReg.lean`): for every `g ∈ L²(0,1;H)` there is
a Lions solution whose derivative and elliptic part lie in `L²(0,1;H)` with
`‖w'‖ + ‖A_{N,H}w‖ ≤ C‖g‖`, and `IsMaxRegConstant (aN D N ε) C` holds for that finite `C`;
`truncation_maxReg_growth` combines existence and the lower bound, and
`truncation_optimalMaxRegConstant` shows that the best constant is attained.  The paper argues that
the truncations are finite sums of smooth functions; Lean proves maximal regularity by Lions'
theorem in the triple `D₀ ⊂ V ⊂ D₀'` with pivot `V` (`D₀ = D(A_{0,H})`, `LionsC12/Interval/MaxRegSpace.lean`),
under a Gårding inequality by an exponential shift (`lions_existence_garding`,
`LionsC12/Lions/Garding.lean`), using only that `𝔞_N(t,·)` is `C¹` with `|∂ₓ𝔞_N| ≤ ε Σ_{j≤N} j`
uniformly in `t` (no time regularity), and transfers the regularity to every Lions solution by
uniqueness.  The constant is explicit but far from optimal (it grows like `exp(c N⁴)`); the paper
claims no upper bound.  "Maximal regularity" is for zero initial value.  *Effect:* as stated,
with explicit constants; different route.

### Section 6

**C6.1. Lemma 6.1** (`lem:zero-extension-flux`).  *Paper:* `q ∈ L¹(0,1;H¹(0,π))` with vanishing
traces; the identity in `𝒟'((0,1) × ℝ)`.  *Lean:* `zero_extension_flux`
(`LionsC12/Transfer/FluxExtension.lean`) for `q ∈ L¹(0,1;W^{1,1}(0,π))` ⊇ `L¹(0,1;H¹(0,π))`, read as
`q, ∂ₓq` integrable on `(0,1) × (0,π)` and `q(t,·)` the primitive of `∂ₓq(t,·)` with `q(t,0) = 0`
and `q(t,π) = 0` for almost every `t`; the identity holds for every `ψ` that is `C¹` in `x`, which
contains the test functions of `𝒟'((0,1) × ℝ)`.  *Effect:* stronger.

**C6.2. Propositions 6.2 and 6.3** (`prop:line`, `prop:tensor`).  *Lean:* one theorem,
`lions_counterexample_fullspace` (`LionsC12/Domains/Corollary.lean`), for every `d = n + 1 ≥ 1` on
`Ω = ℝ^d` without rescaling: `𝔟(t,x) = 𝔞(t,x₁)`, `U(t) = ũ(t) ⊗ χ` and
`F(t) = f̃(t) ⊗ χ − 𝔞 ũ(t) ⊗ Δ'χ` almost everywhere, satisfying every clause of Corollary 1.2 on
`ℝ^d` (`DomainClauses`), including `F ∈ C([0,1];L²)`, `U ∈ C([0,1];H¹₀(ℝ^d)) ∩ C¹([0,1];H⁻¹(ℝ^d))`
and uniqueness.  Proposition 6.2 is the case `n = 0`, on `EuclideanSpace ℝ (Fin 1)` rather than
`ℝ`.  *Effect:* stronger (more clauses), different form (the line as `ℝ^1`).

**C6.3. Section 6, the route to the weak formulation.**  *Paper:* "tensoring defines bounded
maps on the relevant Sobolev and Bochner spaces, and a straightforward calculation gives" the
equation.  *Lean:* the weak form on the line of the zero-extended and rescaled solution with no
boundary condition on the test function (`weak1D`, `LionsC12/Domains/OneDim.lean`), the weak form
of `−div(b∇(P ⊗ Q)) = A ⊗ Q − bP ⊗ Δ'Q` by Fubini and integration by parts on lines
(`tensorΩ_weak`, `LionsC12/Domains/Tensor.lean`), and density of test functions in `V_Ω`
(`swf`, `LionsC12/Domains/Equation.lean`).  *Effect:* different route (the details the paper
leaves to the reader).

### Section 7

**C7.1. Corollary 7.1, the route** (`sec:endpoint-exclusions`).  *Paper:* each of (i)–(iv) is
excluded by contradiction: the hypothesis is sufficient for maximal `L²`-regularity by a theorem
of Dier, Haak–Ouhabaz, Achache–Ouhabaz or Auscher–Egert, and maximal regularity fails by
Theorem 1.1.  *Lean:* `endpoint_hypotheses_fail` (`LionsC12/Endpoint/Main.lean`) proves the failure
of every hypothesis directly from the construction; the cited theorems are not formalised
(D2).  *Effect:* different route; the Lean statement does not depend on the literature.

**C7.2. The operator norm** (§7, `‖𝒜(t) − 𝒜(s)‖_{L(V,V')} ≤ ‖𝔞(t) − 𝔞(s)‖_X`).  *Lean:* the
operator norm is `formOpDist`, the supremum of `|𝔞(t)[v,w] − 𝔞(s)[v,w]| / (‖v‖_V ‖w‖_V)` over
`v, w ≠ 0` with the graph norm of `V` (no operator `V → V'` is constructed), and it is proved
*equal* to `‖𝔞(t) − 𝔞(s)‖_{L^∞(0,π)}` (`formOpDist_eq_eLpNorm`, `formOpDist_a`,
`LionsC12/Endpoint/OpNorm.lean`).  `X = L^∞(0,π)` is `Lp ℝ ∞ (volume.restrict (Ioo 0 π))` and the
coefficient path is `aX`.  *Effect:* stronger.

**C7.3. (i) bounded variation.**  *Lean:* `eVariationOn (aX D ε) (Icc 0 1) = ⊤`, and no function
`g`, monotone on `[0,1]`, satisfies Dier's estimate for `0 ≤ s ≤ t ≤ 1` (`LionsC12/Endpoint/BV.lean`).
*Effect:* as stated.

**C7.4. (ii) Dini modulus.**  *Lean:* `ω : ℝ → ℝ` monotone and non-negative on `[0,1]` with the
estimate for `s, t ∈ [0,1]`; "`∫₀¹ ω(r) r^{−3/2} dr < ∞`" is finiteness of the lower Lebesgue
integral of `ofReal (ω r / r^{3/2})` on `(0,1)`.  `dini_form_lintegral_eq_top` and
`dini_coeff_lintegral_eq_top` (`LionsC12/Endpoint/Dini.lean`) prove that this integral is `∞` for
every admissible `ω`.  *Effect:* stronger (Bochner integrability implies finiteness of the lower
integral).

**C7.5. (iii) piecewise `H^{1/2}`.**  *Lean:* a partition is `u : Fin (N+1) → ℝ`, strictly
monotone, `u 0 = 0`, `u N = 1`; some piece `(u k, u (k+1))` has infinite Gagliardo seminorm
`∫⁻∫⁻ ‖𝔞(t) − 𝔞(s)‖²_X / (t − s)²`, and the same for `formOpDist` (`LionsC12/Endpoint/Gagliardo.lean`).
Only the seminorm part of the `H^{1/2}` norm is used, which suffices for a failure.
*Effect:* as stated.

**C7.6. (iv) the Auscher–Egert condition.**  *Lean:* intervals are `(p,q)` with
`0 ≤ p < q ≤ 1`; `M ∈ [0,∞)` is an element of `ℝ≥0∞` below `⊤`; integrals are lower Lebesgue
integrals.  `not_exists_auscherEgert_bound` has the supremum inside the almost-everywhere
quantifier, as in the paper; `not_exists_auscherEgert_bound'` excludes even the weaker hypothesis
in which the null set may depend on the interval.  *Effect:* stronger.

**C7.7. The side conditions of Achache–Ouhabaz** (proof of Corollary 7.1).  *Lean:* local
smallness for every interval `(p,q)` with the constant `4 C_β² ε²` (`iSup_lintegral_formOpDist_sq_div_le`,
`exists_partition_local_smallness`, `LionsC12/Endpoint/Smallness.lean`); the uniform form
equivalence is `(479/480)‖∂ₓv‖² ≤ Re 𝔞(t)[v,v] ≤ (481/480)‖∂ₓv‖²` with `‖∂ₓv‖_H` in place of
`‖v‖_V` (Poincaré's inequality on `V` is not formalised).  The positive self-adjoint realisation
`A_H(t)`, its square root and the Kato property are not formalised (D2).  *Effect:* weaker
(the form part of the side conditions only).

**C7.8. Proof routes in Section 7.**  The lower bounds at the scale of one mode are taken at the
point `x = 0` (as in C3.2); the Gagliardo energy of one oscillation is bounded below on
rectangles where the phase lies in `[π/4, 3π/4]` and `[5π/4, 7π/4]`, with the constant
`1/(36π)` under the condition `A L ≥ 8π` (`LionsC12/Endpoint/Rectangles.lean`); the variation is
bounded below by `3K` quarter-period steps of the first mode on each `J_j`; the Dini integral by
the pieces `(h_{j+1}, h_j]` and the harmonic series.  *Effect:* different route.

## Part D. Not formalised

**D1. Remark 3.1** (*Choice of the frequencies*): a comment that the factor 16 could be replaced
by a dyadic family; no claim of the paper depends on it.

**D2. The sufficiency theorems cited in Section 7**: Dier [Theorem 4.1], Haak–Ouhabaz
[Theorem 1.2], Achache–Ouhabaz [Theorem 2.2] and Auscher–Egert [Theorem 2, condition (8)], and
the operator-theoretic part of the side conditions of Achache–Ouhabaz (the self-adjoint
realisations and the Kato square-root property).  Corollary 7.1 does not need them in the Lean
route (C7.1).

## Part E. Material not in the paper

**E1. Lions' theorem on real Gelfand triples** (`LionsC12/Lions/`): Lions' projection theorem,
existence (`lions_existence`), the Lions–Magenes energy identity (`lions_magenes`), uniqueness
(`lions_uniqueness`), and the continuous representative (`variational_continuous`).  The paper
cites Lions' theorem.

**E2. Corollary 1.2 on every open set** (`lions_counterexample_open`), and
Propositions 6.2/6.3 with all clauses of Corollary 1.2 (`lions_counterexample_fullspace`); see B5,
C6.2.

**E3. The explicit layer** (`LionsC12/Construction/`, `Modes/`, `Coefficient/`, `Solution/`,
`Forcing/`, `Transfer/`).  Every object of Sections 2–6 is first built as an explicit real function
of `(t,x)` with classical derivatives (`HasDerivAt`), and the estimates of the paper are proved for
these functions: pointwise bounds, interval integrals over `0..π`, `finsum`s over the blocks.  The
statements in the paper's spaces (`LionsC12/Interval/`, `LionsC12/Domains/`, `LionsC12/Endpoint/`)
are built on this layer by turning the functions into elements of `L²`, `H¹₀` and `H⁻¹`.
