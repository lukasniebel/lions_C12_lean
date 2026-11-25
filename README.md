# LionsC12

A machine-checked **Lean 4** formalisation of the paper

> Lukas Niebel,
> [*Lions' maximal regularity problem for divergence-form differential operators: failure at the
> ½-Hölder endpoint*](https://arxiv.org/abs/2608.11194v2), arXiv:2608.11194v2.

The two main results of the paper are proved in the paper's function spaces, with uniqueness of
the Lions variational solution: **Theorem 1.1**, the counterexample to maximal `L²`-regularity on
an interval, and **Corollary 1.2**, the counterexample on every bounded domain of every dimension.
Lemma 2.1, Propositions 3.2–3.4, Lemma 4.1, Proposition 5.1, the remark on the growth of the
maximal-regularity constant (Remark 5.2: the truncated problems have maximal `L²`-regularity, and
every constant is at least `c ε √log N`), Lemma 6.1 and Propositions 6.2 and 6.3 are proved as
stated.  One statement is formalised in part:

- **Corollary 7.1**: the failure of each of the four endpoint hypotheses is proved directly from
  the construction, with the form part of the side conditions of Achache–Ouhabaz; the cited
  sufficiency theorems and the operator-theoretic part of those side conditions (self-adjoint
  realisations, square roots, the Kato property) are not formalised.

Remark 3.1, a comment without a claim, has no Lean counterpart.  The development is built on
[mathlib](https://github.com/leanprover-community/mathlib4) alone: the Sobolev spaces `H¹₀`, their
anti-duals, the Lions solutions and the uniqueness theorem are constructed and proved here.  Where
the formal statements or arguments are not literally those of the paper, the difference is
recorded: in summary [below](#deviations-from-the-paper), and completely in
[`DEVIATIONS.md`](DEVIATIONS.md).

- **About 21,000 lines of Lean** in 61 modules.
- **No `sorry`** and no `admit` in the library or in `Solution.lean`; `Challenge.lean`, the
  specification, ends in two deliberate `sorry`s, which `Solution.lean` replaces.
- **No custom axiom.** Every theorem of the library depends only on `propext`,
  `Classical.choice` and `Quot.sound`, and so do the two compared theorems of `Solution.lean`.
  The release gate checks this for each of the 1339 public theorems of the `LionsC12` namespace
  (private declarations, instances and generated lemmas excluded) through
  [`LionsC12/AxiomAudit.lean`](LionsC12/AxiomAudit.lean), whose inventory it compares with a
  fresh enumeration of the built library.
- **Comparator.** `Solution.lean` is checked against `Challenge.lean` by
  [Comparator](https://github.com/leanprover/comparator) with the Lean kernel and the independent
  kernels NanoDa and con-ron (`scripts/verify-comparator.sh`, also run in CI on every push).
- **The Challenge statement.** [`Challenge.lean`](Challenge.lean) states Theorem 1.1 and
  Corollary 1.2 with mathlib notions and the short definitions of the statement layer, and
  [`Solution.lean`](Solution.lean) proves both from the library.
- Pinned to Lean `v4.35.0` and mathlib `v4.35.0`.

## What is proved

**Theorem 1.1** (`LionsC12.lions_counterexample_interval`, `LionsC12/Interval/Theorem.lean`).  Let
`δ > 0`, `H = L²((0,π);ℂ)`, `V = H¹₀((0,π);ℂ)`, `V' = H⁻¹((0,π);ℂ)`.  There are a bounded,
uniformly elliptic, real coefficient `𝔞` with `𝔞 ∈ C^{0,1/2}([0,1];L^∞(0,π))`,
`‖𝔞 − 1‖_{C^{0,1/2}} < δ` and `𝔞 ∉ C^{0,α}` for every `1/2 < α < 1`, a real forcing
`f ∈ C([0,1];H) ∩ L²(0,1;H)` and a real `u ∈ C([0,1];V) ∩ C¹([0,1];V') ∩ W^{1,1}(0,1;H)` with
`u(0) = 0`, which is the unique Lions variational solution of `u' + 𝒜(t)u = f`, the equation
holding in `V'` for every `t ∈ [0,1]`; moreover `u(t) ∈ D(A_H(t))` for every `t`,
`A_H(·)u(·) ∈ L¹(0,1;H) ∖ L²(0,1;H)`, and `∂ₜu ∉ L²(0,1;H)`.

**Corollary 1.2** (`LionsC12.lions_counterexample_domain`, `LionsC12/Domains/Corollary.lean`).  The
same on every bounded open `Ω ⊆ ℝ^d`, `d ≥ 1`, with the isotropic coefficient matrix
`𝔅 = 𝔟 Id_d` and the spaces `L²(Ω;ℂ)`, `H¹₀(Ω;ℂ)`, `H⁻¹(Ω;ℂ)`; the proof does not use boundedness
or connectedness, and `LionsC12.lions_counterexample_open` states it for every non-empty open set.

**The other statements.**  Lemma 2.1 (`lemma_2_1`); Propositions 3.2–3.4 (`abs_a_sub_le`,
`not_holder_Linfty`, `domain_eq_H2`, `not_uniform_bound_on_D₀`); Lemma 4.1 and Proposition 5.1
(`LionsC12/Interval/Solution.lean`, `LionsC12/Interval/Theorem.lean`); the growth of the
maximal-regularity constant of the truncations: they have maximal regularity, and
`C_N ≥ cε√log N` (`truncation_maximal_regularity`, `truncation_maxReg_growth`);
Lemma 6.1 (`zero_extension_flux`); Propositions 6.2 and 6.3 in the paper's spaces
(`lions_counterexample_fullspace`); and Corollary 7.1 (`endpoint_hypotheses_fail`): the coefficient
path has infinite variation in `L^∞`, there is no Dini modulus, neither the coefficient nor the
form path is piecewise `H^{1/2}`, and the Auscher–Egert square condition fails.  The paper deduces
Corollary 7.1 from the theorems of Dier, Haak–Ouhabaz, Achache–Ouhabaz and Auscher–Egert; the
formalisation proves the failure of each hypothesis directly, without them.

**Lions' theorem.**  The paper cites Lions' theorem for uniqueness.  The formalisation proves it:
on real Gelfand triples (existence by Lions' projection theorem, the Lions–Magenes energy identity,
uniqueness, `LionsC12/Lions/`), and uniqueness in the paper's complex spaces by realification
(`IsLionsSol.ae_eq`, `isLionsSolution_unique`, `isLionsSolutionΩ_unique`), for every Lions solution
in the sense of the statement layer.

[`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps every statement of the paper to its Lean
declarations.

## The Challenge statement

[`Challenge.lean`](Challenge.lean) is a self-contained file importing only mathlib.  It defines the
statement layer — `L2`, `H10` (the closure in `L² × L²` of the graphs of `C¹_c` functions), `val`,
`dx`, `Hm1` (the anti-dual of `H10`), the embeddings `ofL2`, `ofH10`, the form `form`, the
distributional time derivative `HasWeakDeriv`, the class `IsLionsSolution`, and their analogues
on `Ω ⊆ ℝ^d` — and states `LionsC12Challenge.lions_counterexample_interval` (Theorem 1.1) and
`LionsC12Challenge.lions_counterexample_domain` (Corollary 1.2), each ending in `sorry`.  The
docstrings of the two theorems say how each clause of the paper is read.
[`Solution.lean`](Solution.lean) repeats the statements and proves them from the library.

The definitions of `Challenge.lean` are repeated character for character in
[`LionsC12/Paper/Statement.lean`](LionsC12/Paper/Statement.lean), and the statements and docstrings
of the two theorems in `Solution.lean`; the release gate checks both identities
([`scripts/check-challenge-text.py`](scripts/check-challenge-text.py)).
[`comparator.json`](comparator.json) configures the
[Comparator](https://github.com/leanprover/comparator) check of `Solution.lean` against
`Challenge.lean` with the permitted axioms `propext`, `Quot.sound`, `Classical.choice`; it is run
by [`scripts/verify-comparator.sh`](scripts/verify-comparator.sh).

## Deviations from the paper

The complete list is [`DEVIATIONS.md`](DEVIATIONS.md).  In summary:

- **Function spaces.** Mathlib has no Sobolev spaces; `H¹₀` is the closure of `C¹_c` graphs in
  `L² × L²` with the graph norm, `H⁻¹` its anti-dual, and the Bochner spaces are mathlib's.  On
  open sets this `H¹₀` is the closure of `C_c^∞` in the space `W^{1,2}` defined by weak
  derivatives (`range_H10toW12`, `range_H10ΩtoW12Ω`).
- **Readings.** `C¹([0,1];V')` is a derivative within `[0,1]` at every point; `W^{1,1}(0,1;H)` is
  integrability with an integrable distributional derivative; "`∂ₜu ∉ L²`" says that no
  `L²`-function represents `u'`; the `C^{0,1/2}` norm is the sum of the two suprema.
- **Uniqueness** is proved under weaker hypotheses than the paper's (non-negativity of the form in
  place of coercivity).  `D(A_{0,H})` is the domain of the realisation of the form, which is
  `H² ∩ H¹₀` (`domain_one_eq_H2`).
- **Explicit constants** in place of `C`: `‖p_K‖_{V'} ≤ 6/K`, `|𝔞 − 1| ≤ ε/480`, the constant
  `π/1536` in the growth of the maximal-regularity constant.  Maximal regularity of the truncations
  is proved by Lions' theorem in the triple `H² ∩ H¹₀ ⊂ H¹₀ ⊂ (H² ∩ H¹₀)'` rather than from
  smoothness of the truncated coefficient.
- **Routes.** Propositions 3.3 and the lower bounds of Section 7 evaluate at `x = 0` instead of
  testing against a Fourier coefficient; `U ∈ C¹([0,1];V_Ω')` in Corollary 1.2 is proved without
  dilation estimates in `H⁻¹`; Corollary 7.1 is proved directly, and the cited sufficiency theorems
  are not formalised.

## Guarantees

- **No `sorry`, no escape hatches.** The release gate [`scripts/audit.sh`](scripts/audit.sh)
  strips comments and strings from every source file of the library, `Check.lean`,
  `CheckDecls.lean` and `Solution.lean` and rejects `sorry`, `sorryAx`, `admit`, the declaration
  keywords `axiom`, `opaque`, `constant`, `unsafe`, `extern`, `partial def`, and `implemented_by`,
  `native_decide`, `lcProof`, `unsafeCast`, `ofReduceBool`, `ofReduceNat`, `trustCompiler`.  It
  requires every module except [`LionsC12/AxiomAudit.lean`](LionsC12/AxiomAudit.lean) to be imported
  from the root module.  The library and `Solution.lean` are built with warnings as errors, and the
  library passes the Batteries linter; `Challenge.lean` must build with exactly two warnings, its
  deliberate `sorry`s.  Every tracked `.lean` file is a `module` file of at most 10,000 lines, and
  none is a symbolic link ([`scripts/check-lean-sources.py`](scripts/check-lean-sources.py)).
- **Axioms.** [`LionsC12/AxiomAudit.lean`](LionsC12/AxiomAudit.lean), generated by
  [`scripts/generate-axiom-audit.py`](scripts/generate-axiom-audit.py), prints the axioms of every
  public theorem of the `LionsC12` namespace (private declarations, instances and generated lemmas
  excluded); the gate fails unless each depends on no axiom other than `propext`,
  `Classical.choice`, `Quot.sound`, unless the *set* of reported declarations equals the checked-in
  list [`scripts/audited-declarations.txt`](scripts/audited-declarations.txt), and unless that
  inventory equals a fresh enumeration of the theorems of the built library
  (`generate-axiom-audit.py --check`).  It also prints the axioms of the two compared theorems of
  `Solution.lean` and requires the same three.
- **Comparator.** [`scripts/verify-comparator.sh`](scripts/verify-comparator.sh) runs
  [Comparator](https://github.com/leanprover/comparator) with [`comparator.json`](comparator.json):
  it builds `Challenge.lean` and `Solution.lean` in a sandbox, checks that `Solution.lean` proves
  exactly the statements of `Challenge.lean` with the permitted axioms, and replays the proofs in
  the Lean kernel and in the independent kernels NanoDa and con-ron.  It needs
  [bubblewrap](https://github.com/containers/bubblewrap) with unprivileged user namespaces.
- **Continuous integration.** [`.github/workflows/audit.yml`](.github/workflows/audit.yml) runs the
  release gate and Comparator on every push to `main` and on pull requests.
- **Release surface.** [`Check.lean`](Check.lean) is a curated tour of the statement layer and the
  principal results of each section; every `#check`ed name is on the audited list, and the file is
  elaborated with warnings as errors.
- **Non-vacuity.** The objects are explicit: the coefficient `1 + εβ`, the solution
  `ρφ + Σ y_{j,m} p_{K_{j,m}}`, the forcing `∂ₜu + 𝒜(t)u`; the Lions class contains the solution and
  uniqueness is proved for every member of it.  The negative clauses are formulated so that they
  cannot hold for a trivial reason (no representative of `u'` is square integrable).
- **Pinned toolchain.** Lean `v4.35.0` and mathlib `v4.35.0`, with every dependency revision
  recorded in [`lake-manifest.json`](lake-manifest.json).

## Building

The Lean toolchain is pinned in [`lean-toolchain`](lean-toolchain) (`leanprover/lean4:v4.35.0`)
and every dependency revision in [`lake-manifest.json`](lake-manifest.json).  With
[elan](https://github.com/leanprover/elan) installed:

```bash
lake exe cache get   # prebuilt mathlib
lake build
```

Afterwards `import LionsC12` loads the whole development.

The repository also carries a self-contained toolchain, which the release gate uses and which needs
no elan.  On Linux x86-64, [`scripts/bootstrap-lean.sh`](scripts/bootstrap-lean.sh) downloads the
official Lean `v4.35.0` release into `.toolchains/` and verifies its checksum, compiles a small
`LD_PRELOAD` library from [`scripts/proc_exe_shim.c`](scripts/proc_exe_shim.c) (for environments
without procfs), fetches the dependencies pinned in `lake-manifest.json` and downloads the mathlib
cache.  [`scripts/lake`](scripts/lake) and [`scripts/lean`](scripts/lean) run `lake` and `lean` of
that installation.

```bash
./scripts/bootstrap-lean.sh
```

The release gate builds the library with warnings as errors and runs the checks of
[Guarantees](#guarantees):

```bash
LEAN_NUM_THREADS=4 bash scripts/audit.sh
```

## Repository layout

```
LionsC12/               the library
  Paper/                the statement layer (the definitions of Challenge.lean)
  Spaces/               L², H¹₀, H⁻¹ and W^{1,2} on the line; the forms; time derivatives
  Lions/                Lions' theorem: real Gelfand triples, complex realification
  Construction/         the definitions of the construction; existence of the cutoffs
  Modes/, Coefficient/, Solution/, Forcing/
                        §§2–5 for the explicit functions (classical derivatives)
  Interval/             §§1–5 in the paper's spaces: Theorem 1.1, Lemma 2.1, Prop. 3.4,
                        Lemma 4.1, Prop. 5.1, the growth of the maximal-regularity constant
  Transfer/             §6: zero extension and parabolic rescaling; Lemma 6.1
  Domains/              §6 and Corollary 1.2 in the paper's spaces
  Endpoint/             §7: Corollary 7.1
  AxiomAudit.lean       the axiom report (generated)
LionsC12.lean           the root module, importing the whole library
Challenge.lean          Theorem 1.1 and Corollary 1.2 in mathlib's terms, ending in `sorry`
Solution.lean           the same theorems, proved from the library
comparator.json         the Comparator configuration
formalization.yaml      provenance, sources, process and review (formalization.yaml v0.4)
Check.lean              the release surface
CheckDecls.lean         the check that every declaration cited in the blueprint exists
CORRESPONDENCE.md       paper ↔ Lean, statement by statement
DEVIATIONS.md           every deviation from the paper
docs/MODULE_MAP.md      every module, with its content and imports
blueprint/              the Lean blueprint
home_page/              the landing page of the documentation site
scripts/                the release gate, the pinned toolchain and the Comparator check
```

## Blueprint

[`blueprint/`](blueprint/) is a Lean blueprint built with
[leanblueprint](https://github.com/PatrickMassot/leanblueprint), with one chapter per section of the
paper and one for Lions' theorem.  Each node carries the statement, the Lean declarations that
formalise it, and its dependencies; where the Lean statement or proof differs from the paper, a
paragraph **Lean form** after the node says how.  Every node is formalised.

To build it, install `leanblueprint` (it needs a TeX distribution and Graphviz) and run
`leanblueprint web` or `leanblueprint pdf` from the repository root.  The release gate checks that
every declaration cited in the blueprint exists in the built library.  The workflow
[`.github/workflows/blueprint.yml`](.github/workflows/blueprint.yml), run on every push to `main`,
builds the blueprint (web and pdf) and the API documentation and assembles them with
[`home_page/`](home_page/) into the `documentation-site` artifact of the run; nothing is deployed.

## How this was built

The Lean code, the blueprint and the documentation were written by AI coding agents (Anthropic's
Claude models, run through Claude Code); the author of the paper supplied the paper and directed and
supervised the work.  Lean checks the proofs against the formal statements; the correspondence
between those statements and the paper is documented in [`CORRESPONDENCE.md`](CORRESPONDENCE.md) and
[`DEVIATIONS.md`](DEVIATIONS.md).  The author reviewed that the statements are the intended theorems;
each public statement, the Challenge statement among them, was compared with the paper by
independent AI review passes, and [Comparator](https://github.com/leanprover/comparator) checks
`Solution.lean` against `Challenge.lean` with the Lean kernel and the independent kernels NanoDa and
con-ron.  This is not external peer review.

## Author and citation

The formalisation accompanies the paper of [**Lukas Niebel**](https://lukasniebel.github.io).  To
cite it, use [`CITATION.cff`](CITATION.cff).

## Acknowledgements

Lukas Niebel is funded by SNSF Starting Grant TMSGI2_226018 and by the Deutsche
Forschungsgemeinschaft (DFG, German Research Foundation) under Germany's Excellence Strategy
EXC 2044/2–390685587, Mathematics Münster: Dynamics–Geometry–Structure.

## License

The Lean code in this repository is copyright 2026 Lukas Niebel and is licensed under the Apache
License 2.0; see [`LICENSE`](LICENSE).
