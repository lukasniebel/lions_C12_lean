# Module map

Every module of the library, by directory, with the title of its module docstring and the modules
of the project it imports.  `LionsC12.lean` imports all of them except `LionsC12.AxiomAudit`
(the axiom audit, elaborated by `scripts/audit.sh`).  The paper-to-Lean correspondence at the level of
declarations is `CORRESPONDENCE.md`; the blueprint (`blueprint/`) gives it statement by statement.

The library has two layers.  The *explicit* layer (`Construction`, `Modes`, `Coefficient`, `Solution`,
`Forcing`, `Transfer`) builds the construction from explicit real functions of `(t,x)` with classical
derivatives and proves the estimates of the paper for them.  The *Hilbert-space* layer (`Paper`, `Spaces`,
`Lions`, `Interval`, `Domains`, `Endpoint`) states the results in the paper's spaces `L²`, `H¹₀`, `H⁻¹`
and Bochner spaces, building on the explicit layer.

## `LionsC12/Paper/` — The statement layer (the definitions of `Challenge.lean`)

| Module | Content | Imports (project) |
|---|---|---|
| `Statement.lean` (194 lines) | The statement layer: the function spaces of the paper | — |

## `LionsC12/Spaces/` — Function spaces on the line, the forms, distributional time derivatives

| Module | Content | Imports (project) |
|---|---|---|
| `Forms.lean` (153 lines) | The forms `𝔞(t)[v,w]` on `H¹₀(U)` and uniqueness of the Lions solution | `Spaces.Line` |
| `Line.lean` (601 lines) | The spaces `L²(U;ℂ)`, `H¹₀(U;ℂ)` and `H⁻¹(U;ℂ)` on the line | `Lions.Complex` |
| `Sobolev.lean` (553 lines) | `W^{1,2}(U)` and `H¹₀(U)` through weak derivatives, on an open set `U ⊆ ℝ` | `Spaces.Line`, `Spaces.TimeL2` |
| `Time.lean` (255 lines) | Distributional derivatives in time | `Paper.Statement`, `Lions.WeakDeriv` |
| `TimeL2.lean` (159 lines) | Time regularity of `L²`-valued functions with a fixed compact support | `Spaces.Line` |

## `LionsC12/Lions/` — Lions' theorem: real Gelfand triples and the complex realification

| Module | Content | Imports (project) |
|---|---|---|
| `Complex.lean` (244 lines) | Lions' theory on complex Gelfand triples: uniqueness of the variational solution | `Lions.Uniqueness`, `Spaces.Time` |
| `Energy.lean` (1180 lines) | The Lions–Magenes lemma | `Lions.Gelfand`, `Lions.WeakDeriv`, `Lions.Steklov` |
| `Garding.lean` (289 lines) | Lions' theorem under a Gårding inequality | `Spaces.Time`, `Lions.Uniqueness` |
| `Gelfand.lean` (549 lines) | Gelfand triples and Lions' existence theorem | `Lions.Projection` |
| `Projection.lean` (127 lines) | Lions' projection theorem | — |
| `Steklov.lean` (432 lines) | Steklov averages | — |
| `Uniqueness.lean` (199 lines) | Lions' theorem: uniqueness and the continuous representative | `Lions.Gelfand`, `Lions.WeakDeriv`, `Lions.Energy` |
| `WeakDeriv.lean` (572 lines) | Weak derivatives in `V'`, the absolutely continuous representative, integration by parts | `Lions.Gelfand` |

## `LionsC12/Construction/` — Definitions of the construction and existence of the cutoffs

| Module | Content | Imports (project) |
|---|---|---|
| `Cutoffs.lean` (158 lines) | Existence of the cutoff data | `Construction.Defs` |
| `Defs.lean` (264 lines) | Lions' maximal regularity problem: the ½-Hölder counterexample | — |

## `LionsC12/Modes/` — Section 2: the oscillatory modes, explicitly

| Module | Content | Imports (project) |
|---|---|---|
| `Trig.lean` (505 lines) | The spatial oscillatory modes (Section 2 of the paper) | `Construction.Defs` |
| `Vprime.lean` (262 lines) | The `V'`-estimate for the oscillatory modes (Lemma 2.1 of the paper) | `Construction.Defs`, `Modes.Trig` |

## `LionsC12/Coefficient/` — Section 3: blocks, frequencies and the coefficient, explicitly

| Module | Content | Imports (project) |
|---|---|---|
| `Blocks.lean` (359 lines) | Arithmetic of the time blocks and lacunary frequencies (Section 3 of the paper) | `Construction.Defs` |
| `FrozenDomain.lean` (540 lines) | Proposition 3.4: blow-up of the frozen operator on the fixed domain element `φ` | `Construction.Defs`, `Coefficient.Blocks`, `Coefficient.Support`, `Modes.Trig`, `Solution.Basic` |
| `Holder.lean` (434 lines) | Proposition 3.2: ellipticity and `1/2`-Hölder time regularity of the coefficient | `Construction.Defs`, `Coefficient.Blocks`, `Coefficient.Support` |
| `Sharpness.lean` (290 lines) | Proposition 3.3: sharpness within the Hölder scale | `Construction.Defs`, `Coefficient.Blocks`, `Coefficient.Support` |
| `Support.lean` (443 lines) | Supports of the cutoffs, active blocks, and the `finsum` reductions | `Construction.Defs`, `Coefficient.Blocks` |

## `LionsC12/Solution/` — Section 4: the solution and its time derivative, explicitly

| Module | Content | Imports (project) |
|---|---|---|
| `Basic.lean` (504 lines) | Section 4: the candidate solution, its derivatives, and the ODE (4.2) | `Construction.Defs`, `Coefficient.Blocks`, `Coefficient.Support`, `Modes.Trig` |
| `Bochner.lean` (690 lines) | Lemma 4.1 / Proposition 5.1 in Bochner form | `Construction.Defs`, `Coefficient.Blocks`, `Coefficient.Support`, `Modes.Trig`, `Modes.Vprime`, `Coefficient.Holder`, `Solution.Basic`, `Forcing.Cancellation`, `Forcing.Continuity`, `Solution.L1`, `Forcing.Elliptic` |
| `Divergence.lean` (290 lines) | Lemma 4.1: the time derivative is not square integrable | `Construction.Defs`, `Coefficient.Blocks`, `Coefficient.Support`, `Modes.Trig`, `Solution.Basic` |
| `L1.lean` (350 lines) | Lemma 4.1: `∂_t u ∈ L¹(0,1;H)` | `Construction.Defs`, `Coefficient.Blocks`, `Coefficient.Support`, `Modes.Trig`, `Solution.Basic`, `Solution.Divergence` |

## `LionsC12/Forcing/` — Section 5: cancellation, the forcing, the truncations, explicitly

| Module | Content | Imports (project) |
|---|---|---|
| `Bounds.lean` (134 lines) | Uniform bounds and the time support of the construction | `Coefficient.Holder`, `Forcing.Continuity`, `Forcing.Elliptic`, `Solution.L1` |
| `Cancellation.lean` (312 lines) | Section 5 of the paper: cancellation, the PDE, and the bounded forcing | `Construction.Defs`, `Coefficient.Blocks`, `Coefficient.Support`, `Modes.Trig`, `Solution.Basic` |
| `Continuity.lean` (544 lines) | Joint continuity (Proposition 5.1) | `Construction.Defs`, `Coefficient.Blocks`, `Coefficient.Support`, `Modes.Trig`, `Solution.Basic`, `Coefficient.Holder`, `Forcing.Cancellation` |
| `Elliptic.lean` (223 lines) | The elliptic part: `𝒜(t) u(t) ∈ H` pointwise, but not in `L²(0,1;H)` | `Construction.Defs`, `Coefficient.Blocks`, `Coefficient.Support`, `Modes.Trig`, `Solution.Basic`, `Solution.Divergence`, `Forcing.Cancellation` |
| `Truncation.lean` (557 lines) | Growth of the maximal-regularity constant | `Construction.Defs`, `Coefficient.Blocks`, `Coefficient.Support`, `Modes.Trig`, `Solution.Basic`, `Solution.Divergence`, `Forcing.Cancellation`, `Coefficient.Holder`, `Forcing.Continuity` |

## `LionsC12/Interval/` — Sections 1–5 in the paper's spaces: Theorem 1.1

| Module | Content | Imports (project) |
|---|---|---|
| `DomainH2.lean` (83 lines) | `D(A_{0,H}) = H²(0,π) ∩ H¹₀(0,π)`: Proposition 3.4 with the paper's `D₀` | `Spaces.Sobolev`, `Interval.FrozenDomain` |
| `Dual.lean` (174 lines) | Dual norms in `H⁻¹((0,π);ℂ)` from estimates against `C¹` test functions | `Interval.Elements` |
| `Elements.lean` (209 lines) | The concrete functions as elements of `L²((0,π);ℂ)`, `H¹₀((0,π);ℂ)` and `H⁻¹((0,π);ℂ)` | `Construction.Cutoffs`, `Coefficient.Sharpness`, `Coefficient.FrozenDomain`, `Solution.Bochner`, `Forcing.Bounds`, `Forcing.Truncation`, `Transfer.Rescaling`, `Spaces.Forms` |
| `FrozenDomain.lean` (383 lines) | Proposition 3.4 in the paper's spaces: common operator domain without uniform graph control | `Interval.Theorem` |
| `MaxReg.lean` (415 lines) | Maximal `L²`-regularity of the truncated problems | `Interval.MaxRegSpace`, `Interval.Truncation`, `Lions.Garding` |
| `MaxRegSpace.lean` (421 lines) | The domain `D₀` of the Dirichlet Laplacian as a Hilbert space, and `C¹` coefficients | `Interval.FrozenDomain` |
| `Modes.lean` (140 lines) | Lemma 2.1 in the paper's spaces | `Interval.FrozenDomain` |
| `Solution.lean` (228 lines) | Lemma 4.1 in the paper's spaces: `u ∈ C([0,1];V) ∩ C¹([0,1];V') ∩ W^{1,1}(0,1;H)` | `Interval.Dual` |
| `Theorem.lean` (353 lines) | Theorem 1.1 in the paper's function spaces | `Interval.Solution`, `Construction.Cutoffs` |
| `Truncation.lean` (372 lines) | The remark on the growth of the maximal-regularity constant, in the paper's spaces | `Interval.Theorem` |

## `LionsC12/Transfer/` — Section 6: zero extension, parabolic rescaling, Lemma 6.1

| Module | Content | Imports (project) |
|---|---|---|
| `FluxExtension.lean` (144 lines) | Lemma 6.1: zero extension of a vanishing flux | `Spaces.Time`, `Transfer.Rescaling` |
| `Rescaling.lean` (286 lines) | Zero extension and parabolic rescaling of the interval construction | `Construction.Defs`, `Coefficient.Blocks`, `Coefficient.Support`, `Modes.Trig`, `Solution.Basic`, `Solution.Divergence`, `Forcing.Cancellation`, `Coefficient.Holder`, `Coefficient.Sharpness`, `Forcing.Continuity`, `Forcing.Elliptic` |

## `LionsC12/Domains/` — Section 6 and Corollary 1.2 in the paper's spaces

| Module | Content | Imports (project) |
|---|---|---|
| `Construction.lean` (374 lines) | The counterexample on a domain: the functions | `Domains.OneDim` |
| `Coordinates.lean` (141 lines) | Coordinates `x = (x₁, x')` on `ℝ^{n+1}` | `Domains.Spaces`, `Spaces.TimeL2` |
| `Corollary.lean` (231 lines) | Corollary 1.2 of the paper in the paper's Hilbert spaces | `Domains.Main` |
| `Equation.lean` (365 lines) | The counterexample on a domain in the paper's spaces | `Domains.Construction` |
| `Main.lean` (286 lines) | The clauses of Corollary 1.2 for the construction on a domain | `Domains.Equation`, `Construction.Cutoffs` |
| `OneDim.lean` (347 lines) | One-dimensional ingredients of the construction on a domain | `Domains.Tensor`, `Interval.Elements` |
| `Sobolev.lean` (363 lines) | `W^{1,2}(Ω)` and `H¹₀(Ω)` through weak gradients, on an open set `Ω ⊆ ℝ^d` | `Domains.Spaces`, `Spaces.Sobolev` |
| `Spaces.lean` (512 lines) | The spaces `L²(Ω;ℂ)`, `H¹₀(Ω;ℂ)` and `H⁻¹(Ω;ℂ)` on a domain `Ω ⊆ ℝ^d` | `Spaces.Forms` |
| `Tensor.lean` (432 lines) | Tensor products `P(x₁) Q(x')` and their spatial weak formulation | `Domains.Coordinates` |

## `LionsC12/Endpoint/` — Section 7: Corollary 7.1

| Module | Content | Imports (project) |
|---|---|---|
| `BV.lean` (222 lines) | (i) Unbounded variation: failure of Dier's hypothesis | `Endpoint.Coefficient` |
| `Coefficient.lean` (258 lines) | The coefficient path `t ↦ 𝔞(t) ∈ L^∞(0,π)` and its increments | `Endpoint.OpNorm`, `Interval.Theorem` |
| `Dini.lean` (263 lines) | (ii) No Dini modulus: failure of the Haak–Ouhabaz hypothesis | `Endpoint.Coefficient` |
| `Gagliardo.lean` (453 lines) | (iii) Not piecewise `H^{1/2}` and (iv) the Auscher–Egert square condition | `Endpoint.Coefficient`, `Endpoint.Rectangles` |
| `Main.lean` (117 lines) | Corollary 7.1: failure of the known sufficient hypotheses at the endpoint | `Endpoint.BV`, `Endpoint.Dini`, `Endpoint.Gagliardo`, `Endpoint.Smallness` |
| `OpNorm.lean` (573 lines) | The operator norm `‖𝒜(t) − 𝒜(s)‖_{L(V,V')}` of a coefficient increment | `Spaces.Forms` |
| `Rectangles.lean` (273 lines) | The Gagliardo `H^{1/2}` energy of a single oscillation | — |
| `Smallness.lean` (117 lines) | The positive side conditions: local smallness and uniform form equivalence | `Endpoint.Coefficient` |

## `LionsC12/AxiomAudit.lean`

The axiom audit: one `#print axioms` for every theorem of the library (generated by `scripts/generate-axiom-audit.py`).

## Top-level files

| File | Content |
|---|---|
| `Challenge.lean` | Theorem 1.1 and Corollary 1.2 in Mathlib's terms and the definitions of the statement layer, with `sorry` |
| `Solution.lean` | the same statements, proved by `LionsC12.lions_counterexample_interval` and `LionsC12.lions_counterexample_domain` |
| `Check.lean` | a curated tour of the public API, elaborated with warnings as errors by the release gate |
| `CheckDecls.lean` | `lake exe checkdecls`: every declaration cited by the blueprint exists |
