# Correspondence: paper ↔ Lean

This document maps the statements of the paper *Lions' maximal regularity problem for
divergence-form differential operators: failure at the ½-Hölder endpoint* (Lukas Niebel,
arXiv:2608.11194v2) to the Lean declarations that formalise them.  `docs/MODULE_MAP.md` gives the
same correspondence at the level of modules, and the blueprint under `blueprint/` gives it with
the statements written out.

**Conventions.**
- Lean names are given in full; the statement layer is in the namespace `LionsC12Challenge`,
  everything else in `LionsC12`.  File paths are relative to the repository root.
- **Source** gives the paper's printed number and its LaTeX label.
- **Status**: `proved` — formalised and proved as stated; `proved*` — proved, with a difference
  recorded in `DEVIATIONS.md` (the Notes column gives the entries); `definition` — a definition;
  `not formalised` — no Lean counterpart (Part D of `DEVIATIONS.md`).
- The function spaces, Bochner spaces, Lions solutions and negative clauses are read as in Part A
  (A1–A9) of `DEVIATIONS.md`, which is not repeated in every row.
- No module contains `sorry` or a project-specific axiom; every audited declaration depends only
  on `propext`, `Classical.choice` and `Quot.sound` (`LionsC12/AxiomAudit.lean`).

## Section 1: the main results

| Source | Lean declaration(s) | File | Status | Notes |
|---|---|---|---|---|
| §1, `H = L²((0,π);ℂ)`, `V = H¹₀((0,π);ℂ)`, `V' = H⁻¹((0,π);ℂ)` | `LionsC12Challenge.L2`, `LionsC12Challenge.H10`, `LionsC12Challenge.Hm1`, `LionsC12Challenge.val`, `LionsC12Challenge.dx`, `LionsC12Challenge.ofL2`, `LionsC12Challenge.ofH10` | `LionsC12/Paper/Statement.lean` | definition | A1 |
| §1, the form `𝔞(t)[v,w]` and `𝒜(t)` | `LionsC12Challenge.form` | `LionsC12/Paper/Statement.lean` | definition | |
| §1, Lions variational solution, distributional time derivative | `LionsC12Challenge.IsLionsSolution`, `LionsC12Challenge.HasWeakDeriv` | `LionsC12/Paper/Statement.lean` | definition | A2, A3 |
| Theorem 1.1 (`thm:main`), the Challenge statement | `LionsC12Challenge.lions_counterexample_interval` | `Challenge.lean`, `Solution.lean` | proved* | A4–A7, B1–B4 |
| Theorem 1.1 (`thm:main`) | `LionsC12.lions_counterexample_interval` | `LionsC12/Interval/Theorem.lean` | proved* | B1–B4 |
| Theorem 1.1, `u(t) ∈ D(A_H(t))`, `A_H(·)u(·) ∈ L¹ ∖ L²` | `LionsC12.form_uV`, `LionsC12.AH_u_L1_not_L2` | `LionsC12/Interval/Theorem.lean` | proved | A4 |
| Theorem 1.1, uniqueness | `LionsC12.eq_uV_of_isLionsSolution`, `LionsC12.isLionsSolution_unique` | `LionsC12/Interval/Theorem.lean`, `LionsC12/Spaces/Forms.lean` | proved* | A9 |
| Corollary 1.2 (`cor:bounded-domains`), spaces on `Ω` | `LionsC12Challenge.L2Ω`, `LionsC12Challenge.H10Ω`, `LionsC12Challenge.Hm1Ω`, `LionsC12Challenge.isoCoeff`, `LionsC12Challenge.formΩ`, `LionsC12Challenge.IsLionsSolutionΩ` | `LionsC12/Paper/Statement.lean` | definition | A1 |
| §1 and Corollary 1.2, `H¹₀` as the closure of `C_c^∞` in `W^{1,2}` | `LionsC12.W12Graph`, `LionsC12.H10Graph_le_W12Graph`, `LionsC12.H10Graph_eq_closure_smoothGraph`, `LionsC12.range_H10toW12`, `LionsC12.W12ΩGraph`, `LionsC12.H10ΩGraph_le_W12ΩGraph`, `LionsC12.H10ΩGraph_eq_closure_smoothGraphΩ`, `LionsC12.range_H10ΩtoW12Ω` | `LionsC12/Spaces/Sobolev.lean`, `LionsC12/Domains/Sobolev.lean` | proved | A1 |
| Corollary 1.2 (`cor:bounded-domains`), the Challenge statement | `LionsC12Challenge.lions_counterexample_domain` | `Challenge.lean`, `Solution.lean` | proved* | B5–B9 |
| Corollary 1.2 (`cor:bounded-domains`) | `LionsC12.lions_counterexample_domain`, `LionsC12.lions_counterexample_open` | `LionsC12/Domains/Corollary.lean` | proved* | B5–B9 |

## Section 2: spatial oscillatory modes

| Source | Lean declaration(s) | File | Status | Notes |
|---|---|---|---|---|
| `φ`, `p_K`, `c_K` | `LionsC12.φ`, `LionsC12.p`, `LionsC12.c`, `LionsC12.pV`, `LionsC12.φV` | `LionsC12/Construction/Defs.lean`, `LionsC12/Interval/Modes.lean`, `LionsC12/Interval/FrozenDomain.lean` | definition | |
| `eq:endpoint-conditions` | `LionsC12.p_zero`, `LionsC12.p_pi`, `LionsC12.p'_zero`, `LionsC12.p'_pi` | `LionsC12/Modes/Trig.lean` | proved | |
| Lemma 2.1 (`lem:oscillatory-modes`) | `LionsC12.lemma_2_1` | `LionsC12/Interval/Modes.lean` | proved* | C2.1, C2.2 |
| `eq:oscillatory-mode-norms` | `LionsC12.normSq_p`, `LionsC12.normSq_c`, `LionsC12.normSq_p'`, `LionsC12.norm_p_Hm1_le` | `LionsC12/Modes/Trig.lean`, `LionsC12/Interval/Modes.lean` | proved* | C2.1 |
| `eq:oscillatory-mode-laplacian` | `LionsC12.isRealisation_pV` | `LionsC12/Interval/Modes.lean` | proved* | C2.2 |
| `eq:coefficient-profile-identity` | `LionsC12.hasDerivAt_coeff_profile` | `LionsC12/Modes/Trig.lean` | proved | |

## Section 3: time blocks, frequencies, and the coefficient

| Source | Lean declaration(s) | File | Status | Notes |
|---|---|---|---|---|
| `τ_j`, `ℓ_j`, `M_j`, `I_j`, `J_j`, `K_{j,m}`, `θ_{j,m}`, `η`, `η_j`, `β`, `𝔞` | `LionsC12.τ`, `LionsC12.ℓ`, `LionsC12.M`, `LionsC12.I`, `LionsC12.J`, `LionsC12.K`, `LionsC12.θ`, `LionsC12.Cutoffs`, `LionsC12.ηj`, `LionsC12.β`, `LionsC12.a` | `LionsC12/Construction/Defs.lean` | definition | A8 |
| `eq:reciprocal-sums` | `LionsC12.S_le`, `LionsC12.sum_K_inv_sq_le`, `LionsC12.M_mul_ℓ`, `LionsC12.M_mul_S_le` | `LionsC12/Coefficient/Blocks.lean` | proved | |
| `eq:oscillations` | `LionsC12.six_le_K_sq_mul_ℓ` | `LionsC12/Coefficient/Blocks.lean` | proved | a lower bound, which is what the proofs use |
| Remark 3.1 | — | — | not formalised | D1 |
| Proposition 3.2 (`prop:coefficient`) | `LionsC12.abs_a_sub_one_le`, `LionsC12.abs_a_sub_le`, `LionsC12.eLpNorm_a_sub_one_le`, `LionsC12.eLpNorm_a_sub_le`, `LionsC12.isBoundedCoeff_a` | `LionsC12/Coefficient/Holder.lean`, `LionsC12/Interval/Theorem.lean` | proved* | C3.1 |
| Proposition 3.3 (`prop:holder-sharp`) | `LionsC12.not_holder`, `LionsC12.not_holder_Linfty` | `LionsC12/Coefficient/Sharpness.lean`, `LionsC12/Interval/Theorem.lean` | proved* | C3.2 |
| Proposition 3.4 (`prop:frozen-domains`) | `LionsC12.domain_eq`, `LionsC12.domain_eq_H2`, `LionsC12.domain_one_eq_H2`, `LionsC12.exists_bound_on_D₀`, `LionsC12.not_uniform_bound_on_D₀` | `LionsC12/Interval/FrozenDomain.lean`, `LionsC12/Interval/DomainH2.lean` | proved* | C3.4 |

## Section 4: the variational solution and its time derivative

| Source | Lean declaration(s) | File | Status | Notes |
|---|---|---|---|---|
| `eq:y-def`, `eq:u-def` | `LionsC12.y`, `LionsC12.v`, `LionsC12.u`, `LionsC12.uV` | `LionsC12/Construction/Defs.lean`, `LionsC12/Interval/Solution.lean` | definition | |
| `eq:y-ode`, `eq:r-def` | `LionsC12.hasDerivAt_y`, `LionsC12.y_ode` | `LionsC12/Solution/Basic.lean` | proved | |
| Lemma 4.1 (`lem:solution-regularity`) | `LionsC12.continuous_uV`, `LionsC12.hasDerivAt_ofH10_uV`, `LionsC12.continuous_uV'`, `LionsC12.integrableOn_utH`, `LionsC12.hasWeakDeriv_val_uV`, `LionsC12.uV_zero`, `LionsC12.not_exists_L2_rep_uV'` | `LionsC12/Interval/Solution.lean`, `LionsC12/Interval/Theorem.lean` | proved* | B2, C4.1 |
| Lemma 4.1, `∫₀¹ ‖∂ₜu‖² = ∞` | `LionsC12.not_integrableOn_utNormSq` | `LionsC12/Solution/Divergence.lean` | proved | |

## Section 5: cancellation and the forcing

| Source | Lean declaration(s) | File | Status | Notes |
|---|---|---|---|---|
| `eq:exact-mode-cancellation` | `LionsC12.mode_cancellation` | `LionsC12/Forcing/Cancellation.lean` | proved | |
| `eq:f-def`, `eq:f-decomposition` | `LionsC12.f`, `LionsC12.pde`, `LionsC12.fH`, `LionsC12.utH_add_AuH` | `LionsC12/Construction/Defs.lean`, `LionsC12/Forcing/Cancellation.lean`, `LionsC12/Interval/Theorem.lean` | proved | |
| Proposition 5.1 (`prop:forcing`) | `LionsC12.continuous_fH`, `LionsC12.equation_uV` | `LionsC12/Interval/Theorem.lean` | proved* | C5.1 |
| Remark 5.2 (growth of the maximal-regularity constant) | `LionsC12.maxRegConstant_growth`, `LionsC12.IsMaxRegConstant` | `LionsC12/Interval/Truncation.lean` | proved* | C5.2 |
| Remark 5.2, the truncations have maximal `L²`-regularity | `LionsC12.truncation_maximal_regularity`, `LionsC12.truncation_maxReg_growth`, `LionsC12.truncation_optimalMaxRegConstant`, `LionsC12.isMaxRegConstant_of_C1` | `LionsC12/Interval/MaxReg.lean` | proved* | C5.2 (different route) |

## Section 6: full-space and bounded-domain consequences

| Source | Lean declaration(s) | File | Status | Notes |
|---|---|---|---|---|
| Lemma 6.1 (`lem:zero-extension-flux`) | `LionsC12.zero_extension_flux`, `LionsC12.integral_deriv_mul_primitive` | `LionsC12/Transfer/FluxExtension.lean` | proved* | C6.1 |
| §6, `E₀u`, `E₀f`, the weak form on the line | `LionsC12.uZ`, `LionsC12.fZ`, `LionsC12.weak1D` | `LionsC12/Transfer/Rescaling.lean`, `LionsC12/Domains/OneDim.lean` | proved* | C6.3 |
| Proposition 6.2 (`prop:line`) | `LionsC12.lions_counterexample_fullspace` (`n = 0`) | `LionsC12/Domains/Corollary.lean` | proved* | C6.2 |
| Proposition 6.3 (`prop:tensor`) | `LionsC12.lions_counterexample_fullspace`, `LionsC12.DomainClauses` | `LionsC12/Domains/Corollary.lean` | proved* | C6.2 |
| Proof of Proposition 6.3, tensorisation | `LionsC12.tens`, `LionsC12.lapQ`, `LionsC12.tensorΩ_weak` | `LionsC12/Domains/Tensor.lean` | proved* | C6.3 |
| Proof of Corollary 1.2, the rescaled construction | `LionsC12.domB`, `LionsC12.domW`, `LionsC12.domF`, `LionsC12.dU`, `LionsC12.dF`, `LionsC12.dU'` | `LionsC12/Domains/Construction.lean`, `LionsC12/Domains/Equation.lean` | definition | B7 |
| Proof of Corollary 1.2, the clauses | `LionsC12.domainClauses_of_params`, `LionsC12.lions_counterexample_open`, `LionsC12.swf`, `LionsC12.dU'_eq`, `LionsC12.hasDerivAt_ofH10_dU`, `LionsC12.not_holder_dB`, `LionsC12.isLionsSolutionΩ_dU`, `LionsC12.not_exists_L2_dU'`, `LionsC12.not_exists_L2_form` | `LionsC12/Domains/Corollary.lean`, `LionsC12/Domains/Equation.lean`, `LionsC12/Domains/Main.lean` | proved* | B5, B7–B9 |

## Section 7: comparison with endpoint hypotheses in the literature

| Source | Lean declaration(s) | File | Status | Notes |
|---|---|---|---|---|
| §7, `‖𝒜(t) − 𝒜(s)‖_{L(V,V')} ≤ ‖𝔞(t) − 𝔞(s)‖_X` | `LionsC12.formOpDist`, `LionsC12.formOpDist_eq_eLpNorm`, `LionsC12.formOpDist_a` | `LionsC12/Endpoint/OpNorm.lean`, `LionsC12/Endpoint/Coefficient.lean` | proved* | C7.2 (equality) |
| Corollary 7.1, bundled | `LionsC12.endpoint_hypotheses_fail` | `LionsC12/Endpoint/Main.lean` | proved* | C7.1 |
| Corollary 7.1 (i) | `LionsC12.eVariationOn_aX_eq_top`, `LionsC12.not_exists_dier_bound` | `LionsC12/Endpoint/BV.lean` | proved* | C7.1, C7.3 |
| Corollary 7.1 (ii) | `LionsC12.not_exists_dini_form`, `LionsC12.not_exists_dini_coeff`, `LionsC12.dini_form_lintegral_eq_top`, `LionsC12.dini_coeff_lintegral_eq_top` | `LionsC12/Endpoint/Dini.lean` | proved* | C7.1, C7.4 |
| Corollary 7.1 (iii) | `LionsC12.exists_piece_gagliardo_eq_top`, `LionsC12.exists_piece_gagliardo_form_eq_top`, `LionsC12.gagliardoCoeff_eq_top` | `LionsC12/Endpoint/Gagliardo.lean` | proved* | C7.1, C7.5 |
| Corollary 7.1 (iv), `eq:auscher-egert-condition` | `LionsC12.not_exists_auscherEgert_bound`, `LionsC12.not_exists_auscherEgert_bound'` | `LionsC12/Endpoint/Gagliardo.lean` | proved* | C7.1, C7.6 |
| Proof of Corollary 7.1, side conditions of Achache–Ouhabaz | `LionsC12.iSup_lintegral_formOpDist_sq_div_le`, `LionsC12.exists_partition_local_smallness`, `LionsC12.form_self_re_equiv` | `LionsC12/Endpoint/Smallness.lean` | proved* | C7.7 |
| The theorems of Dier, Haak–Ouhabaz, Achache–Ouhabaz, Auscher–Egert | — | — | not formalised | D2 |

## Lions' theorem (cited by the paper)

| Source | Lean declaration(s) | File | Status | Notes |
|---|---|---|---|---|
| Lions' theorem, real Gelfand triples | `LionsC12.lions_existence`, `LionsC12.lions_magenes`, `LionsC12.lions_uniqueness`, `LionsC12.lions_theorem` | `LionsC12/Lions/Gelfand.lean`, `LionsC12/Lions/Energy.lean`, `LionsC12/Lions/Uniqueness.lean` | proved | E1 |
| Lions' theorem under a Gårding inequality (exponential shift) | `LionsC12.lions_existence_garding` | `LionsC12/Lions/Garding.lean` | proved | E1 |
| Uniqueness in the paper's complex spaces | `LionsC12.IsLionsSol.ae_eq`, `LionsC12.isLionsSolution_unique`, `LionsC12.isLionsSolutionΩ_unique` | `LionsC12/Lions/Complex.lean`, `LionsC12/Spaces/Forms.lean`, `LionsC12/Domains/Spaces.lean` | proved* | A9 |
