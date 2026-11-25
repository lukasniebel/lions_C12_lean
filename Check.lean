module

public import LionsC12

/-!
# Release surface

A curated tour of the development: the statement layer and the two headline theorems first, then
the principal results of each section of the paper, then Lions' theorem.  This is not a log of
everything that is proved — that is `LionsC12/AxiomAudit.lean`, which inspects every theorem of the
library.

`scripts/audit.sh` elaborates this file with `-D warningAsError=true`, so it doubles as the
warning-clean smoke test of the public API: this file is outside the Lake libraries, so that step is
the only one that compiles it.  The gate also requires every `#check`ed name below to appear in
`scripts/audited-declarations.txt`, hence to carry a `#print axioms` report.  The `#print` commands
interleaved with the `#check`s of statement-level definitions are not cross-checked against that
list: they are there so that a reader of this file alone sees what each definition unfolds to.
-/

-- --------------------------------------------------------------------------
-- 1. The statement layer and the main results (Section 1)
-- --------------------------------------------------------------------------

-- `H¹₀(U;ℂ)` as the closure of the graphs of `C¹_c` functions, its anti-dual, the forms, and the
-- Lions variational solutions (`LionsC12/Paper/Statement.lean`, repeated in `Challenge.lean`).
#print LionsC12Challenge.H10Graph
#print LionsC12Challenge.form
#print LionsC12Challenge.HasWeakDeriv
#print LionsC12Challenge.IsLionsSolution
#print LionsC12Challenge.formΩ
#print LionsC12Challenge.IsLionsSolutionΩ
-- Theorem 1.1: the counterexample on an interval, with the statement of `Challenge.lean`.
#check LionsC12.lions_counterexample_interval
-- Corollary 1.2: the counterexample on every bounded domain of every dimension ...
#check LionsC12.lions_counterexample_domain
-- ... which holds on every non-empty open set.
#check LionsC12.lions_counterexample_open

-- --------------------------------------------------------------------------
-- 2. Spatial oscillatory modes (Section 2)
-- --------------------------------------------------------------------------

-- Lemma 2.1 in the paper's spaces, with `‖p_K‖_{V'} ≤ 6/K`.
#check LionsC12.lemma_2_1
#check LionsC12.norm_p_Hm1_le
-- Identity (2.4): the coefficient acting on the profile.
#check LionsC12.hasDerivAt_coeff_profile

-- --------------------------------------------------------------------------
-- 3. The coefficient (Section 3)
-- --------------------------------------------------------------------------

-- The reciprocal sums (3.1).
#check LionsC12.S_le
#check LionsC12.M_mul_S_le
-- Proposition 3.2: `|𝔞 − 1| ≤ ε/480` and the ½-Hölder bound, pointwise and in `L^∞`.
#check LionsC12.abs_a_sub_one_le
#check LionsC12.abs_a_sub_le
#check LionsC12.eLpNorm_a_sub_le
-- Proposition 3.3: no `α`-Hölder bound for `1/2 < α < 1`.
#check LionsC12.not_holder
#check LionsC12.not_holder_Linfty
-- Proposition 3.4: a common operator domain without uniform graph control.
#check LionsC12.domain_eq
#check LionsC12.exists_bound_on_D₀
#check LionsC12.not_uniform_bound_on_D₀

-- --------------------------------------------------------------------------
-- 4. The solution and its time derivative (Section 4)
-- --------------------------------------------------------------------------

-- Lemma 4.1: `u ∈ C([0,1];V) ∩ C¹([0,1];V') ∩ W^{1,1}(0,1;H)`, `u(0) = 0`, `∂ₜu ∉ L²(0,1;H)`.
#check LionsC12.continuous_uV
#check LionsC12.hasDerivAt_ofH10_uV
#check LionsC12.hasWeakDeriv_val_uV
#check LionsC12.integrableOn_utH
#check LionsC12.not_exists_L2_rep_uV'

-- --------------------------------------------------------------------------
-- 5. Cancellation and the forcing (Section 5)
-- --------------------------------------------------------------------------

-- The exact cancellation (5.2) and the equation pointwise.
#check LionsC12.mode_cancellation
#check LionsC12.pde
-- Proposition 5.1: `f ∈ C([0,1];H)` and the equation in `V'` for every `t`.
#check LionsC12.continuous_fH
#check LionsC12.equation_uV
-- `u` is the unique Lions solution; `u(t) ∈ D(A_H(t))`; `A_H(·)u(·) ∈ L¹ ∖ L²`.
#check LionsC12.isLionsSolution_uV
#check LionsC12.eq_uV_of_isLionsSolution
#check LionsC12.form_uV
#check LionsC12.AH_u_L1_not_L2
-- Remark 5.2: the truncations have maximal `L²`-regularity, and their maximal-regularity
-- constants grow like `√log N`.
#print LionsC12.IsMaxRegConstant
#check LionsC12.maxRegConstant_growth
#check LionsC12.truncation_maximal_regularity
#check LionsC12.truncation_maxReg_growth

-- --------------------------------------------------------------------------
-- 6. Full-space and bounded-domain consequences (Section 6)
-- --------------------------------------------------------------------------

-- Lemma 6.1: the zero extension of a vanishing flux.
#check LionsC12.zero_extension_flux
-- The weak form on the line and the tensorisation.
#check LionsC12.weak1D
#check LionsC12.tensorΩ_weak
-- Propositions 6.2 and 6.3 in the paper's spaces, with every clause of Corollary 1.2 on `ℝ^d`.
#check LionsC12.lions_counterexample_fullspace
-- The rescaled construction satisfies every clause of Corollary 1.2.
#check LionsC12.domainClauses_of_params

-- --------------------------------------------------------------------------
-- 7. Endpoint hypotheses (Section 7)
-- --------------------------------------------------------------------------

-- `‖𝒜(t) − 𝒜(s)‖_{L(V,V')} = ‖𝔞(t) − 𝔞(s)‖_{L^∞}`.
#check LionsC12.formOpDist_eq_eLpNorm
#check LionsC12.formOpDist_a
-- Corollary 7.1, bundled, and its parts (i)–(iv).
#check LionsC12.endpoint_hypotheses_fail
#check LionsC12.eVariationOn_aX_eq_top
#check LionsC12.not_exists_dier_bound
#check LionsC12.dini_form_lintegral_eq_top
#check LionsC12.exists_piece_gagliardo_eq_top
#check LionsC12.not_exists_auscherEgert_bound

-- --------------------------------------------------------------------------
-- 8. Lions' theorem
-- --------------------------------------------------------------------------

-- On real Gelfand triples: existence, the Lions–Magenes identity, uniqueness.
#check LionsC12.lions_existence
#check LionsC12.lions_existence_garding
#check LionsC12.lions_magenes
#check LionsC12.lions_theorem
-- Uniqueness in the paper's complex spaces, by realification.
#check LionsC12.IsLionsSol.ae_eq
#check LionsC12.isLionsSolution_unique
#check LionsC12.isLionsSolutionΩ_unique
