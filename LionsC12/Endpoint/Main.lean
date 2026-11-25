module

public import LionsC12.Endpoint.BV
public import LionsC12.Endpoint.Dini
public import LionsC12.Endpoint.Gagliardo
public import LionsC12.Endpoint.Smallness

/-!
# Corollary 7.1: failure of the known sufficient hypotheses at the endpoint

The bundled statement `LionsC12.endpoint_hypotheses_fail` of Section 7 of the paper, for the
coefficient `𝔞 = a D ε` (every choice of cutoffs `D`, every `0 < ε ≤ 1`), `X = L^∞(0,π)`,
`V = H¹₀(0,π)` with its graph norm and the forms `𝔞(t)[v,w]` of `LionsC12.Paper.Statement`.

The paper obtains (i)–(iv) by contradiction: each hypothesis is sufficient for maximal
`L²`-regularity by a theorem in the literature (Dier; Haak–Ouhabaz; Achache–Ouhabaz;
Auscher–Egert), and maximal regularity fails by the main theorem.  **Those sufficiency theorems
are not formalised.**  Instead, the failure of each hypothesis is proved directly from the
construction (files `LionsC12/Endpoint/*.lean`).
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped ENNReal NNReal

/-- **Corollary 7.1 (failure of the known sufficient hypotheses at the endpoint).**

Let `D` be the cutoff data, `0 < ε ≤ 1`, `𝔞 = a D ε`, `X = L^∞(0,π)`, `V = H¹₀(0,π)` with
the graph norm, and `𝔞(t)[v,w] = form (Ioo 0 π) (a D ε) t v w`.  Then:

* **(0)** `‖𝒜(t) − 𝒜(s)‖_{L(V,V')} = ‖𝔞(t) − 𝔞(s)‖_X`, where the operator norm is
  `formOpDist` (the supremum of `|𝔞(t)[v,w] − 𝔞(s)[v,w]|/(‖v‖ ‖w‖)` over `v, w ≠ 0`) and the
  `X`-norm is the essential supremum on `(0,π)` (`eLpNorm · ∞`);
* **(i)** `𝔞 ∉ BV([0,1]; X)`: the total variation of `t ↦ [𝔞(t)] ∈ Lp ℝ ∞` on `[0,1]` is `∞`;
  and there is no nondecreasing `g` on `[0,1]` with
  `|𝔞(t)[v,w] − 𝔞(s)[v,w]| ≤ (g(t) − g(s)) ‖v‖ ‖w‖` for `0 ≤ s ≤ t ≤ 1` (Dier, Thm 4.1);
* **(ii)** there is no nondecreasing `ω : [0,1] → [0,∞)` with
  `|𝔞(t)[v,w] − 𝔞(s)[v,w]| ≤ ω(|t − s|) ‖v‖ ‖w‖` on `[0,1]` and
  `∫₀¹ ω(r) r^{−3/2} dr < ∞` (Haak–Ouhabaz, Thm 1.2), nor one with
  `‖𝔞(t) − 𝔞(s)‖_X ≤ ω(|t − s|)`;
* **(iii)** for every finite partition `0 = t₀ < t₁ < … < t_N = 1` some piece `(t_k, t_{k+1})`
  has infinite Gagliardo seminorms
  `∫∫ ‖𝔞(t) − 𝔞(s)‖²_X / |t − s|² = ∞` and `∫∫ ‖𝒜(t) − 𝒜(s)‖²_{L(V,V')} / |t − s|² = ∞`:
  neither `𝔞` nor `𝒜` is piecewise `H^{1/2}` (Achache–Ouhabaz, Thm 2.2);
* **(iv)** there is no `M < ∞` with
  `sup_{I ⊆ [0,1], |I| > 0} |I|⁻¹ ∫∫_{I×I} |𝔞(t,x) − 𝔞(s,x)|²/|t − s|² ≤ M` for a.e.
  `x ∈ (0,π)` (Auscher–Egert, Thm 2, condition (8));
* **(5)** the positive side conditions of Achache–Ouhabaz hold: local smallness
  `sup_{t ∈ I} ∫_I ‖𝒜(t) − 𝒜(s)‖²_{L(V,V')}/|t − s| ds ≤ 4 C_β² ε² |I|` for every interval
  `I = (p,q)`, and the uniform form equivalence
  `(479/480) ‖∂ₓv‖² ≤ Re 𝔞(t)[v,v] ≤ (481/480) ‖∂ₓv‖²`.

All integrals are lower Lebesgue integrals in `ℝ≥0∞` (`0/0 = 0` on the diagonal), so no
integrability side conditions are imposed; intervals are open.

**The sufficiency theorems of Dier, Haak–Ouhabaz, Achache–Ouhabaz and Auscher–Egert, through
which the paper deduces (i)–(iv) from the main theorem, are not formalised; the failure of their
hypotheses is proved directly from the construction.**  The operator square root in the Kato
property is not formalised either; only its form part is stated. -/
theorem endpoint_hypotheses_fail (D : Cutoffs) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    -- (0) the operator norm of the increments
    (∀ t s : ℝ, formOpDist (Ioo 0 π) (a D ε) t s =
      eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π))) ∧
    -- (i) unbounded variation, and no Dier bound
    eVariationOn (aX D ε) (Icc 0 1) = ⊤ ∧
    (¬ ∃ g : ℝ → ℝ, MonotoneOn g (Icc 0 1) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → ∀ v w : H10 (Ioo 0 π),
        ‖form (Ioo 0 π) (a D ε) t v w -
            form (Ioo 0 π) (a D ε) s v w‖ ≤ (g t - g s) * ‖v‖ * ‖w‖) ∧
    -- (ii) no Dini modulus, for the forms and for the coefficient
    (¬ ∃ ω : ℝ → ℝ, MonotoneOn ω (Icc 0 1) ∧ (∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ ω r) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ v w : H10 (Ioo 0 π),
        ‖form (Ioo 0 π) (a D ε) t v w -
            form (Ioo 0 π) (a D ε) s v w‖ ≤ ω |t - s| * ‖v‖ * ‖w‖) ∧
      ∫⁻ r in Ioo 0 1, ENNReal.ofReal (ω r / r ^ ((3 : ℝ) / 2)) < ⊤) ∧
    (¬ ∃ ω : ℝ → ℝ, MonotoneOn ω (Icc 0 1) ∧ (∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ ω r) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖aX D ε t - aX D ε s‖ ≤ ω |t - s|) ∧
      ∫⁻ r in Ioo 0 1, ENNReal.ofReal (ω r / r ^ ((3 : ℝ) / 2)) < ⊤) ∧
    -- (iii) no partition into `H^{1/2}` pieces
    (∀ (N : ℕ) (u : Fin (N + 1) → ℝ), StrictMono u → u 0 = 0 → u (Fin.last N) = 1 →
      ∃ k : Fin N,
        ∫⁻ t in Ioo (u k.castSucc) (u k.succ), ∫⁻ s in Ioo (u k.castSucc) (u k.succ),
          eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π)) ^ 2 /
            ENNReal.ofReal ((t - s) ^ 2) = ⊤ ∧
        ∫⁻ t in Ioo (u k.castSucc) (u k.succ), ∫⁻ s in Ioo (u k.castSucc) (u k.succ),
          formOpDist (Ioo 0 π) (a D ε) t s ^ 2 / ENNReal.ofReal ((t - s) ^ 2) = ⊤) ∧
    -- (iv) no Auscher–Egert bound
    (¬ ∃ Mb : ℝ≥0∞, Mb < ⊤ ∧ ∀ᵐ x ∂(volume.restrict (Ioo 0 π)),
      (⨆ (p : ℝ) (q : ℝ) (_ : 0 ≤ p) (_ : p < q) (_ : q ≤ 1),
        (ENNReal.ofReal (q - p))⁻¹ * ∫⁻ t in Ioo p q, ∫⁻ s in Ioo p q,
          ENNReal.ofReal ((a D ε t x - a D ε s x) ^ 2 / (t - s) ^ 2)) ≤ Mb) ∧
    -- (5) local smallness and the uniform form equivalence
    (∀ p q : ℝ, ⨆ t ∈ Ioo p q, ∫⁻ s in Ioo p q,
        formOpDist (Ioo 0 π) (a D ε) t s ^ 2 / ENNReal.ofReal |t - s| ≤
      ENNReal.ofReal (4 * Cβ D ^ 2 * ε ^ 2 * (q - p))) ∧
    (∀ (t : ℝ) (v : H10 (Ioo 0 π)),
      479 / 480 * ‖dx (Ioo 0 π) v‖ ^ 2 ≤ (form (Ioo 0 π) (a D ε) t v v).re ∧
        (form (Ioo 0 π) (a D ε) t v v).re ≤
          481 / 480 * ‖dx (Ioo 0 π) v‖ ^ 2) :=
  ⟨fun t s => formOpDist_a D ε t s,
    eVariationOn_aX_eq_top D hε0,
    not_exists_dier_bound D hε0,
    not_exists_dini_form D hε0,
    not_exists_dini_coeff D hε0,
    fun _ u _ h0 h1 => by
      obtain ⟨k, hk⟩ := exists_piece_gagliardo_eq_top D hε0 u h0 h1
      exact ⟨k, hk, by rw [← gagliardoForm_eq] at hk; exact hk⟩,
    not_exists_auscherEgert_bound D hε0,
    fun p q => iSup_lintegral_formOpDist_sq_div_le D hε0.le p q,
    fun t v => form_self_re_equiv D hε0.le hε1 t v⟩

end LionsC12
