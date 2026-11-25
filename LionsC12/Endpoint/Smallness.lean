module

public import LionsC12.Endpoint.Coefficient

/-!
# The positive side conditions: local smallness and uniform form equivalence

The two side conditions of Achache–Ouhabaz [Theorem 2.2] that the paper verifies in the proof
of Corollary 7.1(iii) do hold for the construction:

* `lintegral_formOpDist_sq_div_le` — **local smallness**: for every interval `I = (p,q)` and
  every `t`,
  `∫_I ‖𝒜(t) − 𝒜(s)‖²_{L(V,V')} / |t − s| ds ≤ 4 C_β² ε² |I|`,
  from the `½`-Hölder bound of Proposition 3.2 (`eLpNorm_a_sub_le`) and
  `‖𝒜(t) − 𝒜(s)‖_{L(V,V')} = ‖𝔞(t) − 𝔞(s)‖_{L^∞}`; `C_β` depends only on the cutoff `η`.
  Consequently (`exists_partition_local_smallness`) a sufficiently fine uniform partition of
  `[0,1]` makes this quantity smaller than any prescribed `δ > 0` on every piece.
* `form_self_re_equiv` — **uniform form equivalence** (the form part of the uniform Kato
  square-root property): `(479/480) ‖∂ₓv‖² ≤ Re 𝔞(t)[v,v] ≤ (481/480) ‖∂ₓv‖²` for all `t`
  and `v ∈ V = H¹₀(0,π)`, for `0 ≤ ε ≤ 1`.  The identification
  `‖A_H(t)^{1/2} v‖² = 𝔞(t)[v,v]` is the spectral theorem for the self-adjoint realisation;
  the operator square root is not available in mathlib and is not formalised.

The integrals are lower Lebesgue integrals in `ℝ≥0∞`, with `0/0 = 0` at `s = t`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped ENNReal NNReal

variable (D : Cutoffs)

/-- The squared operator increment is `≤ 4 C_β² ε² |t − s|`. -/
theorem formOpDist_sq_le {ε : ℝ} (hε : 0 ≤ ε) (t s : ℝ) :
    formOpDist (Ioo 0 π) (a D ε) t s ^ 2 ≤ ENNReal.ofReal (4 * Cβ D ^ 2 * ε ^ 2 * |t - s|) := by
  rw [formOpDist_a]
  have h := eLpNorm_a_sub_le D hε s t
  calc eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π)) ^ 2
      ≤ ENNReal.ofReal (2 * ε * Cβ D * |t - s| ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = ENNReal.ofReal (4 * Cβ D ^ 2 * ε ^ 2 * |t - s|) := by
        rw [← ENNReal.ofReal_pow (by have := Cβ_nonneg D; positivity)]
        congr 1
        have hsq : (|t - s| ^ (1 / 2 : ℝ)) ^ 2 = |t - s| := by
          rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (abs_nonneg _)]
        rw [show (2 * ε * Cβ D * |t - s| ^ (1 / 2 : ℝ)) ^ 2
            = 4 * Cβ D ^ 2 * ε ^ 2 * (|t - s| ^ (1 / 2 : ℝ)) ^ 2 by ring, hsq]

/-- **Local smallness** (condition (2.1) of Achache–Ouhabaz): for every interval `I = (p,q)` and
every `t`, `∫_I ‖𝒜(t) − 𝒜(s)‖²_{L(V,V')} / |t − s| ds ≤ 4 C_β² ε² |I|`. -/
theorem lintegral_formOpDist_sq_div_le {ε : ℝ} (hε : 0 ≤ ε) (p q t : ℝ) :
    ∫⁻ s in Ioo p q, formOpDist (Ioo 0 π) (a D ε) t s ^ 2 / ENNReal.ofReal |t - s| ≤
      ENNReal.ofReal (4 * Cβ D ^ 2 * ε ^ 2 * (q - p)) := by
  have hpt : ∀ s, formOpDist (Ioo 0 π) (a D ε) t s ^ 2 / ENNReal.ofReal |t - s| ≤
      ENNReal.ofReal (4 * Cβ D ^ 2 * ε ^ 2) := by
    intro s
    rcases eq_or_ne t s with rfl | _
    · rw [formOpDist_a]
      simp
    refine ENNReal.div_le_of_le_mul ?_
    rw [← ENNReal.ofReal_mul (by have := Cβ_nonneg D; positivity)]
    exact formOpDist_sq_le D hε t s
  calc ∫⁻ s in Ioo p q, formOpDist (Ioo 0 π) (a D ε) t s ^ 2 / ENNReal.ofReal |t - s|
      ≤ ∫⁻ _ in Ioo p q, ENNReal.ofReal (4 * Cβ D ^ 2 * ε ^ 2) := lintegral_mono hpt
    _ = ENNReal.ofReal (4 * Cβ D ^ 2 * ε ^ 2 * (q - p)) := by
        rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]

/-- Local smallness with the supremum over `t ∈ I`. -/
theorem iSup_lintegral_formOpDist_sq_div_le {ε : ℝ} (hε : 0 ≤ ε) (p q : ℝ) :
    ⨆ t ∈ Ioo p q, ∫⁻ s in Ioo p q,
        formOpDist (Ioo 0 π) (a D ε) t s ^ 2 / ENNReal.ofReal |t - s| ≤
      ENNReal.ofReal (4 * Cβ D ^ 2 * ε ^ 2 * (q - p)) :=
  iSup₂_le fun t _ => lintegral_formOpDist_sq_div_le D hε p q t

/-- A sufficiently fine uniform partition `t_k = k/N` of `[0,1]` makes the local quantity
`sup_{t ∈ I} ∫_I ‖𝒜(t) − 𝒜(s)‖²/|t − s| ds` smaller than any `δ > 0` on every piece. -/
theorem exists_partition_local_smallness {ε : ℝ} (hε : 0 ≤ ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∀ k : ℕ, k < N →
      ⨆ t ∈ Ioo ((k : ℝ) / N) ((k + 1 : ℝ) / N), ∫⁻ s in Ioo ((k : ℝ) / N) ((k + 1 : ℝ) / N),
          formOpDist (Ioo 0 π) (a D ε) t s ^ 2 / ENNReal.ofReal |t - s| ≤ ENNReal.ofReal δ := by
  set C := 4 * Cβ D ^ 2 * ε ^ 2 with hC
  have hC0 : 0 ≤ C := by have := Cβ_nonneg D; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (C / δ)
  have hN0 : 0 < N := by
    have : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    exact_mod_cast this
  refine ⟨N, hN0, fun k _ => (iSup_lintegral_formOpDist_sq_div_le D hε _ _).trans ?_⟩
  refine ENNReal.ofReal_le_ofReal ?_
  have hN0' : (0 : ℝ) < N := by exact_mod_cast hN0
  rw [show ((k + 1 : ℝ) / N - k / N) = 1 / N by field_simp; ring, ← hC]
  rw [div_lt_iff₀ hδ] at hN
  rw [mul_one_div, div_le_iff₀ hN0']
  linarith

/-- **Uniform form equivalence** (the form part of the uniform Kato square-root property):
`(479/480) ‖∂ₓv‖² ≤ Re 𝔞(t)[v,v] ≤ (481/480) ‖∂ₓv‖²` for every `t` and `v ∈ V = H¹₀(0,π)`. -/
theorem form_self_re_equiv {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : ℝ) (v : H10 (Ioo 0 π)) :
    479 / 480 * ‖dx (Ioo 0 π) v‖ ^ 2 ≤ (form (Ioo 0 π) (a D ε) t v v).re ∧
      (form (Ioo 0 π) (a D ε) t v v).re ≤ 481 / 480 * ‖dx (Ioo 0 π) v‖ ^ 2 := by
  have hb := isBoundedCoeff_a D hε0 hε1 t
  refine ⟨form_self_re_ge hb (by norm_num) (a_ge D hε0 hε1 t) v, ?_⟩
  calc (form (Ioo 0 π) (a D ε) t v v).re
      ≤ ‖form (Ioo 0 π) (a D ε) t v v‖ := Complex.re_le_norm _
    _ ≤ 481 / 480 * ‖dx (Ioo 0 π) v‖ * ‖dx (Ioo 0 π) v‖ := norm_form_le hb v v
    _ = 481 / 480 * ‖dx (Ioo 0 π) v‖ ^ 2 := by ring

/-- The forms are uniformly bounded on `V`: `|𝔞(t)[v,w]| ≤ (481/480) ‖v‖_V ‖w‖_V`. -/
theorem norm_form_a_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : ℝ) (v w : H10 (Ioo 0 π)) :
    ‖form (Ioo 0 π) (a D ε) t v w‖ ≤ 481 / 480 * ‖v‖ * ‖w‖ :=
  (norm_form_le (isBoundedCoeff_a D hε0 hε1 t) v w).trans (by
    gcongr <;> [exact norm_dx_le v; exact norm_dx_le w])

end LionsC12
