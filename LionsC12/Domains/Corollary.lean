module

public import LionsC12.Domains.Main

/-!
# Corollary 1.2 of the paper in the paper's Hilbert spaces

* `DomainClauses` — the conjunction of the clauses of Corollary 1.2, verbatim from the statement
  of `LionsC12Challenge.lions_counterexample_domain`;
* `domainClauses_of_params` — the construction of `LionsC12.Domains.Equation` satisfies them, for
  every choice of parameters `0 < ε ≤ 1`, `0 < r ≤ 1`, `p ∈ Ω`, `closedBall p (r(π+1)) ⊆ Ω` with
  `ε/480 + 2εC_β/r < δ`;
* `lions_counterexample_open` — Corollary 1.2 on every nonempty open `Ω ⊆ ℝ^d`, `d ≥ 1`;
* `lions_counterexample_domain` — **Corollary 1.2**, with the statement of
  `LionsC12Challenge.lions_counterexample_domain` character for character (boundedness of `Ω` is
  not needed);
* `lions_counterexample_fullspace` — Propositions 6.2/6.3 in Hilbert form: on `Ω = ℝ^{n+1}`
  without rescaling, `𝔟(t,x) = 𝔞(t,x₁)` and `U(t) = ũ(t) ⊗ χ`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped InnerProductSpace ComplexConjugate ENNReal

/-- The clauses of Corollary 1.2 (verbatim from `LionsC12Challenge.lions_counterexample_domain`)
for given `𝔟`, `F`, `U`, `U'`. -/
def DomainClauses (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (δ : ℝ)
    (𝔟 : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (F : ℝ → L2Ω d Ω) (U : ℝ → H10Ω d Ω)
    (U' : ℝ → Hm1Ω d Ω) : Prop :=
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
          formΩ d Ω 𝔟 t (U t) w = ofL2Ω d Ω (g t) w

theorem domainClauses_of_params {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩ : IsOpen Ω) (D : Cutoffs) (P : DomParams n Ω) (hp : P.p ∈ Ω) (hr1 : P.r ≤ 1)
    (hε : 0 < P.ε) {δ : ℝ} (hδ : P.ε / 480 + 2 * |P.ε| * Cβ D / P.r < δ) :
    DomainClauses (n + 1) Ω δ (dB D P) (dF D P) (dU D P) (dU' D P) := by
  refine ⟨(continuous_domB D P.ε P.p).measurable, ⟨479 / 480, 481 / 480, by norm_num,
    dB_bounds D P⟩, fun t x => isSelfAdjoint_smul_id _, ⟨479 / 480, by norm_num, ?_⟩,
    ⟨P.ε / 480, 2 * |P.ε| * Cβ D / P.r, div_nonneg P.hε0 (by norm_num),
      div_nonneg (mul_nonneg (mul_nonneg zero_le_two (abs_nonneg _)) (Cβ_nonneg D)) P.hr.le, hδ,
      fun t _ => eLpNorm_isoCoeff_sub_id_le D P t,
      fun s _ t _ => eLpNorm_isoCoeff_sub_le D P s t⟩,
    fun α hα hα1 => not_holder_dB D P hΩ hp hr1 hε hα hα1,
    (continuous_dF D P).continuousOn, memLp_Ioo01_of_continuous (continuous_dF D P),
    im_dF D P, (continuous_dU D P).continuousOn,
    fun t _ => (hasDerivAt_ofH10_dU D P t).hasDerivWithinAt, (continuous_dU' D P).continuousOn,
    integrableOn_Ioo01_of_continuous (continuous_val_dU D P),
    ⟨dG D P, integrableOn_dG D P, hasWeakDeriv_val_dU D P⟩, im_val_dU D P, dU_zero D P,
    fun t _ w => equation_dU D P t w, isLionsSolutionΩ_dU D P,
    fun W hW => isLionsSolutionΩ_unique hΩ (isBoundedCoeffΩ_dB D P)
      (fun t x => le_trans (by norm_num) (dB_bounds D P t x).1) hW (isLionsSolutionΩ_dU D P),
    not_exists_L2_dU' D P hΩ hr1 hε, not_exists_L2_form D P hΩ hr1 hε⟩
  intro t x ξ
  have e : ⟪isoCoeff (dB D P) t x ξ, ξ⟫_ℝ = dB D P t x * ‖ξ‖ ^ 2 := by
    simp [isoCoeff, real_inner_smul_left]
  rw [e]
  exact mul_le_mul_of_nonneg_right (dB_bounds D P t x).1 (sq_nonneg _)

/-- The choice of `ε` in terms of `δ` and `r`. -/
theorem exists_eps (D : Cutoffs) {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε / 480 + 2 * |ε| * Cβ D / r < δ := by
  have hCβ : 0 ≤ Cβ D := Cβ_nonneg D
  set ε : ℝ := min 1 (δ * r / (2 * (1 + 2 * Cβ D))) with hεdef
  have hεpos : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεδ : ε ≤ δ * r / (2 * (1 + 2 * Cβ D)) := min_le_right _ _
  refine ⟨ε, hεpos, hε1, ?_⟩
  rw [abs_of_pos hεpos]
  have h1 : ε * (1 + 2 * Cβ D) / r ≤ δ / 2 := by
    have hpos : 0 < 2 * (1 + 2 * Cβ D) := by positivity
    rw [div_le_iff₀ hr]
    calc ε * (1 + 2 * Cβ D) ≤ δ * r / (2 * (1 + 2 * Cβ D)) * (1 + 2 * Cβ D) := by gcongr
      _ = δ / 2 * r := by field_simp
  have h2 : ε / 480 + 2 * ε * Cβ D / r ≤ ε * (1 + 2 * Cβ D) / r := by
    have : ε / 480 ≤ ε / r := by
      apply div_le_div_of_nonneg_left hεpos.le hr
      linarith
    have h3 : ε / r + 2 * ε * Cβ D / r = ε * (1 + 2 * Cβ D) / r := by ring
    linarith
  linarith

/-- **Corollary 1.2 on every nonempty open set** `Ω ⊆ ℝ^d`, `d ≥ 1`. -/
theorem lions_counterexample_open (d : ℕ) (hd : 1 ≤ d) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hΩ : IsOpen Ω) (hΩne : Ω.Nonempty) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (𝔟 : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (F : ℝ → L2Ω d Ω) (U : ℝ → H10Ω d Ω)
      (U' : ℝ → Hm1Ω d Ω), DomainClauses d Ω δ 𝔟 F U U' := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨p, hp⟩ := hΩne
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hΩ p hp
  have hπ1 : 0 < π + 1 := by positivity
  set r : ℝ := min 1 (ρ / (2 * (π + 1))) with hrdef
  have hr : 0 < r := lt_min one_pos (by positivity)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hK : domK r p ⊆ Ω := by
    refine (Metric.closedBall_subset_ball ?_).trans hball
    have h1 : r ≤ ρ / (2 * (π + 1)) := min_le_right _ _
    calc r * (π + 1) ≤ ρ / (2 * (π + 1)) * (π + 1) := by gcongr
      _ = ρ / 2 := by field_simp
      _ < ρ := by linarith
  obtain ⟨D⟩ := Cutoffs.nonempty
  obtain ⟨ε, hε, hε1, hεδ⟩ := exists_eps D hδ hr hr1
  let P : DomParams n Ω := ⟨ε, r, p, hε.le, hε1, hr, hK⟩
  exact ⟨dB D P, dF D P, dU D P, dU' D P, domainClauses_of_params hΩ D P hp hr1 hε hεδ⟩

/-- **Corollary 1.2 of Niebel, arXiv:2608.11194v2**, with the statement of
`LionsC12Challenge.lions_counterexample_domain`. -/
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
          formΩ d Ω 𝔟 t (U t) w = ofL2Ω d Ω (g t) w := by
  -- the boundedness of `Ω` is not needed
  have _ := hΩb
  obtain ⟨𝔟, F, U, U', h⟩ := lions_counterexample_open d hd Ω hΩ hΩne δ hδ
  exact ⟨𝔟, F, U, U', h⟩

/-! ### The full space: Propositions 6.2 and 6.3 in Hilbert form -/

theorem Qr_one_zero {n : ℕ} : Qr 1 (0 : EuclideanSpace ℝ (Fin (n + 1))) = ⇑(bumpE n) := by
  funext y
  simp [Qr]

/-- **Propositions 6.2/6.3 in the paper's Hilbert spaces** (`d = n + 1`, `Ω = ℝ^d`): without any
rescaling, the coefficient `𝔟(t,x) = 𝔞(t,x₁)`, the solution `U(t) = ũ(t) ⊗ χ` (`ũ` the zero
extension of the interval solution, `χ` a bump on `ℝ^n`) and the forcing
`F(t) = f̃(t) ⊗ χ - 𝔞 ũ(t) ⊗ Δχ` satisfy every clause of Corollary 1.2 on `ℝ^d`: `U` is the
unique Lions solution, `F ∈ C([0,1];L²(ℝ^d)) ∩ L²(0,1;L²(ℝ^d))`, `U ∈ C([0,1];H¹₀(ℝ^d)) ∩
C¹([0,1];H⁻¹(ℝ^d)) ∩ W^{1,1}(0,1;L²(ℝ^d))`, but `U' ∉ L²(0,1;L²(ℝ^d))`. -/
theorem lions_counterexample_fullspace (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (D : Cutoffs) (ε : ℝ), 0 < ε ∧ ε ≤ 1 ∧
      ∃ (𝔟 : ℝ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (F : ℝ → L2Ω (n + 1) univ)
        (U : ℝ → H10Ω (n + 1) univ) (U' : ℝ → Hm1Ω (n + 1) univ),
        DomainClauses (n + 1) univ δ 𝔟 F U U' ∧
        (∀ t x, 𝔟 t x = a D ε t (x 0)) ∧
        (∀ t, ∀ᵐ x ∂volume, valΩ (n + 1) univ (U t) x
          = ((uZ D ε t (x 0) * bumpE n (tailL n x) : ℝ) : ℂ)) ∧
        (∀ t, ∀ᵐ x ∂volume, F t x
          = ((fZ D ε t (x 0) * bumpE n (tailL n x)
            - a D ε t (x 0) * uZ D ε t (x 0) * lapQ (bumpE n) (tailL n x) : ℝ) : ℂ)) := by
  obtain ⟨D⟩ := Cutoffs.nonempty
  obtain ⟨ε, hε, hε1, hεδ⟩ := exists_eps D hδ one_pos le_rfl
  let P : DomParams n univ := ⟨ε, 1, 0, hε.le, hε1, one_pos, subset_univ _⟩
  have hb : ∀ t x, dB D P t x = a D ε t (x 0) := fun t x => by
    simp [P, dB, domB, bR]
  refine ⟨D, ε, hε, hε1, dB D P, dF D P, dU D P, dU' D P,
    domainClauses_of_params isOpen_univ D P (mem_univ _) le_rfl hε hεδ, hb, fun t => ?_,
    fun t => ?_⟩
  · have h := (ae_restrict_iff' MeasurableSet.univ).1 (coe_val_dU D P t)
    filter_upwards [h] with x hx
    rw [hx (mem_univ x)]
    simp [P, domW, tens, UR, Qr_one_zero]
  · have h := (ae_restrict_iff' MeasurableSet.univ).1 (coe_dF D P t)
    filter_upwards [h] with x hx
    rw [hx (mem_univ x), domF, tens]
    have hQ : Qr P.r P.p = ⇑(bumpE n) := Qr_one_zero
    rw [hQ]
    simp [P, FR, UR, bR]

end LionsC12
