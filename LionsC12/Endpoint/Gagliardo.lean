module

public import LionsC12.Endpoint.Coefficient
public import LionsC12.Endpoint.Rectangles
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.PSeries

/-!
# (iii) Not piecewise `H^{1/2}` and (iv) the Auscher–Egert square condition

Corollary 7.1(iii) and (iv) of the paper.

* (iii) `exists_piece_gagliardo_eq_top`, `exists_piece_gagliardo_form_eq_top`: for every finite
  partition `0 = t₀ < t₁ < … < t_N = 1` there is a piece `(t_{k}, t_{k+1})` on which the
  Gagliardo seminorm of the `W^{1/2,2}` space is infinite,
  `∫∫_{(t_k,t_{k+1})²} ‖𝔞(t) − 𝔞(s)‖²_{L^∞(0,π)} / |t − s|² ds dt = ∞`,
  and the same for `‖𝒜(t) − 𝒜(s)‖_{L(V,V')}`; so neither `𝔞 : [0,1] → L^∞(0,π)` nor
  `𝒜 : [0,1] → L(V,V')` is piecewise `H^{1/2}` on any finite partition, the hypothesis of
  Achache–Ouhabaz [Theorem 2.2].
* (iv) `not_exists_auscherEgert_bound`: there is no `M < ∞` such that for almost every
  `x ∈ (0,π)`, `sup_{I ⊆ [0,1]} |I|⁻¹ ∫∫_{I×I} |𝔞(t,x) − 𝔞(s,x)|²/|t − s|² ≤ M`, the
  scale-invariant square condition (8) of Auscher–Egert [Theorem 2].

The paper derives both from the main theorem and the cited sufficiency theorems.  Here they are
proved directly.  For `t, s ∈ J_j`, spatial orthogonality (`integral_a_sub_sq`) gives
`∫₀^π |𝔞(t,x) − 𝔞(s,x)|² dx = (π/2) ε² ∑_m K_{j,m}⁻² (sin θ_{j,m}(t) − sin θ_{j,m}(s))²`, and
`‖𝔞(t) − 𝔞(s)‖²_∞` is at least `1/π` times this.  Each mode contributes
`∫∫_{J×J} (sin θ_m(t) − sin θ_m(s))²/(t − s)² ≥ K_{j,m}² |J|/(36π)`
(`lintegral_sin_sub_sq_ge`), so block `j` contributes `≳ ε² M_j |J_j| ≍ ε²/(j+1)` to (iii)
and `≳ ε² M_j |J_j|` to the `x`-integral of the quantity in (iv) over `I = J_j`
(Tonelli).  The blocks accumulate at `5/16` from the left, and `M_j = j → ∞`.

All integrals are lower Lebesgue integrals in `ℝ≥0∞` (no integrability side conditions);
`0/0 = 0` on the diagonal `t = s`.  Intervals `I` are open, `I = (p,q)` with `0 ≤ p < q ≤ 1`;
open and closed intervals give the same integrals.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped ENNReal NNReal

variable (D : Cutoffs)

/-! ### Superadditivity of the lower Lebesgue integral -/

theorem sum_lintegral_le_lintegral_sum {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑ i ∈ s, f i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    calc ∫⁻ x, f i x ∂μ + ∑ j ∈ s, ∫⁻ x, f j x ∂μ
        ≤ ∫⁻ x, f i x ∂μ + ∫⁻ x, ∑ j ∈ s, f j x ∂μ := by gcongr
      _ ≤ ∫⁻ x, (f i x + ∑ j ∈ s, f j x) ∂μ := le_lintegral_add _ _
      _ = ∫⁻ x, ∑ j ∈ insert i s, f j x ∂μ := by
          congr 1; ext x; rw [Finset.sum_insert hi]

/-! ### The Gagliardo energy of one block -/

/-- The interior `(τ_j + ℓ_j/3, τ_j + 2ℓ_j/3)` of the middle third `J_j`. -/
def pJ (j : ℕ) : ℝ := τ j + ℓ j / 3

/-- The right end point of `J_j`. -/
def qJ (j : ℕ) : ℝ := τ j + 2 * ℓ j / 3

theorem Ioo_subset_J (j : ℕ) : Ioo (pJ j) (qJ j) ⊆ J j := Ioo_subset_Icc_self

theorem qJ_sub_pJ (j : ℕ) : qJ j - pJ j = ℓ j / 3 := by unfold pJ qJ; ring

theorem pJ_lt_qJ {j : ℕ} (hj : 1 ≤ j) : pJ j < qJ j := by
  have := ℓ_pos hj; unfold pJ qJ; linarith

/-- **Per block:** `∫∫_{J_j²} ∑_m K⁻²(sin θ_m(t) − sin θ_m(s))²/(t − s)² ≥ M_j |J_j|/(36π)`. -/
theorem lintegral_modeSq_ge {j : ℕ} (hj : 1 ≤ j) :
    ENNReal.ofReal (M j * (ℓ j / 3) / (36 * π)) ≤
      ∫⁻ t in Ioo (pJ j) (qJ j), ∫⁻ s in Ioo (pJ j) (qJ j),
        ENNReal.ofReal (modeSq j t s / (t - s) ^ 2) := by
  have hπ := pi_pos
  have hℓ := ℓ_pos hj
  -- split into modes
  have hsplit : ∀ t s : ℝ, ENNReal.ofReal (modeSq j t s / (t - s) ^ 2) =
      ∑ m ∈ Finset.Icc 1 (M j), ENNReal.ofReal ((((K j m : ℝ))⁻¹) ^ 2) *
        ENNReal.ofReal ((sin ((K j m : ℝ) ^ 2 * (t - τ j)) -
          sin ((K j m : ℝ) ^ 2 * (s - τ j))) ^ 2 / (t - s) ^ 2) := by
    intro t s
    rw [modeSq, Finset.sum_div, ENNReal.ofReal_sum_of_nonneg fun m _ => by positivity]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [θ]
    ring
  -- one mode
  have hmode : ∀ m ∈ Finset.Icc 1 (M j), ENNReal.ofReal (ℓ j / 3 / (36 * π)) ≤
      ∫⁻ t in Ioo (pJ j) (qJ j), ∫⁻ s in Ioo (pJ j) (qJ j),
        ENNReal.ofReal ((((K j m : ℝ))⁻¹) ^ 2) *
          ENNReal.ofReal ((sin ((K j m : ℝ) ^ 2 * (t - τ j)) -
            sin ((K j m : ℝ) ^ 2 * (s - τ j))) ^ 2 / (t - s) ^ 2) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    have hK : (512 : ℝ) ≤ (K j m : ℝ) := by exact_mod_cast K_ge hj hm1
    have hK0 : (0 : ℝ) < (K j m : ℝ) := by linarith
    have hKℓ : (K j m : ℝ) * ℓ j = 16 ^ m := K_mul_ℓ hj
    have h16 : (16 : ℝ) ≤ 16 ^ m := by
      calc (16 : ℝ) = 16 ^ 1 := (pow_one _).symm
        _ ≤ 16 ^ m := pow_le_pow_right₀ (by norm_num) hm1
    have hA : 8 * π ≤ (K j m : ℝ) ^ 2 * (qJ j - pJ j) := by
      rw [qJ_sub_pJ, show (K j m : ℝ) ^ 2 * (ℓ j / 3) = (K j m : ℝ) * ((K j m : ℝ) * ℓ j) / 3 by
        ring, hKℓ]
      nlinarith [pi_le_four]
    have hτ : τ j ≤ pJ j := by unfold pJ; linarith
    have key := lintegral_sin_sub_sq_ge (by positivity : (0 : ℝ) < (K j m : ℝ) ^ 2) hτ hA
    simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (ℓ j / 3 / (36 * π))
        = ENNReal.ofReal ((((K j m : ℝ))⁻¹) ^ 2) *
            ENNReal.ofReal ((K j m : ℝ) ^ 2 * (qJ j - pJ j) / (36 * π)) := by
          rw [← ENNReal.ofReal_mul (by positivity), qJ_sub_pJ]
          congr 1
          field_simp
      _ ≤ _ := by gcongr
  calc ENNReal.ofReal (M j * (ℓ j / 3) / (36 * π))
      = ∑ _m ∈ Finset.Icc 1 (M j), ENNReal.ofReal (ℓ j / 3 / (36 * π)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), Nat.add_sub_cancel]
        congr 1; ring
    _ ≤ ∑ m ∈ Finset.Icc 1 (M j), ∫⁻ t in Ioo (pJ j) (qJ j), ∫⁻ s in Ioo (pJ j) (qJ j),
          ENNReal.ofReal ((((K j m : ℝ))⁻¹) ^ 2) *
            ENNReal.ofReal ((sin ((K j m : ℝ) ^ 2 * (t - τ j)) -
              sin ((K j m : ℝ) ^ 2 * (s - τ j))) ^ 2 / (t - s) ^ 2) := Finset.sum_le_sum hmode
    _ ≤ ∫⁻ t in Ioo (pJ j) (qJ j), ∑ m ∈ Finset.Icc 1 (M j), ∫⁻ s in Ioo (pJ j) (qJ j),
          ENNReal.ofReal ((((K j m : ℝ))⁻¹) ^ 2) *
            ENNReal.ofReal ((sin ((K j m : ℝ) ^ 2 * (t - τ j)) -
              sin ((K j m : ℝ) ^ 2 * (s - τ j))) ^ 2 / (t - s) ^ 2) :=
        sum_lintegral_le_lintegral_sum _ _
    _ ≤ ∫⁻ t in Ioo (pJ j) (qJ j), ∫⁻ s in Ioo (pJ j) (qJ j),
          ENNReal.ofReal (modeSq j t s / (t - s) ^ 2) := by
        refine lintegral_mono fun t => ?_
        simp_rw [hsplit]
        exact sum_lintegral_le_lintegral_sum _ _

/-! ### (iii) Piecewise `H^{1/2}` -/

/-- On `J_j`: `ε²/2 · modeSq/(t − s)² ≤ ‖𝔞(t) − 𝔞(s)‖²_{L^∞}/(t − s)²` (with `0/0 = 0`). -/
theorem ofReal_modeSq_div_le {j : ℕ} (hj : 1 ≤ j) {t s : ℝ} (ht : t ∈ J j) (hs : s ∈ J j)
    (ε : ℝ) :
    ENNReal.ofReal (ε ^ 2 / 2) * ENNReal.ofReal (modeSq j t s / (t - s) ^ 2) ≤
      eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π)) ^ 2 /
        ENNReal.ofReal ((t - s) ^ 2) := by
  rcases eq_or_ne t s with rfl | hts
  · simp [modeSq]
  have hpos : 0 < (t - s) ^ 2 := by
    have : t - s ≠ 0 := sub_ne_zero.2 hts
    positivity
  rw [← ENNReal.ofReal_mul (by positivity), ← mul_div_assoc, ENNReal.ofReal_div_of_pos hpos]
  exact ENNReal.div_le_div_right (ofReal_modeSq_le_eLpNorm_sq D hj ht hs ε) _

/-- The Gagliardo `W^{1/2,2}` energy of the coefficient path on an interval `(p,q)`:
`∫∫_{(p,q)²} ‖𝔞(t) − 𝔞(s)‖²_{L^∞(0,π)} / |t − s|² ds dt ∈ [0,∞]`. -/
def gagliardoCoeff (ε p q : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo p q, ∫⁻ s in Ioo p q,
    eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π)) ^ 2 /
      ENNReal.ofReal ((t - s) ^ 2)

/-- The Gagliardo `W^{1/2,2}` energy of the operator path `t ↦ 𝒜(t) ∈ L(V,V')` on `(p,q)`:
`∫∫_{(p,q)²} ‖𝒜(t) − 𝒜(s)‖²_{L(V,V')} / |t − s|² ds dt ∈ [0,∞]`. -/
def gagliardoForm (ε p q : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo p q, ∫⁻ s in Ioo p q,
    formOpDist (Ioo 0 π) (a D ε) t s ^ 2 / ENNReal.ofReal ((t - s) ^ 2)

theorem gagliardoForm_eq (ε p q : ℝ) : gagliardoForm D ε p q = gagliardoCoeff D ε p q := by
  simp only [gagliardoForm, gagliardoCoeff, formOpDist_a]

/-- **Per block:** the Gagliardo energy of the coefficient on `J_j` is
`≥ ε² M_j |J_j| / (72π)`. -/
theorem gagliardo_J_ge {j : ℕ} (hj : 1 ≤ j) (ε : ℝ) :
    ENNReal.ofReal (ε ^ 2 / 2 * (M j * (ℓ j / 3) / (36 * π))) ≤
      gagliardoCoeff D ε (pJ j) (qJ j) := by
  rw [ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal (ε ^ 2 / 2) * ENNReal.ofReal (M j * (ℓ j / 3) / (36 * π))
      ≤ ENNReal.ofReal (ε ^ 2 / 2) * ∫⁻ t in Ioo (pJ j) (qJ j), ∫⁻ s in Ioo (pJ j) (qJ j),
          ENNReal.ofReal (modeSq j t s / (t - s) ^ 2) := by
        gcongr; exact lintegral_modeSq_ge hj
    _ = ∫⁻ t in Ioo (pJ j) (qJ j), ∫⁻ s in Ioo (pJ j) (qJ j),
          ENNReal.ofReal (ε ^ 2 / 2) * ENNReal.ofReal (modeSq j t s / (t - s) ^ 2) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1; ext t
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ gagliardoCoeff D ε (pJ j) (qJ j) := by
        refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
        refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
        exact ofReal_modeSq_div_le D hj (Ioo_subset_J j ht) (Ioo_subset_J j hs) ε

/-- Divergence of the tails of the harmonic series. -/
theorem exists_sum_Ico_inv_succ_gt (j₀ : ℕ) (C : ℝ) :
    ∃ n, j₀ ≤ n ∧ C < ∑ j ∈ Finset.Ico j₀ n, (1 : ℝ) / ((j : ℝ) + 1) := by
  have ht := Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop
    (C + ∑ j ∈ Finset.range j₀, (1 : ℝ) / ((j : ℝ) + 1))).exists_forall_of_atTop
  refine ⟨max n j₀, le_max_right _ _, ?_⟩
  have h := hn (max n j₀) (le_max_left _ _)
  rw [← Finset.sum_range_add_sum_Ico _ (le_max_right n j₀)] at h
  linarith

/-- The Gagliardo energy on an interval `(p,q)` with `p < 5/16 ≤ q` is infinite: it contains
all the middle thirds `J_j` with `τ_j ≥ p`. -/
theorem gagliardoCoeff_eq_top {ε : ℝ} (hε : 0 < ε) {p q : ℝ} (hp : p < 5 / 16)
    (hq : 5 / 16 ≤ q) : gagliardoCoeff D ε p q = ⊤ := by
  have hπ := pi_pos
  -- the blocks inside `(p, 5/16)`
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt (1 / (5 - 16 * p))
  have hj₀1 : 1 ≤ j₀ + 1 := by omega
  have hin : ∀ j, j₀ + 1 ≤ j → Ioo (pJ j) (qJ j) ⊆ Ioo p q := by
    intro j hj
    have hj1 : 1 ≤ j := by omega
    have hjr : (j₀ : ℝ) + 1 ≤ j := by exact_mod_cast hj
    have hτp : p ≤ τ j := by
      unfold τ
      have h5 : 0 < 5 - 16 * p := by linarith
      have : 1 / (5 - 16 * p) < j := by linarith
      rw [div_lt_iff₀ h5] at this
      have hj0 : (0 : ℝ) < j := by linarith
      rw [show (5 : ℝ) / 16 - 1 / (16 * j) = (5 * j - 1) / (16 * j) by field_simp,
        le_div_iff₀ (by positivity)]
      nlinarith
    intro x hx
    have h1 := (J_subset_I hj1 (Ioo_subset_J j hx))
    have h2 := τ_lt (j := j + 1) (by omega)
    exact ⟨lt_of_le_of_lt hτp h1.1, by linarith [h1.2]⟩
  refine ENNReal.eq_top_of_forall_nnreal_le fun C => ?_
  obtain ⟨n, hn, hsum⟩ := exists_sum_Ico_inv_succ_gt (j₀ + 1) (C * (3456 * π) / ε ^ 2)
  have hdisj : (↑(Finset.Ico (j₀ + 1) n) : Set ℕ).PairwiseDisjoint
      (fun j => Ioo (pJ j) (qJ j)) := by
    intro i hi i' hi' hii'
    have h1 : 1 ≤ i := by have := (Finset.mem_Ico.1 hi).1; omega
    have h1' : 1 ≤ i' := by have := (Finset.mem_Ico.1 hi').1; omega
    exact (I_disjoint hii').mono ((Ioo_subset_J i).trans (J_subset_I h1))
      ((Ioo_subset_J i').trans (J_subset_I h1'))
  have hval : ∀ j ∈ Finset.Ico (j₀ + 1) n, ε ^ 2 / 2 * (M j * (ℓ j / 3) / (36 * π)) =
      ε ^ 2 / (3456 * π) * (1 / ((j : ℝ) + 1)) := by
    intro j hj
    have hj1 : 1 ≤ j := by have := (Finset.mem_Ico.1 hj).1; omega
    have := M_mul_ℓ hj1
    rw [show (M j : ℝ) * (ℓ j / 3) = (M j * ℓ j) / 3 by ring, this]
    field_simp
    ring
  calc (C : ℝ≥0∞) = ENNReal.ofReal C := (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ ENNReal.ofReal (∑ j ∈ Finset.Ico (j₀ + 1) n,
          ε ^ 2 / 2 * (M j * (ℓ j / 3) / (36 * π))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Finset.sum_congr rfl hval, ← Finset.mul_sum]
        rw [div_lt_iff₀ (by positivity)] at hsum
        have e : ε ^ 2 / (3456 * π) * ∑ j ∈ Finset.Ico (j₀ + 1) n, (1 : ℝ) / ((j : ℝ) + 1)
            = (∑ j ∈ Finset.Ico (j₀ + 1) n, (1 : ℝ) / ((j : ℝ) + 1)) * ε ^ 2 / (3456 * π) := by
          ring
        rw [e, le_div_iff₀ (by positivity)]
        linarith
    _ = ∑ j ∈ Finset.Ico (j₀ + 1) n,
          ENNReal.ofReal (ε ^ 2 / 2 * (M j * (ℓ j / 3) / (36 * π))) :=
        ENNReal.ofReal_sum_of_nonneg fun j hj => by rw [hval j hj]; positivity
    _ ≤ ∑ j ∈ Finset.Ico (j₀ + 1) n, gagliardoCoeff D ε (pJ j) (qJ j) :=
        Finset.sum_le_sum fun j hj => gagliardo_J_ge D (by have := (Finset.mem_Ico.1 hj).1; omega) ε
    _ ≤ ∑ j ∈ Finset.Ico (j₀ + 1) n, ∫⁻ t in Ioo (pJ j) (qJ j), ∫⁻ s in Ioo p q,
          eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π)) ^ 2 /
            ENNReal.ofReal ((t - s) ^ 2) :=
        Finset.sum_le_sum fun j hj =>
          lintegral_mono fun t => lintegral_mono_set (hin j (Finset.mem_Ico.1 hj).1)
    _ = ∫⁻ t in ⋃ j ∈ Finset.Ico (j₀ + 1) n, Ioo (pJ j) (qJ j), ∫⁻ s in Ioo p q,
          eLpNorm (fun x => a D ε t x - a D ε s x) ∞ (volume.restrict (Ioo 0 π)) ^ 2 /
            ENNReal.ofReal ((t - s) ^ 2) :=
        (lintegral_biUnion_finset hdisj (fun _ _ => measurableSet_Ioo) _).symm
    _ ≤ gagliardoCoeff D ε p q :=
        lintegral_mono_set (iUnion₂_subset fun j hj => hin j (Finset.mem_Ico.1 hj).1)

/-- In a finite partition of `[0,1]`, some piece `(t_k, t_{k+1})` has `t_k < x ≤ t_{k+1}`. -/
theorem exists_castSucc_lt_le {N : ℕ} (t : Fin (N + 1) → ℝ) {x : ℝ} (h0 : t 0 < x)
    (h1 : x ≤ t (Fin.last N)) : ∃ k : Fin N, t k.castSucc < x ∧ x ≤ t k.succ := by
  classical
  set S := Finset.univ.filter (fun i : Fin (N + 1) => x ≤ t i) with hS
  have hne : S.Nonempty := ⟨Fin.last N, by simp [hS, h1]⟩
  have hi₀ : S.min' hne ∈ S := S.min'_mem hne
  have hx : x ≤ t (S.min' hne) := (Finset.mem_filter.1 hi₀).2
  have hi₀0 : S.min' hne ≠ 0 := by
    intro h; rw [h] at hx; linarith
  obtain ⟨k, hk⟩ := Fin.exists_succ_eq.2 hi₀0
  refine ⟨k, ?_, hk ▸ hx⟩
  by_contra hlt
  push Not at hlt
  have hmem : k.castSucc ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩
  have := S.min'_le _ hmem
  rw [← hk] at this
  exact absurd this (not_le.2 (Fin.castSucc_lt_succ (i := k)))

/-- **(iii), coefficient form:** for every finite partition `0 = t₀ < t₁ < … < t_N = 1` of
`[0,1]`, some piece `(t_k, t_{k+1})` has infinite Gagliardo seminorm
`∫∫ ‖𝔞(t) − 𝔞(s)‖²_{L^∞(0,π)}/|t − s|² = ∞`: `𝔞 : [0,1] → L^∞(0,π)` is not piecewise
`H^{1/2}`.  (Strict monotonicity of the partition is not needed.) -/
theorem exists_piece_gagliardo_eq_top {ε : ℝ} (hε : 0 < ε) {N : ℕ} (t : Fin (N + 1) → ℝ)
    (h0 : t 0 = 0) (h1 : t (Fin.last N) = 1) :
    ∃ k : Fin N, gagliardoCoeff D ε (t k.castSucc) (t k.succ) = ⊤ := by
  obtain ⟨k, hk1, hk2⟩ := exists_castSucc_lt_le t (x := 5 / 16) (by rw [h0]; norm_num)
    (by rw [h1]; norm_num)
  exact ⟨k, gagliardoCoeff_eq_top D hε hk1 hk2⟩

/-- **(iii), operator form:** for every finite partition `0 = t₀ < … < t_N = 1`, some piece
has `∫∫ ‖𝒜(t) − 𝒜(s)‖²_{L(V,V')}/|t − s|² = ∞`: `𝒜 : [0,1] → L(V,V')` is not piecewise
`H^{1/2}`. -/
theorem exists_piece_gagliardo_form_eq_top {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (t : Fin (N + 1) → ℝ) (h0 : t 0 = 0) (h1 : t (Fin.last N) = 1) :
    ∃ k : Fin N, gagliardoForm D ε (t k.castSucc) (t k.succ) = ⊤ := by
  obtain ⟨k, hk⟩ := exists_piece_gagliardo_eq_top D hε t h0 h1
  exact ⟨k, by rw [gagliardoForm_eq, hk]⟩

/-! ### (iv) The Auscher–Egert square condition -/

/-- The quantity of the Auscher–Egert square condition at `x ∈ (0,π)` on the interval `(p,q)`:
`∫∫_{(p,q)²} |𝔞(t,x) − 𝔞(s,x)|² / |t − s|² ds dt ∈ [0,∞]`. -/
def aeSquare (ε x p q : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo p q, ∫⁻ s in Ioo p q,
    ENNReal.ofReal ((a D ε t x - a D ε s x) ^ 2 / (t - s) ^ 2)

theorem measurable_aeIntegrand {γ : Type*} [TopologicalSpace γ] [MeasurableSpace γ]
    [OpensMeasurableSpace γ] (ε : ℝ) {T S X : γ → ℝ} (hT : Continuous T) (hS : Continuous S)
    (hX : Continuous X) :
    Measurable fun z =>
      ENNReal.ofReal ((a D ε (T z) (X z) - a D ε (S z) (X z)) ^ 2 / (T z - S z) ^ 2) := by
  have ha := continuous_a D ε
  have h1 : Continuous fun z => (a D ε (T z) (X z) - a D ε (S z) (X z)) ^ 2 :=
    ((ha.comp (hT.prodMk hX)).sub (ha.comp (hS.prodMk hX))).pow 2
  have h2 : Continuous fun z => (T z - S z) ^ 2 := (hT.sub hS).pow 2
  exact (h1.measurable.div h2.measurable).ennreal_ofReal

/-- The `x`-integral of the square-condition integrand on `J_j` (spatial orthogonality). -/
theorem lintegral_x_aeIntegrand {j : ℕ} (hj : 1 ≤ j) {t s : ℝ} (ht : t ∈ J j) (hs : s ∈ J j)
    (ε : ℝ) :
    ∫⁻ x in Ioo 0 π, ENNReal.ofReal ((a D ε t x - a D ε s x) ^ 2 / (t - s) ^ 2) =
      ENNReal.ofReal (π / 2 * ε ^ 2) * ENNReal.ofReal (modeSq j t s / (t - s) ^ 2) := by
  have hc : Continuous fun x => (a D ε t x - a D ε s x) ^ 2 / (t - s) ^ 2 :=
    ((continuous_a_sub D ε t s).pow 2).div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal
      ((hc.integrableOn_Icc (a := 0) (b := π)).mono_set Ioo_subset_Icc_self)
      (Eventually.of_forall fun x => by positivity),
    ← ENNReal.ofReal_mul (by positivity), integral_div, integral_Iπ_eq,
    integral_a_sub_sq D hj ht hs ε]
  congr 1
  ring

/-- **Tonelli:** the `x`-integral of the square-condition quantity over `I = J_j` is at least
`(π/2) ε² M_j |J_j| / (36π)`. -/
theorem lintegral_aeSquare_ge {j : ℕ} (hj : 1 ≤ j) (ε : ℝ) :
    ENNReal.ofReal (π / 2 * ε ^ 2) * ENNReal.ofReal (M j * (ℓ j / 3) / (36 * π)) ≤
      ∫⁻ x in Ioo 0 π, aeSquare D ε x (pJ j) (qJ j) := by
  set F : ℝ → ℝ → ℝ → ℝ≥0∞ := fun x t s =>
    ENNReal.ofReal ((a D ε t x - a D ε s x) ^ 2 / (t - s) ^ 2) with hF
  have hm1 : Measurable fun z : (ℝ × ℝ) × ℝ => F z.1.1 z.1.2 z.2 :=
    measurable_aeIntegrand D ε (continuous_snd.comp continuous_fst) continuous_snd
      (continuous_fst.comp continuous_fst)
  have hm2 : ∀ t : ℝ, Measurable fun z : ℝ × ℝ => F z.1 t z.2 := fun t =>
    measurable_aeIntegrand D ε continuous_const continuous_snd continuous_fst
  -- exchange the order of integration
  have hswap : ∫⁻ x in Ioo 0 π, aeSquare D ε x (pJ j) (qJ j) =
      ∫⁻ t in Ioo (pJ j) (qJ j), ∫⁻ s in Ioo (pJ j) (qJ j), ∫⁻ x in Ioo 0 π, F x t s := by
    unfold aeSquare
    rw [lintegral_lintegral_swap (hm1.lintegral_prod_right'.aemeasurable)]
    refine lintegral_congr fun t => ?_
    exact lintegral_lintegral_swap (hm2 t).aemeasurable
  rw [hswap]
  calc ENNReal.ofReal (π / 2 * ε ^ 2) * ENNReal.ofReal (M j * (ℓ j / 3) / (36 * π))
      ≤ ENNReal.ofReal (π / 2 * ε ^ 2) * ∫⁻ t in Ioo (pJ j) (qJ j), ∫⁻ s in Ioo (pJ j) (qJ j),
          ENNReal.ofReal (modeSq j t s / (t - s) ^ 2) := by
        gcongr; exact lintegral_modeSq_ge hj
    _ = ∫⁻ t in Ioo (pJ j) (qJ j), ∫⁻ s in Ioo (pJ j) (qJ j),
          ENNReal.ofReal (π / 2 * ε ^ 2) * ENNReal.ofReal (modeSq j t s / (t - s) ^ 2) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1; ext t
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ t in Ioo (pJ j) (qJ j), ∫⁻ s in Ioo (pJ j) (qJ j), ∫⁻ x in Ioo 0 π, F x t s := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
        refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
        exact (lintegral_x_aeIntegrand D hj (Ioo_subset_J j ht) (Ioo_subset_J j hs) ε).symm

/-- **(iv), interval by interval:** there is no `M < ∞` such that for every interval
`I = (p,q) ⊆ [0,1]` and almost every `x ∈ (0,π)`,
`|I|⁻¹ ∫∫_{I×I} |𝔞(t,x) − 𝔞(s,x)|²/|t − s|² ≤ M`.  (This is stronger than the failure of the
condition with the supremum over `I` inside the almost-everywhere quantifier,
`not_exists_auscherEgert_bound`.) -/
theorem not_exists_auscherEgert_bound' {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ Mb : ℝ≥0∞, Mb < ⊤ ∧ ∀ p q : ℝ, 0 ≤ p → p < q → q ≤ 1 →
      ∀ᵐ x ∂(volume.restrict (Ioo 0 π)), (ENNReal.ofReal (q - p))⁻¹ * aeSquare D ε x p q ≤ Mb := by
  rintro ⟨Mb, hMb, hb⟩
  have hπ := pi_pos
  set m := Mb.toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hMm : Mb = ENNReal.ofReal m := (ENNReal.ofReal_toReal hMb.ne).symm
  obtain ⟨j, hj⟩ := exists_nat_gt (72 * m * π / ε ^ 2 + 1)
  have hj1 : 1 ≤ j := by
    have : (1 : ℝ) < j := by
      have : 0 ≤ 72 * m * π / ε ^ 2 := by positivity
      linarith
    exact_mod_cast this.le
  have hℓ := ℓ_pos hj1
  have hL : 0 < qJ j - pJ j := by rw [qJ_sub_pJ]; positivity
  -- the hypothesis on `I = J_j`
  have hp0 : 0 ≤ pJ j := by have := τ_ge hj1; unfold pJ; linarith
  have hq1 : qJ j ≤ 1 := by
    have := τ_add_ℓ hj1
    have := τ_lt (j := j + 1) (by omega)
    unfold qJ; linarith
  have hI := hb (pJ j) (qJ j) hp0 (pJ_lt_qJ hj1) hq1
  have hup : ∫⁻ x in Ioo 0 π, aeSquare D ε x (pJ j) (qJ j) ≤
      ENNReal.ofReal (qJ j - pJ j) * Mb * ENNReal.ofReal π := by
    calc ∫⁻ x in Ioo 0 π, aeSquare D ε x (pJ j) (qJ j)
        ≤ ∫⁻ _ in Ioo 0 π, ENNReal.ofReal (qJ j - pJ j) * Mb := by
          refine lintegral_mono_ae ?_
          filter_upwards [hI] with x hx
          exact (ENNReal.inv_mul_le_iff (by simpa using hL) ENNReal.ofReal_ne_top).1 hx
      _ = ENNReal.ofReal (qJ j - pJ j) * Mb * ENNReal.ofReal π := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
  have hcomb := (lintegral_aeSquare_ge D hj1 ε).trans hup
  rw [hMm, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity), qJ_sub_pJ] at hcomb
  have hMj : (M j : ℝ) = j := rfl
  rw [hMj] at hcomb
  -- `ε² j/72 ≤ m π`
  have e : π / 2 * ε ^ 2 * (j * (ℓ j / 3) / (36 * π)) = (ℓ j / 3) * (ε ^ 2 * j / 72) := by
    field_simp; ring
  rw [e, mul_assoc] at hcomb
  have h3 := le_of_mul_le_mul_left hcomb (by positivity : 0 < ℓ j / 3)
  have h4 : 72 * m * π / ε ^ 2 < j := by linarith
  rw [div_lt_iff₀ (by positivity)] at h4
  nlinarith

/-- **(iv) Failure of the Auscher–Egert square condition:** there is no `M < ∞` such that
`sup_{I ⊆ [0,1], |I| > 0} |I|⁻¹ ∫∫_{I×I} |𝔞(t,x) − 𝔞(s,x)|²/|t − s|² ds dt ≤ M` for almost every
`x ∈ (0,π)` (condition (8) of Auscher–Egert [Theorem 2]); the intervals are `I = (p,q)`,
`0 ≤ p < q ≤ 1`. -/
theorem not_exists_auscherEgert_bound {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ Mb : ℝ≥0∞, Mb < ⊤ ∧ ∀ᵐ x ∂(volume.restrict (Ioo 0 π)),
      (⨆ (p : ℝ) (q : ℝ) (_ : 0 ≤ p) (_ : p < q) (_ : q ≤ 1),
        (ENNReal.ofReal (q - p))⁻¹ * aeSquare D ε x p q) ≤ Mb := by
  rintro ⟨Mb, hMb, hb⟩
  refine not_exists_auscherEgert_bound' D hε ⟨Mb, hMb, fun p q hp hpq hq => ?_⟩
  filter_upwards [hb] with x hx
  exact le_trans (le_iSup₂_of_le p q (le_iSup₂_of_le hp hpq
    (le_iSup (fun _ : q ≤ 1 => (ENNReal.ofReal (q - p))⁻¹ * aeSquare D ε x p q) hq))) hx

end LionsC12
