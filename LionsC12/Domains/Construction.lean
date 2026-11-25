module

public import LionsC12.Domains.OneDim

/-!
# The counterexample on a domain: the functions

For a point `p ∈ ℝ^{n+1}` and a radius `0 < r`, the parabolically rescaled and tensorised
interval counterexample of Section 6 of the paper, as functions on `ℝ × ℝ^{n+1}`:

* `domB t x = 𝔞(t/r², (x₁ - p₁)/r)`, the scalar coefficient;
* `domW t x = ũ(t/r², (x₁ - p₁)/r) Q(x')`, `Q(y) = χ((y - p')/r)` with a bump `χ`, the solution;
* `domWt`, `domGrad`: its time derivative and its gradient;
* `domF t x = r⁻² f̃(t/r², (x₁-p₁)/r) Q(x') - 𝔟 ũ ΔQ(x')`, the forcing.

All of them vanish outside the compact set `K = closedBall p (r(π+1))` (`mem_domK_of`), and they are
continuous in time with values in `L²` (uniformly on `K`).  The elements of the Hilbert spaces
built from them are defined in `LionsC12.Domains.Equation`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology LionsC12Challenge Real
open scoped InnerProductSpace ComplexConjugate ENNReal

variable (D : Cutoffs) {n : ℕ}

/-! ### The bump in the tail variables -/

/-- A smooth bump on `ℝ^n`, `1` on the ball of radius `1/2` and supported in the closed unit
ball. -/
def bumpE (n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The rescaled bump `Q(y) = χ((y - p')/r)`. -/
def Qr (r : ℝ) (p : EuclideanSpace ℝ (Fin (n + 1))) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  bumpE n (r⁻¹ • (y - tailL n p))

theorem Qr_eq_zero {r : ℝ} (hr : 0 < r) (p : EuclideanSpace ℝ (Fin (n + 1)))
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∉ Metric.closedBall (tailL n p) r) : Qr r p y = 0 := by
  apply (bumpE n).zero_of_le_dist
  rw [Metric.mem_closedBall, not_le] at hy
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr, ← dist_eq_norm]
  show (1 : ℝ) ≤ r⁻¹ * dist y (tailL n p)
  rw [inv_mul_eq_div, le_div_iff₀ hr, one_mul]
  exact hy.le

theorem Qr_center (r : ℝ) (p : EuclideanSpace ℝ (Fin (n + 1))) : Qr r p (tailL n p) = 1 := by
  apply (bumpE n).one_of_mem_closedBall
  simp [bumpE]

theorem isBumpFn_Qr {r : ℝ} (hr : 0 < r) (p : EuclideanSpace ℝ (Fin (n + 1))) :
    IsBumpFn (Qr r p) where
  contDiff := (bumpE n).contDiff.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
  hasCompactSupport := HasCompactSupport.intro (isCompact_closedBall (tailL n p) r)
    fun _ hy => Qr_eq_zero hr p hy

/-- A function vanishing off a closed set has vanishing derivative off that set. -/
theorem fderiv_eq_zero_of_compl {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} {S : Set E} (hS : IsClosed S)
    (hg : ∀ y ∉ S, g y = 0) {y : E} (hy : y ∉ S) : fderiv ℝ g y = 0 := by
  have hev : g =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [hS.isOpen_compl.mem_nhds hy] with z hz
    exact hg z hz
  rw [hev.fderiv_eq, fderiv_const_apply]

theorem dQr_eq_zero {r : ℝ} (hr : 0 < r) (p : EuclideanSpace ℝ (Fin (n + 1))) (j : Fin n)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∉ Metric.closedBall (tailL n p) r) :
    dQ (Qr r p) j y = 0 := by
  rw [dQ, fderiv_eq_zero_of_compl Metric.isClosed_closedBall (fun _ h => Qr_eq_zero hr p h) hy]
  rfl

theorem lapQr_eq_zero {r : ℝ} (hr : 0 < r) (p : EuclideanSpace ℝ (Fin (n + 1)))
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∉ Metric.closedBall (tailL n p) r) :
    lapQ (Qr r p) y = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [d2Q, fderiv_eq_zero_of_compl Metric.isClosed_closedBall
    (fun _ h => dQr_eq_zero hr p j h) hy]
  rfl

/-! ### The support set -/

/-- The compact set `K = closedBall p (r(π+1)) ⊇ p + r([0,π] × closedBall 0 1)`. -/
def domK (r : ℝ) (p : EuclideanSpace ℝ (Fin (n + 1))) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.closedBall p (r * (π + 1))

theorem isCompact_domK (r : ℝ) (p : EuclideanSpace ℝ (Fin (n + 1))) : IsCompact (domK r p) :=
  isCompact_closedBall _ _

theorem measurableSet_domK (r : ℝ) (p : EuclideanSpace ℝ (Fin (n + 1))) :
    MeasurableSet (domK r p) :=
  Metric.isClosed_closedBall.measurableSet

theorem mem_domK_of {r : ℝ} {p x : EuclideanSpace ℝ (Fin (n + 1))}
    (h1 : x 0 ∈ Ioo (p 0) (p 0 + r * π)) (h2 : tailL n x ∈ Metric.closedBall (tailL n p) r) :
    x ∈ domK r p := by
  rw [domK, Metric.mem_closedBall, dist_eq_norm]
  have h := norm_le_head_add_tail (x - p)
  have e1 : (x - p) 0 = x 0 - p 0 := rfl
  rw [e1, map_sub] at h
  rw [Metric.mem_closedBall, dist_eq_norm] at h2
  have h3 : |x 0 - p 0| ≤ r * π := by
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2]
  linarith

/-- A tensor product `f(x₁) g(x')` with `f` supported in `[p₁, p₁ + rπ]` and `g` in
`closedBall p' r` vanishes off `K`. -/
theorem tens_eq_zero_of_notMem {r : ℝ} {p : EuclideanSpace ℝ (Fin (n + 1))} {f : ℝ → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ∀ s, f s ≠ 0 → s ∈ Ioo (p 0) (p 0 + r * π))
    (hg : ∀ y, y ∉ Metric.closedBall (tailL n p) r → g y = 0)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∉ domK r p) : f (x 0) * g (tailL n x) = 0 := by
  by_contra h
  have h1 := hf _ (left_ne_zero_of_mul h)
  have h2 : tailL n x ∈ Metric.closedBall (tailL n p) r := by
    by_contra h2
    exact right_ne_zero_of_mul h (hg _ h2)
  exact hx (mem_domK_of h1 h2)

/-! ### The functions -/

variable (ε r : ℝ) (p : EuclideanSpace ℝ (Fin (n + 1)))

/-- The coefficient `𝔟(t,x) = 𝔞(t/r², (x₁ - p₁)/r)`. -/
def domB (t : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ := bR D ε r (p 0) t (x 0)

/-- The solution `U(t,x) = ũ(t/r², (x₁ - p₁)/r) Q(x')`. -/
def domW (t : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ := tens (UR D ε r (p 0) t) (Qr r p) x

/-- Its time derivative. -/
def domWt (t : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  tens (URt D ε r (p 0) t) (Qr r p) x

/-- Its gradient. -/
def domGrad (t : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℂ (Fin (n + 1)) :=
  gradTens (UR D ε r (p 0) t) (URx D ε r (p 0) t) (Qr r p) x

/-- The forcing `F = r⁻² f̃ ⊗ Q - 𝔟 ũ ⊗ ΔQ`. -/
def domF (t : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  tens (FR D ε r (p 0) t) (Qr r p) x
    - bR D ε r (p 0) t (x 0) * UR D ε r (p 0) t (x 0) * lapQ (Qr r p) (tailL n x)

/-- The elliptic part `-div(𝔟 ∇U) = r⁻² E₀(𝒜u) ⊗ Q - 𝔟 ũ ⊗ ΔQ`. -/
def domA (t : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  ARZ D ε r (p 0) t (x 0) * Qr r p (tailL n x)
    - bR D ε r (p 0) t (x 0) * UR D ε r (p 0) t (x 0) * lapQ (Qr r p) (tailL n x)

theorem domF_sub_domWt (t : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    domF D ε r p t x - domWt D ε r p t x = domA D ε r p t x := by
  simp only [domF, domWt, domA, tens, ← FR_sub_URt D ε r (p 0) t (x 0)]
  ring

variable {r}

theorem domW_eq_zero (hr : 0 < r) (t : ℝ) {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∉ domK r p) : domW D ε r p t x = 0 :=
  tens_eq_zero_of_notMem (fun _ h => UR_ne_zero hr h) (fun _ h => Qr_eq_zero hr p h) hx

theorem domWt_eq_zero (hr : 0 < r) (t : ℝ) {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∉ domK r p) : domWt D ε r p t x = 0 :=
  tens_eq_zero_of_notMem (fun _ h => URt_ne_zero hr h) (fun _ h => Qr_eq_zero hr p h) hx

theorem domGrad_eq_zero (hr : 0 < r) (t : ℝ) {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∉ domK r p) : domGrad D ε r p t x = 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [domGrad, gradTens_zero]
    rw [tens_eq_zero_of_notMem (fun _ h => URx_ne_zero hr h) (fun _ h => Qr_eq_zero hr p h) hx]
    simp
  · simp only [domGrad, gradTens_succ]
    rw [tens_eq_zero_of_notMem (fun _ h => UR_ne_zero hr h) (fun _ h => dQr_eq_zero hr p j h) hx]
    simp

theorem domF_eq_zero (hr : 0 < r) (t : ℝ) {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∉ domK r p) : domF D ε r p t x = 0 := by
  have h1 := tens_eq_zero_of_notMem (r := r) (p := p) (f := FR D ε r (p 0) t)
    (fun _ h => FR_ne_zero hr h) (fun _ h => Qr_eq_zero hr p h) hx
  have h2 := tens_eq_zero_of_notMem (r := r) (p := p)
    (f := fun s => bR D ε r (p 0) t s * UR D ε r (p 0) t s)
    (fun _ h => UR_ne_zero hr (right_ne_zero_of_mul h)) (fun _ h => lapQr_eq_zero hr p h) hx
  simp only [domF, tens] at h1 ⊢
  rw [h1, h2, sub_zero]

/-! ### Regularity in `x` -/

theorem hasDerivAt_URt_t (t s : ℝ) :
    HasDerivAt (fun τ => UR D ε r (p 0) τ s) (URt D ε r (p 0) t s) t :=
  hasDerivAt_UR_t' D ε r (p 0) t s

theorem contDiff_domW (hr : 0 < r) (t : ℝ) : ContDiff ℝ 1 (domW D ε r p t) :=
  contDiff_tens (contDiff_UR_x D ε r (p 0) t) ((isBumpFn_Qr hr p).contDiff.of_le (by simp))

theorem grad_domW (hr : 0 < r) (t : ℝ) :
    grad (fun x => (domW D ε r p t x : ℂ)) = domGrad D ε r p t :=
  funext fun x => grad_tens (fun s => hasDerivAt_UR_x' D ε r (p 0) t s)
    (isBumpFn_Qr hr p).differentiable x

/-! ### Joint continuity -/

theorem continuous_head_pair :
    Continuous fun q : ℝ × EuclideanSpace ℝ (Fin (n + 1)) => (q.1, q.2 0) :=
  continuous_fst.prodMk (continuous_head.comp continuous_snd)

theorem continuous_domW (hr : 0 < r) :
    Continuous (Function.uncurry fun t x => (domW D ε r p t x : ℂ)) := by
  have h1 := (continuous_UR2 D ε r (p 0)).comp (continuous_head_pair (n := n))
  have h2 : Continuous fun q : ℝ × EuclideanSpace ℝ (Fin (n + 1)) => Qr r p (tailL n q.2) :=
    ((isBumpFn_Qr hr p).continuous.comp (tailL n).continuous).comp continuous_snd
  simp only [Function.comp_def] at h1
  have h3 := Complex.continuous_ofReal.comp (h1.mul h2)
  simp only [Function.comp_def] at h3
  show Continuous fun q : ℝ × EuclideanSpace ℝ (Fin (n + 1)) =>
    ((UR D ε r (p 0) q.1 (q.2 0) * Qr r p (tailL n q.2) : ℝ) : ℂ)
  exact h3

theorem continuous_domB : Continuous (Function.uncurry (domB D ε r p)) := by
  have h1 := (continuous_bR2 D ε r (p 0)).comp (continuous_head_pair (n := n))
  simp only [Function.comp_def] at h1
  show Continuous fun q : ℝ × EuclideanSpace ℝ (Fin (n + 1)) => bR D ε r (p 0) q.1 (q.2 0)
  exact h1

theorem continuous_domGrad (hr : 0 < r) : Continuous (Function.uncurry (domGrad D ε r p)) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  have hh : Continuous fun q : ℝ × EuclideanSpace ℝ (Fin (n + 1)) => (q.1, q.2 0) :=
    continuous_fst.prodMk (continuous_head.comp continuous_snd)
  have ht : Continuous fun q : ℝ × EuclideanSpace ℝ (Fin (n + 1)) => tailL n q.2 :=
    (tailL n).continuous.comp continuous_snd
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact Complex.continuous_ofReal.comp (((continuous_URx2 D ε r (p 0)).comp hh).mul
      ((isBumpFn_Qr hr p).continuous.comp ht))
  · simp only [Fin.cons_succ]
    exact Complex.continuous_ofReal.comp (((continuous_UR2 D ε r (p 0)).comp hh).mul
      (((isBumpFn_Qr hr p).continuous_dQ j).comp ht))

theorem continuous_domBGrad (hr : 0 < r) :
    Continuous (Function.uncurry fun t x => (domB D ε r p t x : ℂ) • domGrad D ε r p t x) :=
  (Complex.continuous_ofReal.comp (continuous_domB D ε p)).smul (continuous_domGrad D ε p hr)

theorem continuousOn_domWt (hr : 0 < r) {T : Set ℝ} (hT : ∀ t ∈ T, t / r ^ 2 ≠ 5 / 16) :
    ContinuousOn (Function.uncurry fun t x => (domWt D ε r p t x : ℂ))
      (T ×ˢ (univ : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  intro q hq
  refine ContinuousAt.continuousWithinAt ?_
  refine Complex.continuous_ofReal.continuousAt.comp ?_
  have hh : Continuous fun q : ℝ × EuclideanSpace ℝ (Fin (n + 1)) => (q.1, q.2 0) :=
    continuous_fst.prodMk (continuous_head.comp continuous_snd)
  have h1 : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin (n + 1)) =>
      URt D ε r (p 0) q.1 (q.2 0)) q :=
    ContinuousAt.comp (f := fun q : ℝ × EuclideanSpace ℝ (Fin (n + 1)) => (q.1, q.2 0)) (x := q)
      (continuousAt_URt2 D ε r (p 0) (hT q.1 hq.1) (q.2 0)) hh.continuousAt
  exact h1.mul (((isBumpFn_Qr hr p).continuous.comp (tailL n).continuous).comp
    continuous_snd).continuousAt

/-- The forcing is uniformly continuous in time on `K`. -/
theorem eventually_domF (hr : 0 < r) (t₀ : ℝ) :
    ∀ η > 0, ∀ᶠ t in 𝓝 t₀, ∀ x ∈ domK r p,
      ‖(domF D ε r p t x : ℂ) - (domF D ε r p t₀ x : ℂ)‖ ≤ η := by
  intro η hη
  have hh : Continuous fun q : ℝ × EuclideanSpace ℝ (Fin (n + 1)) => (q.1, q.2 0) :=
    continuous_fst.prodMk (continuous_head.comp continuous_snd)
  have hQ := isBumpFn_Qr hr p
  have hc1 : Continuous (Function.uncurry fun t (x : EuclideanSpace ℝ (Fin (n + 1))) =>
      (fRc D ε r (p 0) t (x 0) * Qr r p (tailL n x) : ℝ)) :=
    ((continuous_fRc2 D ε r (p 0)).comp hh).mul
      ((hQ.continuous.comp (tailL n).continuous).comp continuous_snd)
  have hc2 : Continuous (Function.uncurry fun t (x : EuclideanSpace ℝ (Fin (n + 1))) =>
      (bR D ε r (p 0) t (x 0) * UR D ε r (p 0) t (x 0) * lapQ (Qr r p) (tailL n x) : ℝ)) :=
    (((continuous_bR2 D ε r (p 0)).comp hh).mul ((continuous_UR2 D ε r (p 0)).comp hh)).mul
      ((hQ.continuous_lapQ.comp (tailL n).continuous).comp continuous_snd)
  have e1 := eventually_norm_sub_le_of_continuousOn (isCompact_domK r p) (t₀ := t₀) one_pos
    hc1.continuousOn (η / 2) (by positivity)
  have e2 := eventually_norm_sub_le_of_continuousOn (isCompact_domK r p) (t₀ := t₀) one_pos
    hc2.continuousOn (η / 2) (by positivity)
  filter_upwards [e1, e2] with t h1 h2 x hx
  have k1 := h1 x hx
  have k2 := h2 x hx
  simp only [Real.norm_eq_abs] at k1 k2
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hFR := abs_FR_sub_le D ε r (p 0) t t₀ (x 0)
  have e : domF D ε r p t x - domF D ε r p t₀ x
      = (FR D ε r (p 0) t (x 0) - FR D ε r (p 0) t₀ (x 0)) * Qr r p (tailL n x)
        - (bR D ε r (p 0) t (x 0) * UR D ε r (p 0) t (x 0) * lapQ (Qr r p) (tailL n x)
          - bR D ε r (p 0) t₀ (x 0) * UR D ε r (p 0) t₀ (x 0) * lapQ (Qr r p) (tailL n x)) := by
    simp only [domF, tens]; ring
  have k3 : |(FR D ε r (p 0) t (x 0) - FR D ε r (p 0) t₀ (x 0)) * Qr r p (tailL n x)|
      ≤ |fRc D ε r (p 0) t (x 0) * Qr r p (tailL n x)
          - fRc D ε r (p 0) t₀ (x 0) * Qr r p (tailL n x)| := by
    rw [← sub_mul, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right hFR (abs_nonneg _)
  rw [e]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ η / 2 + η / 2 := add_le_add (k3.trans k1) k2
    _ = η := by ring

/-! ### Square integrability -/

theorem memLp_of_bdd_supp {X F : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup F] {f : X → F} (hf : AEStronglyMeasurable f μ) {C : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ C) {K : Set X} (hKμ : μ K < ∞)
    (h0 : ∀ x ∉ K, f x = 0) : MemLp f 2 μ := by
  have hsupp : Function.support f ⊆ K := fun x hx => by
    by_contra hK
    exact hx (h0 x hK)
  show eLpNorm f 2 μ < ∞
  rw [← eLpNorm_restrict_eq_of_support_subset hf hsupp]
  refine (eLpNorm_le_of_ae_bound hf.restrict (Eventually.of_forall hb)).trans_lt ?_
  rw [Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hKμ.ne)
    ENNReal.ofReal_lt_top

variable (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))

theorem domK_measure_lt_top : (volume.restrict Ω) (domK r p) < ∞ :=
  (Measure.restrict_apply_le _ _).trans_lt (isCompact_domK r p).measure_lt_top

theorem memLp_domWt (hr : 0 < r) (t : ℝ) :
    MemLp (fun x => (domWt D ε r p t x : ℂ)) 2 (volume.restrict Ω) := by
  obtain ⟨C₁, h₁⟩ := bdd_Z (continuous_ut_x D ε (t / r ^ 2))
  obtain ⟨C₂, h₂⟩ := (isBumpFn_Qr hr p).bdd
  refine memLp_of_bdd_supp ?_ (C := |r⁻¹ ^ 2| * C₁ * C₂) (fun x => ?_)
    (domK_measure_lt_top p Ω) (fun x hx => by rw [domWt_eq_zero D ε p hr t hx, Complex.ofReal_zero])
  · refine (Complex.measurable_ofReal.comp ?_).aestronglyMeasurable
    refine Measurable.mul ?_ ((isBumpFn_Qr hr p).continuous.comp (tailL n).continuous).measurable
    have hm : Measurable fun s : ℝ => URt D ε r (p 0) t s :=
      measurable_const.mul ((measurable_Z (continuous_ut_x D ε _)).comp
        ((measurable_id.sub_const _).div_const _))
    exact hm.comp measurable_head
  · rw [Complex.norm_real, Real.norm_eq_abs, domWt, tens, URt, abs_mul, abs_mul]
    refine mul_le_mul (mul_le_mul_of_nonneg_left (h₁ _) (abs_nonneg _)) (h₂ _) (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans (h₁ 0)))

theorem memLp_domF {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hr : 0 < r) (t : ℝ) :
    MemLp (fun x => (domF D ε r p t x : ℂ)) 2 (volume.restrict Ω) := by
  obtain ⟨C₂, h₂⟩ := (isBumpFn_Qr hr p).bdd
  obtain ⟨C₃, h₃⟩ := (isBumpFn_Qr hr p).bdd_lapQ
  refine memLp_of_bdd_supp ?_
    (C := |r⁻¹ ^ 2| * Cf D * C₂ + 481 / 480 * 2 * C₃) (fun x => ?_)
    (domK_measure_lt_top p Ω) (fun x hx => by rw [domF_eq_zero D ε p hr t hx, Complex.ofReal_zero])
  · refine (Complex.measurable_ofReal.comp ?_).aestronglyMeasurable
    refine Measurable.sub ?_ ?_
    · refine Measurable.mul ?_ ((isBumpFn_Qr hr p).continuous.comp (tailL n).continuous).measurable
      have hm : Measurable fun s : ℝ => FR D ε r (p 0) t s :=
        measurable_const.mul ((measurable_Z (continuous_f_x D ε _)).comp
          ((measurable_id.sub_const _).div_const _))
      exact hm.comp measurable_head
    · refine Measurable.mul (Measurable.mul ?_ ?_)
        ((isBumpFn_Qr hr p).continuous_lapQ.comp (tailL n).continuous).measurable
      · exact (continuous_bR_x D ε r (p 0) t).measurable.comp measurable_head
      · exact (continuous_UR_x D ε r (p 0) t).measurable.comp measurable_head
  · rw [Complex.norm_real, Real.norm_eq_abs, domF, tens]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [FR, abs_mul, abs_mul]
      refine mul_le_mul (mul_le_mul_of_nonneg_left ((abs_Z_le _ _).trans (abs_f_le D hε0 hε1 _ _))
        (abs_nonneg _)) (h₂ _) (abs_nonneg _) (mul_nonneg (abs_nonneg _)
          ((abs_nonneg _).trans (abs_f_le D hε0 hε1 0 0)))
    · rw [abs_mul, abs_mul]
      refine mul_le_mul (mul_le_mul (abs_a_le D hε0 hε1 _ _) ((abs_Z_le _ _).trans
        (abs_u_le D hε0 hε1 _ _)) (abs_nonneg _) (by norm_num)) (h₃ _) (abs_nonneg _)
        (by norm_num)

theorem memLp_domBGrad {ε : ℝ} (hr : 0 < r) (t : ℝ) :
    MemLp (fun x => (domB D ε r p t x : ℂ) • domGrad D ε r p t x) 2 (volume.restrict Ω) := by
  have hc := (continuous_domBGrad D ε p hr).comp (Continuous.prodMk_right (X := ℝ)
    (Y := EuclideanSpace ℝ (Fin (n + 1))) t)
  simp only [Function.comp_def, Function.uncurry] at hc
  refine (hc.memLp_of_hasCompactSupport ?_).restrict Ω
  exact HasCompactSupport.intro (isCompact_domK r p) fun x hx => by
    rw [domGrad_eq_zero D ε p hr t hx, smul_zero]

end LionsC12
