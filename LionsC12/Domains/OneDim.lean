module

public import LionsC12.Domains.Tensor
public import LionsC12.Interval.Elements

/-!
# One-dimensional ingredients of the construction on a domain

The zero extension `ũ = uZ` of the interval solution and its parabolic rescaling
`UR(t,s) = ũ(t/r², (s - x₀)/r)` (from `LionsC12.Transfer.Rescaling`), as functions on the line:

* `hasDerivAt_uZ`, `hasDerivAt_UR_x'`, `contDiff_UR_x` — `ũ(t)` is `C¹` on `ℝ` (the solution and
  its flux vanish at `0` and `π`);
* `continuous_uZ2`, `continuous_uxZ2`, `continuousAt_utZ2` — joint continuity in `(t,x)` of `ũ`,
  `∂ₓũ` and (off `t = 5/16`) `∂ₜũ`, all vanishing at `x ∈ {0, π}`;
* `weak1D` — the spatial weak formulation at fixed time on the whole line, without boundary
  conditions on the test function: `∫ 𝔟 ∂ₛUR conj(ψ') = ∫ ARZ conj(ψ)` for `ψ ∈ C¹(ℝ;ℂ)`, where
  `ARZ = r⁻² E₀(𝒜u)` is the (rescaled, zero-extended) elliptic part; `FR_sub_URt` —
  `FR - ∂ₜUR = ARZ`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open MeasureTheory Set Filter Topology Real
open scoped ComplexConjugate

variable (D : Cutoffs)

/-! ### The zero extension in two variables -/

theorem Z_ne_zero_mem {g : ℝ → ℝ} {z : ℝ} (h : Z g z ≠ 0) : z ∈ Ioo 0 π := by
  by_contra hz
  exact h (Z_of_notMem hz)

theorem continuousAt_Z2 {g : ℝ → ℝ → ℝ} {q₀ : ℝ × ℝ}
    (hg : ContinuousAt (fun q : ℝ × ℝ => g q.1 q.2) q₀)
    (h0 : q₀.2 = 0 ∨ q₀.2 = π → g q₀.1 q₀.2 = 0) :
    ContinuousAt (fun q : ℝ × ℝ => Z (g q.1) q.2) q₀ := by
  obtain ⟨τ₀, z₀⟩ := q₀
  by_cases hz : z₀ ∈ Ioo 0 π
  · have hev : (fun q : ℝ × ℝ => Z (g q.1) q.2) =ᶠ[𝓝 (τ₀, z₀)] fun q => g q.1 q.2 := by
      have : {q : ℝ × ℝ | q.2 ∈ Ioo 0 π} ∈ 𝓝 (τ₀, z₀) :=
        (isOpen_Ioo.preimage continuous_snd).mem_nhds hz
      filter_upwards [this] with q hq
      exact Z_of_mem hq
    exact hg.congr hev.symm
  by_cases hz' : z₀ = 0 ∨ z₀ = π
  · have hg0 := h0 hz'
    have hZ0 : Z (g τ₀) z₀ = 0 := Z_of_notMem hz
    rw [ContinuousAt, hZ0]
    refine squeeze_zero_norm (a := fun q : ℝ × ℝ => ‖g q.1 q.2‖) (fun q => ?_) ?_
    · simpa [Real.norm_eq_abs] using abs_Z_le (g q.1) q.2
    · have := hg.norm
      simp only [ContinuousAt] at this
      simpa [hg0] using this
  · push Not at hz'
    have hnot : z₀ ∉ Icc 0 π := by
      rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with h | h
      · exact hz'.1 h.symm
      rcases eq_or_lt_of_le h2 with h' | h'
      · exact hz'.2 h'
      exact hz ⟨h, h'⟩
    have hev : (fun q : ℝ × ℝ => Z (g q.1) q.2) =ᶠ[𝓝 (τ₀, z₀)] fun _ => 0 := by
      have : {q : ℝ × ℝ | q.2 ∈ (Icc 0 π)ᶜ} ∈ 𝓝 (τ₀, z₀) :=
        (isClosed_Icc.isOpen_compl.preimage continuous_snd).mem_nhds hnot
      filter_upwards [this] with q hq
      exact Z_of_notMem fun h => hq (Ioo_subset_Icc_self h)
    exact continuousAt_const.congr hev.symm

theorem continuous_uZ2 (ε : ℝ) : Continuous (fun q : ℝ × ℝ => uZ D ε q.1 q.2) :=
  continuous_iff_continuousAt.2 fun q => continuousAt_Z2 (g := u D ε)
    (continuous_u D ε).continuousAt fun h => by
      rcases h with h | h <;> rw [h]
      · exact u_zero_left D ε _
      · exact u_zero_right D ε _

theorem continuous_uxZ2 (ε : ℝ) : Continuous (fun q : ℝ × ℝ => uxZ D ε q.1 q.2) :=
  continuous_iff_continuousAt.2 fun q => continuousAt_Z2 (g := ux D ε)
    (continuous_ux D ε).continuousAt fun h => by
      rcases h with h | h <;> rw [h]
      · exact ux_zero_left D ε _
      · exact ux_zero_right D ε _

theorem ut_zero_left (ε τ : ℝ) : ut D ε τ 0 = 0 := by
  show D.ρ' τ * φ 0 + vt D ε τ 0 = 0
  rw [φ_zero, mul_zero, zero_add]
  exact finsum_eq_zero_of_forall_eq_zero fun j => by simp [vtblock, p_zero]

theorem ut_zero_right (ε τ : ℝ) : ut D ε τ π = 0 := by
  show D.ρ' τ * φ π + vt D ε τ π = 0
  rw [φ_pi, mul_zero, zero_add]
  exact finsum_eq_zero_of_forall_eq_zero fun j => by simp [vtblock, p_pi]

theorem continuousAt_utZ2 (ε : ℝ) {τ₀ : ℝ} (hτ : τ₀ ≠ 5 / 16) (z₀ : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => utZ D ε q.1 q.2) (τ₀, z₀) :=
  continuousAt_Z2 (g := ut D ε) (continuousAt_ut D ε hτ z₀) fun h => by
    rcases h with h | h <;> simp only at h <;> rw [h]
    · exact ut_zero_left D ε _
    · exact ut_zero_right D ε _

/-- The zero extension of the solution is `C¹` in space. -/
theorem hasDerivAt_uZ (ε τ z : ℝ) : HasDerivAt (uZ D ε τ) (uxZ D ε τ z) z :=
  hasDerivAt_Z_of_vanish (hasDerivAt_u_x D ε τ) (u_zero_left D ε τ) (u_zero_right D ε τ)
    (ux_zero_left D ε τ) (ux_zero_right D ε τ) z

theorem bdd_Z {g : ℝ → ℝ} (hg : Continuous g) : ∃ C, ∀ z, |Z g z| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) π)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max C 0, fun z => ?_⟩
  by_cases hz : z ∈ Ioo 0 π
  · rw [Z_of_mem hz]
    exact (hC z (Ioo_subset_Icc_self hz)).trans (le_max_left _ _)
  · rw [Z_of_notMem hz, abs_zero]
    exact le_max_right _ _

theorem measurable_Z {g : ℝ → ℝ} (hg : Continuous g) : Measurable (Z g) :=
  Measurable.ite measurableSet_Ioo hg.measurable measurable_const

/-! ### The rescaled objects on the line -/

/-- The rescaled time derivative `∂ₜUR`. -/
def URt (ε r x₀ : ℝ) (t s : ℝ) : ℝ := r⁻¹ ^ 2 * utZ D ε (t / r ^ 2) ((s - x₀) / r)

/-- The rescaled (zero-extended) elliptic part `r⁻² E₀(𝒜u)`. -/
def ARZ (ε r x₀ : ℝ) (t s : ℝ) : ℝ := r⁻¹ ^ 2 * Z (Au D ε (t / r ^ 2)) ((s - x₀) / r)

/-- The rescaled forcing without the zero extension (continuous). -/
def fRc (ε r x₀ : ℝ) (t s : ℝ) : ℝ := r⁻¹ ^ 2 * f D ε (t / r ^ 2) ((s - x₀) / r)

variable {D}

theorem scale_mem_Ioo_iff {r : ℝ} (hr : 0 < r) (x₀ s : ℝ) :
    (s - x₀) / r ∈ Ioo 0 π ↔ s ∈ Ioo x₀ (x₀ + r * π) := by
  rw [mem_Ioo, mem_Ioo, lt_div_iff₀ hr, div_lt_iff₀ hr]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem scale_right {r : ℝ} (hr : 0 < r) (x₀ : ℝ) : (x₀ + r * π - x₀) / r = π := by
  field_simp; ring

theorem scale_left (r x₀ : ℝ) : (x₀ - x₀) / r = 0 := by simp

theorem mem_Ioo_of_Z_ne {r : ℝ} (hr : 0 < r) {x₀ s : ℝ} {g : ℝ → ℝ}
    (h : Z g ((s - x₀) / r) ≠ 0) : s ∈ Ioo x₀ (x₀ + r * π) :=
  (scale_mem_Ioo_iff hr x₀ s).1 (Z_ne_zero_mem h)

theorem UR_ne_zero {ε r x₀ t s : ℝ} (hr : 0 < r) (h : UR D ε r x₀ t s ≠ 0) :
    s ∈ Ioo x₀ (x₀ + r * π) := mem_Ioo_of_Z_ne hr h

theorem URx_ne_zero {ε r x₀ t s : ℝ} (hr : 0 < r) (h : URx D ε r x₀ t s ≠ 0) :
    s ∈ Ioo x₀ (x₀ + r * π) := mem_Ioo_of_Z_ne hr (right_ne_zero_of_mul h)

theorem URt_ne_zero {ε r x₀ t s : ℝ} (hr : 0 < r) (h : URt D ε r x₀ t s ≠ 0) :
    s ∈ Ioo x₀ (x₀ + r * π) := mem_Ioo_of_Z_ne hr (right_ne_zero_of_mul h)

theorem FR_ne_zero {ε r x₀ t s : ℝ} (hr : 0 < r) (h : FR D ε r x₀ t s ≠ 0) :
    s ∈ Ioo x₀ (x₀ + r * π) := mem_Ioo_of_Z_ne hr (right_ne_zero_of_mul h)

theorem ARZ_ne_zero {ε r x₀ t s : ℝ} (hr : 0 < r) (h : ARZ D ε r x₀ t s ≠ 0) :
    s ∈ Ioo x₀ (x₀ + r * π) := mem_Ioo_of_Z_ne hr (right_ne_zero_of_mul h)

variable (D)

theorem hasDerivAt_UR_x' (ε r x₀ t s : ℝ) :
    HasDerivAt (UR D ε r x₀ t) (URx D ε r x₀ t s) s := by
  have h1 : HasDerivAt (fun w : ℝ => (w - x₀) / r) (1 / r) s := by
    simpa using ((hasDerivAt_id s).sub_const x₀).div_const r
  have h2 := (hasDerivAt_uZ D ε (t / r ^ 2) ((s - x₀) / r)).comp s h1
  have h3 : UR D ε r x₀ t = (uZ D ε (t / r ^ 2)) ∘ fun w : ℝ => (w - x₀) / r := rfl
  rw [h3]
  convert h2 using 1
  rw [URx]
  ring

theorem continuous_uxZ_x (ε τ : ℝ) : Continuous (uxZ D ε τ) :=
  continuous_Z (continuous_ux_x D ε τ) (ux_zero_left D ε τ) (ux_zero_right D ε τ)

theorem continuous_URx_x (ε r x₀ t : ℝ) : Continuous (URx D ε r x₀ t) :=
  continuous_const.mul ((continuous_uxZ_x D ε _).comp (by fun_prop))

theorem continuous_UR_x (ε r x₀ t : ℝ) : Continuous (UR D ε r x₀ t) :=
  (uZ_continuous_x D ε _).comp (by fun_prop)

theorem continuous_bR_x (ε r x₀ t : ℝ) : Continuous (bR D ε r x₀ t) :=
  (continuous_a_x D ε _).comp (by fun_prop)

theorem contDiff_UR_x (ε r x₀ t : ℝ) :
    ContDiff ℝ 1 (UR D ε r x₀ t) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (hasDerivAt_UR_x' D ε r x₀ t s).differentiableAt, ?_⟩
  have : deriv (UR D ε r x₀ t) = URx D ε r x₀ t :=
    funext fun s => (hasDerivAt_UR_x' D ε r x₀ t s).deriv
  rw [this]
  exact continuous_URx_x D ε r x₀ t

theorem measurable_ARZ_x (ε r x₀ t : ℝ) : Measurable (ARZ D ε r x₀ t) :=
  measurable_const.mul ((measurable_Z (continuous_Au_x D ε _)).comp (by fun_prop))

theorem bdd_UR_x {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (r x₀ t : ℝ) :
    ∃ C, ∀ s, |UR D ε r x₀ t s| ≤ C :=
  ⟨2, fun _ => (abs_Z_le _ _).trans (abs_u_le D hε0 hε1 _ _)⟩

theorem bdd_URx_x {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (r x₀ t : ℝ) :
    ∃ C, ∀ s, |URx D ε r x₀ t s| ≤ C :=
  ⟨|r⁻¹| * 2, fun s => by
    rw [URx, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_Z_le _ _).trans (abs_ux_le D hε0 hε1 _ _))
      (abs_nonneg _)⟩

theorem bdd_bR_x {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (r x₀ t : ℝ) :
    ∃ C, ∀ s, |bR D ε r x₀ t s| ≤ C :=
  ⟨481 / 480, fun _ => abs_a_le D hε0 hε1 _ _⟩

theorem bdd_ARZ_x (ε r x₀ t : ℝ) : ∃ C, ∀ s, |ARZ D ε r x₀ t s| ≤ C := by
  obtain ⟨C, hC⟩ := bdd_Z (continuous_Au_x D ε (t / r ^ 2))
  exact ⟨|r⁻¹ ^ 2| * C, fun s => by
    rw [ARZ, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)⟩

/-! ### Joint continuity of the rescaled objects -/

theorem continuous_scale' (r x₀ : ℝ) :
    Continuous (fun q : ℝ × ℝ => ((q.1 / r ^ 2 : ℝ), ((q.2 - x₀) / r : ℝ))) :=
  (continuous_fst.div_const _).prodMk ((continuous_snd.sub continuous_const).div_const _)

theorem continuous_UR2 (ε r x₀ : ℝ) : Continuous (fun q : ℝ × ℝ => UR D ε r x₀ q.1 q.2) :=
  (continuous_uZ2 D ε).comp (continuous_scale' r x₀)

theorem continuous_URx2 (ε r x₀ : ℝ) : Continuous (fun q : ℝ × ℝ => URx D ε r x₀ q.1 q.2) :=
  continuous_const.mul ((continuous_uxZ2 D ε).comp (continuous_scale' r x₀))

theorem continuous_bR2 (ε r x₀ : ℝ) : Continuous (fun q : ℝ × ℝ => bR D ε r x₀ q.1 q.2) := by
  have h := (continuous_a D ε).comp (continuous_scale' r x₀)
  simp only [Function.comp_def] at h
  unfold bR
  exact h

theorem continuous_fRc2 (ε r x₀ : ℝ) : Continuous (fun q : ℝ × ℝ => fRc D ε r x₀ q.1 q.2) := by
  have h := (continuous_f D ε).comp (continuous_scale' r x₀)
  simp only [Function.comp_def] at h
  exact continuous_const.mul h

theorem continuousAt_URt2 (ε r x₀ : ℝ) {t₀ : ℝ} (ht : t₀ / r ^ 2 ≠ 5 / 16) (s₀ : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => URt D ε r x₀ q.1 q.2) (t₀, s₀) := by
  have h := (continuousAt_utZ2 D ε ht ((s₀ - x₀) / r)).comp (x := (t₀, s₀))
    (continuous_scale' r x₀).continuousAt
  show ContinuousAt (fun q : ℝ × ℝ => r⁻¹ ^ 2 * utZ D ε (q.1 / r ^ 2) ((q.2 - x₀) / r)) (t₀, s₀)
  exact continuousAt_const.mul h

theorem FR_eq_ite (ε r x₀ t s : ℝ) :
    FR D ε r x₀ t s = if (s - x₀) / r ∈ Ioo 0 π then fRc D ε r x₀ t s else 0 := by
  by_cases h : (s - x₀) / r ∈ Ioo 0 π
  · rw [FR, fZ, Z_of_mem h, fRc]; simp [h]
  · rw [FR, fZ, Z_of_notMem h, mul_zero]; simp [h]

theorem abs_FR_sub_le (ε r x₀ t t₀ s : ℝ) :
    |FR D ε r x₀ t s - FR D ε r x₀ t₀ s| ≤ |fRc D ε r x₀ t s - fRc D ε r x₀ t₀ s| := by
  rw [FR_eq_ite, FR_eq_ite]
  split_ifs
  · exact le_rfl
  · simp

theorem hasDerivAt_UR_t' (ε r x₀ t s : ℝ) :
    HasDerivAt (fun t => UR D ε r x₀ t s) (URt D ε r x₀ t s) t :=
  hasDerivAt_UR_t D ε r x₀ t s

/-- `FR - ∂ₜUR = ARZ`: the equation `∂ₜu + 𝒜u = f` on `(0,π)`, rescaled and zero-extended. -/
theorem FR_sub_URt (ε r x₀ t s : ℝ) : FR D ε r x₀ t s - URt D ε r x₀ t s = ARZ D ε r x₀ t s := by
  rw [FR, URt, ARZ, ← mul_sub]
  congr 1
  by_cases h : (s - x₀) / r ∈ Ioo 0 π
  · rw [fZ, utZ, Z_of_mem h, Z_of_mem h, Z_of_mem h]
    have := pde D ε (t / r ^ 2) ((s - x₀) / r)
    linarith
  · rw [fZ, utZ, Z_of_notMem h, Z_of_notMem h, Z_of_notMem h, sub_zero]

/-! ### The spatial weak formulation on the line -/

/-- **The spatial weak formulation on the line at fixed time**:
`∫ 𝔟 ∂ₛUR conj(ψ') = ∫ ARZ conj(ψ)` for every `ψ ∈ C¹(ℝ;ℂ)`.  No boundary condition on `ψ` is
needed: the flux `𝔞 ∂ₓu` vanishes at both endpoints. -/
theorem weak1D (ε : ℝ) {r : ℝ} (hr : 0 < r) (x₀ t : ℝ) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ) :
    ∫ s, ((bR D ε r x₀ t s * URx D ε r x₀ t s : ℝ) : ℂ) * conj (deriv ψ s)
      = ∫ s, (ARZ D ε r x₀ t s : ℂ) * conj (ψ s) := by
  set τ := t / r ^ 2
  set L := x₀
  set R := x₀ + r * π
  have hLR : L ≤ R := by
    have : 0 < r * π := mul_pos hr pi_pos
    simp only [L, R]; linarith
  set z : ℝ → ℝ := fun s => (s - x₀) / r with hz
  set flux : ℝ → ℝ := fun s => r⁻¹ * (a D ε τ (z s) * ux D ε τ (z s)) with hflux
  have hfluxd : ∀ s, HasDerivAt flux (-(r⁻¹ ^ 2 * Au D ε τ (z s))) s := by
    intro s
    have h1 : HasDerivAt z (1 / r) s := by
      simpa using ((hasDerivAt_id s).sub_const x₀).div_const r
    have h2 : HasDerivAt flux (r⁻¹ * (-Au D ε τ (z s) * (1 / r))) s :=
      ((hasDerivAt_flux D ε τ (z s)).comp s h1).const_mul r⁻¹
    exact h2.congr_deriv (by ring)
  have hψd : ∀ s, HasDerivAt ψ (deriv ψ s) s :=
    fun s => (hψ.differentiable one_ne_zero s).hasDerivAt
  have hψc : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  -- the left side as an integral over `[L, R]`
  have eL : ∫ s, ((bR D ε r x₀ t s * URx D ε r x₀ t s : ℝ) : ℂ) * conj (deriv ψ s)
      = ∫ s in L..R, (flux s : ℂ) * conj (deriv ψ s) := by
    rw [intervalIntegral.integral_of_le hLR, integral_Ioc_eq_integral_Ioo,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo L R) fun s hs => by
        have : URx D ε r x₀ t s = 0 := by
          by_contra h
          exact hs (URx_ne_zero hr h)
        rw [this, mul_zero, Complex.ofReal_zero, zero_mul]]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    have hs' := (scale_mem_Ioo_iff hr x₀ s).2 hs
    simp only [bR, URx, uxZ, Z_of_mem hs', hflux, hz, τ]
    push_cast; ring
  have eR : ∫ s, (ARZ D ε r x₀ t s : ℂ) * conj (ψ s)
      = ∫ s in L..R, ((r⁻¹ ^ 2 * Au D ε τ (z s) : ℝ) : ℂ) * conj (ψ s) := by
    rw [intervalIntegral.integral_of_le hLR, integral_Ioc_eq_integral_Ioo,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo L R) fun s hs => by
        have : ARZ D ε r x₀ t s = 0 := by
          by_contra h
          exact hs (ARZ_ne_zero hr h)
        rw [this, Complex.ofReal_zero, zero_mul]]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    have hs' := (scale_mem_Ioo_iff hr x₀ s).2 hs
    simp only [ARZ, Z_of_mem hs', hz, τ]
  rw [eL, eR]
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := L) (b := R)
    (u := fun s => (flux s : ℂ)) (u' := fun s => ((-(r⁻¹ ^ 2 * Au D ε τ (z s)) : ℝ) : ℂ))
    (v := fun s => conj (ψ s)) (v' := fun s => conj (deriv ψ s))
    (fun s _ => (hfluxd s).ofReal_comp) (fun s _ => (hψd s).star)
    ((Complex.continuous_ofReal.comp (((continuous_Au_x D ε τ).comp
      (by fun_prop : Continuous z)).const_mul (r⁻¹ ^ 2)).neg).intervalIntegrable _ _)
    ((Complex.continuous_conj.comp hψc).intervalIntegrable _ _)
  have hL0 : flux L = 0 := by
    simp only [hflux, hz, L, scale_left, ux_zero_left, mul_zero]
  have hR0 : flux R = 0 := by
    simp only [hflux, hz, R, scale_right hr, ux_zero_right, mul_zero]
  rw [hIBP, hL0, hR0]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, zero_sub, Complex.ofReal_neg, neg_mul,
    intervalIntegral.integral_neg, neg_neg]

end LionsC12
