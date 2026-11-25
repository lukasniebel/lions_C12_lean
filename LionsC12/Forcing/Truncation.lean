module

public import LionsC12.Construction.Defs
public import LionsC12.Coefficient.Blocks
public import LionsC12.Coefficient.Support
public import LionsC12.Modes.Trig
public import LionsC12.Solution.Basic
public import LionsC12.Solution.Divergence
public import LionsC12.Forcing.Cancellation
public import LionsC12.Coefficient.Holder
public import LionsC12.Forcing.Continuity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Growth of the maximal-regularity constant

This file formalises the remark *Growth of the maximal-regularity constant* of the paper.
For `N : ℕ` we truncate the construction after the block `N`,
`β^{(N)} = ∑_{j ≤ N} β_j`, `𝔞_N = 1 + ε β^{(N)}`, `v^{(N)} = ∑_{j ≤ N} v_j`,
`u_N = ρ φ + v^{(N)}` and `f_N = ∂_t u_N + 𝒜_N(t) u_N`.

All truncated objects are finite sums of smooth functions.  They agree with the full
objects before the block `N + 1` starts, so all the uniform bounds of the paper are
inherited, while the lower bound on the middle thirds of the first `N` blocks gives
`‖∂_t u_N‖²_{L²(0,1;H)} ≥ (π ε²/1536) ∑_{j=1}^N 1/(j+1) ≥ (π ε²/1536)(log (N+2) - 1)`.
-/

@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ## The truncated objects -/

/-- Truncated coefficient perturbation `β^{(N)} = ∑_{j ≤ N} β_j`. -/
def βN (N : ℕ) (t x : ℝ) : ℝ := ∑ j ∈ Finset.range (N + 1), βblock D j t x

/-- Spatial derivative of `β^{(N)}`. -/
def βxN (N : ℕ) (t x : ℝ) : ℝ := ∑ j ∈ Finset.range (N + 1), βxblock D j t x

/-- Truncated coefficient `𝔞_N = 1 + ε β^{(N)}`. -/
def aN (N : ℕ) (ε : ℝ) (t x : ℝ) : ℝ := 1 + ε * βN D N t x

/-- Truncated oscillatory part `v^{(N)} = ∑_{j ≤ N} v_j`. -/
def vN (N : ℕ) (ε : ℝ) (t x : ℝ) : ℝ := ∑ j ∈ Finset.range (N + 1), vblock D ε j t x

/-- Truncated solution `u_N = ρ φ + v^{(N)}`. -/
def uN (N : ℕ) (ε : ℝ) (t x : ℝ) : ℝ := D.ρ t * φ x + vN D N ε t x

/-- `∂_t u_N`. -/
def utN (N : ℕ) (ε : ℝ) (t x : ℝ) : ℝ :=
  D.ρ' t * φ x + ∑ j ∈ Finset.range (N + 1), vtblock D ε j t x

/-- `∂_x u_N`. -/
def uxN (N : ℕ) (ε : ℝ) (t x : ℝ) : ℝ :=
  D.ρ t * φ' x + ∑ j ∈ Finset.range (N + 1), vxblock D ε j t x

/-- `∂_x² u_N`. -/
def uxxN (N : ℕ) (ε : ℝ) (t x : ℝ) : ℝ :=
  D.ρ t * φ'' x + ∑ j ∈ Finset.range (N + 1), vxxblock D ε j t x

/-- `𝒜_N(t) u_N(t) = -∂_x(𝔞_N ∂_x u_N)`. -/
def AuN (N : ℕ) (ε : ℝ) (t x : ℝ) : ℝ :=
  -(ε * βxN D N t x * uxN D N ε t x) - aN D N ε t x * uxxN D N ε t x

/-- The truncated forcing `f_N := ∂_t u_N + 𝒜_N(t) u_N`. -/
def fN (N : ℕ) (ε : ℝ) (t x : ℝ) : ℝ := utN D N ε t x + AuN D N ε t x

/-! ## The truncated supports -/

/-- Blocks after `N` are inactive before `τ_{N+1}`. -/
theorem notMem_I_of_gt {N j : ℕ} (hj : N < j) {t : ℝ} (ht : t ≤ τ (N + 1)) : t ∉ I j := by
  intro hmem
  obtain ⟨h1, _⟩ := Set.mem_Ioo.1 (show t ∈ Set.Ioo (τ j) (τ (j + 1)) from hmem)
  have h2 : τ (N + 1) ≤ τ j := τ_mono (by omega) hj
  linarith

/-- Blocks up to `N` are inactive after `τ_{N+1}`. -/
theorem notMem_I_of_le {N j : ℕ} (hj : j ≤ N) {t : ℝ} (ht : τ (N + 1) ≤ t) : t ∉ I j := by
  intro hmem
  obtain ⟨_, h2⟩ := Set.mem_Ioo.1 (show t ∈ Set.Ioo (τ j) (τ (j + 1)) from hmem)
  have hj1 : 1 ≤ j := one_le_of_mem_I hmem
  have h3 : τ (j + 1) ≤ τ (N + 1) := τ_mono (by omega) (by omega)
  linarith

theorem notMem_I_τ (N j : ℕ) : τ (N + 1) ∉ I j := by
  by_cases h : j ≤ N
  · exact notMem_I_of_le h le_rfl
  · exact notMem_I_of_gt (by omega) le_rfl

/-- The truncated sum of block quantities equals the full `finsum` before `τ_{N+1}`. -/
theorem blockSum_eq_finsum {g : ℕ → ℝ → ℝ → ℝ} (hg : ∀ j t x, t ∉ I j → g j t x = 0)
    (N : ℕ) {t : ℝ} (ht : t ≤ τ (N + 1)) (x : ℝ) :
    ∑ j ∈ Finset.range (N + 1), g j t x = ∑ᶠ j, g j t x := by
  by_cases hex : ∃ j, t ∈ I j
  · obtain ⟨j, hj⟩ := hex
    have hjN : j ≤ N := by
      by_contra hcon
      exact notMem_I_of_gt (by omega) ht hj
    have h1 : ∑ i ∈ Finset.range (N + 1), g i t x = g j t x :=
      Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (by omega))
        (fun i _ hij => hg i t x (notMem_I_of_mem_I hj hij))
    have h2 : ∑ᶠ i, g i t x = g j t x :=
      finsum_eq_single (fun i => g i t x) j fun i hij => hg i t x (notMem_I_of_mem_I hj hij)
    rw [h1, h2]
  · simp only [not_exists] at hex
    rw [Finset.sum_eq_zero (fun i _ => hg i t x (hex i)),
      finsum_eq_zero_of_forall_eq_zero (f := fun i => g i t x) (fun i => hg i t x (hex i))]

/-- The truncated sum of block quantities vanishes after `τ_{N+1}`. -/
theorem blockSum_eq_zero {g : ℕ → ℝ → ℝ → ℝ} (hg : ∀ j t x, t ∉ I j → g j t x = 0)
    (N : ℕ) {t : ℝ} (ht : τ (N + 1) ≤ t) (x : ℝ) :
    ∑ j ∈ Finset.range (N + 1), g j t x = 0 :=
  Finset.sum_eq_zero fun i hi =>
    hg i t x (notMem_I_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) ht)

/-! ## Identification with the full objects -/

theorem βN_eq_β (N : ℕ) {t : ℝ} (ht : t ≤ τ (N + 1)) (x : ℝ) : βN D N t x = β D t x := by
  show ∑ j ∈ Finset.range (N + 1), βblock D j t x = ∑ᶠ j, βblock D j t x
  exact blockSum_eq_finsum (g := fun j t x => βblock D j t x)
    (fun _ _ x h => βblock_eq_zero D h x) N ht x

theorem βN_eq_zero (N : ℕ) {t : ℝ} (ht : τ (N + 1) ≤ t) (x : ℝ) : βN D N t x = 0 :=
  blockSum_eq_zero (g := fun j t x => βblock D j t x)
    (fun _ _ x h => βblock_eq_zero D h x) N ht x

theorem βxN_eq_βx (N : ℕ) {t : ℝ} (ht : t ≤ τ (N + 1)) (x : ℝ) : βxN D N t x = βx D t x := by
  show ∑ j ∈ Finset.range (N + 1), βxblock D j t x = ∑ᶠ j, βxblock D j t x
  exact blockSum_eq_finsum (g := fun j t x => βxblock D j t x)
    (fun _ _ x h => βxblock_eq_zero D h x) N ht x

theorem βxN_eq_zero (N : ℕ) {t : ℝ} (ht : τ (N + 1) ≤ t) (x : ℝ) : βxN D N t x = 0 :=
  blockSum_eq_zero (g := fun j t x => βxblock D j t x)
    (fun _ _ x h => βxblock_eq_zero D h x) N ht x

theorem vtN_eq_vt (N : ℕ) (ε : ℝ) {t : ℝ} (ht : t ≤ τ (N + 1)) (x : ℝ) :
    ∑ j ∈ Finset.range (N + 1), vtblock D ε j t x = vt D ε t x :=
  blockSum_eq_finsum (g := fun j t x => vtblock D ε j t x)
    (fun _ _ x h => vtblock_eq_zero D ε h x) N ht x

theorem vtN_eq_zero (N : ℕ) (ε : ℝ) {t : ℝ} (ht : τ (N + 1) ≤ t) (x : ℝ) :
    ∑ j ∈ Finset.range (N + 1), vtblock D ε j t x = 0 :=
  blockSum_eq_zero (g := fun j t x => vtblock D ε j t x)
    (fun _ _ x h => vtblock_eq_zero D ε h x) N ht x

theorem vxN_eq_vx (N : ℕ) (ε : ℝ) {t : ℝ} (ht : t ≤ τ (N + 1)) (x : ℝ) :
    ∑ j ∈ Finset.range (N + 1), vxblock D ε j t x = vx D ε t x :=
  blockSum_eq_finsum (g := fun j t x => vxblock D ε j t x)
    (fun _ _ x h => vxblock_eq_zero D ε h x) N ht x

theorem vxN_eq_zero (N : ℕ) (ε : ℝ) {t : ℝ} (ht : τ (N + 1) ≤ t) (x : ℝ) :
    ∑ j ∈ Finset.range (N + 1), vxblock D ε j t x = 0 :=
  blockSum_eq_zero (g := fun j t x => vxblock D ε j t x)
    (fun _ _ x h => vxblock_eq_zero D ε h x) N ht x

theorem vxxN_eq_vxx (N : ℕ) (ε : ℝ) {t : ℝ} (ht : t ≤ τ (N + 1)) (x : ℝ) :
    ∑ j ∈ Finset.range (N + 1), vxxblock D ε j t x = vxx D ε t x :=
  blockSum_eq_finsum (g := fun j t x => vxxblock D ε j t x)
    (fun _ _ x h => vxxblock_eq_zero D ε h x) N ht x

theorem vxxN_eq_zero (N : ℕ) (ε : ℝ) {t : ℝ} (ht : τ (N + 1) ≤ t) (x : ℝ) :
    ∑ j ∈ Finset.range (N + 1), vxxblock D ε j t x = 0 :=
  blockSum_eq_zero (g := fun j t x => vxxblock D ε j t x)
    (fun _ _ x h => vxxblock_eq_zero D ε h x) N ht x

theorem utN_eq_ut_of_le (N : ℕ) (ε : ℝ) {t : ℝ} (ht : t ≤ τ (N + 1)) (x : ℝ) :
    utN D N ε t x = ut D ε t x := by
  show D.ρ' t * φ x + ∑ j ∈ Finset.range (N + 1), vtblock D ε j t x = D.ρ' t * φ x + vt D ε t x
  rw [vtN_eq_vt D N ε ht x]

theorem uxN_eq_ux_of_le (N : ℕ) (ε : ℝ) {t : ℝ} (ht : t ≤ τ (N + 1)) (x : ℝ) :
    uxN D N ε t x = ux D ε t x := by
  show D.ρ t * φ' x + ∑ j ∈ Finset.range (N + 1), vxblock D ε j t x = D.ρ t * φ' x + vx D ε t x
  rw [vxN_eq_vx D N ε ht x]

theorem uxxN_eq_uxx_of_le (N : ℕ) (ε : ℝ) {t : ℝ} (ht : t ≤ τ (N + 1)) (x : ℝ) :
    uxxN D N ε t x = uxx D ε t x := by
  show D.ρ t * φ'' x + ∑ j ∈ Finset.range (N + 1), vxxblock D ε j t x
      = D.ρ t * φ'' x + vxx D ε t x
  rw [vxxN_eq_vxx D N ε ht x]

theorem aN_eq_a_of_le (N : ℕ) (ε : ℝ) {t : ℝ} (ht : t ≤ τ (N + 1)) (x : ℝ) :
    aN D N ε t x = a D ε t x := by
  show 1 + ε * βN D N t x = 1 + ε * β D t x
  rw [βN_eq_β D N ht x]

theorem AuN_eq_Au_of_le (N : ℕ) (ε : ℝ) {t : ℝ} (ht : t ≤ τ (N + 1)) (x : ℝ) :
    AuN D N ε t x = Au D ε t x := by
  show -(ε * βxN D N t x * uxN D N ε t x) - aN D N ε t x * uxxN D N ε t x
      = -(ε * βx D t x * ux D ε t x) - a D ε t x * uxx D ε t x
  rw [βxN_eq_βx D N ht x, uxN_eq_ux_of_le D N ε ht x, aN_eq_a_of_le D N ε ht x,
    uxxN_eq_uxx_of_le D N ε ht x]

theorem fN_eq_f_of_le (N : ℕ) (ε : ℝ) {t : ℝ} (ht : t ≤ τ (N + 1)) (x : ℝ) :
    fN D N ε t x = f D ε t x := by
  show utN D N ε t x + AuN D N ε t x = f D ε t x
  rw [utN_eq_ut_of_le D N ε ht x, AuN_eq_Au_of_le D N ε ht x]
  exact pde D ε t x

/-- After `τ_{N+1}` the truncated forcing is the unperturbed one. -/
theorem fN_eq_f0_of_ge (N : ℕ) (ε : ℝ) {t : ℝ} (ht : τ (N + 1) ≤ t) (x : ℝ) :
    fN D N ε t x = f0 D t x := by
  have hβ : βN D N t x = 0 := βN_eq_zero D N ht x
  have hβx : βxN D N t x = 0 := βxN_eq_zero D N ht x
  have hvt : ∑ j ∈ Finset.range (N + 1), vtblock D ε j t x = 0 := vtN_eq_zero D N ε ht x
  have hvx : ∑ j ∈ Finset.range (N + 1), vxblock D ε j t x = 0 := vxN_eq_zero D N ε ht x
  have hvxx : ∑ j ∈ Finset.range (N + 1), vxxblock D ε j t x = 0 := vxxN_eq_zero D N ε ht x
  show utN D N ε t x + AuN D N ε t x = f0 D t x
  show (D.ρ' t * φ x + ∑ j ∈ Finset.range (N + 1), vtblock D ε j t x)
      + (-(ε * βxN D N t x * uxN D N ε t x) - aN D N ε t x * uxxN D N ε t x)
      = D.ρ' t * φ x - D.ρ t * φ'' x
  have haN : aN D N ε t x = 1 := by show 1 + ε * βN D N t x = 1; rw [hβ]; ring
  have huxx : uxxN D N ε t x = D.ρ t * φ'' x := by
    show D.ρ t * φ'' x + ∑ j ∈ Finset.range (N + 1), vxxblock D ε j t x = D.ρ t * φ'' x
    rw [hvxx, add_zero]
  rw [hvt, hβx, haN, huxx]
  ring

/-! ## Regularity of the truncated objects -/

theorem hasDerivAt_uN_x (N : ℕ) (ε : ℝ) (t x : ℝ) :
    HasDerivAt (fun x => uN D N ε t x) (uxN D N ε t x) x := by
  have h1 : HasDerivAt (fun x => D.ρ t * φ x) (D.ρ t * φ' x) x :=
    (hasDerivAt_φ x).const_mul (D.ρ t)
  have h2 : HasDerivAt (fun x => ∑ j ∈ Finset.range (N + 1), vblock D ε j t x)
      (∑ j ∈ Finset.range (N + 1), vxblock D ε j t x) x :=
    HasDerivAt.fun_sum fun j _ => hasDerivAt_vblock_x D ε j t x
  exact h1.add h2

theorem hasDerivAt_uxN_x (N : ℕ) (ε : ℝ) (t x : ℝ) :
    HasDerivAt (fun x => uxN D N ε t x) (uxxN D N ε t x) x := by
  have h1 : HasDerivAt (fun x => D.ρ t * φ' x) (D.ρ t * φ'' x) x :=
    (hasDerivAt_φ' x).const_mul (D.ρ t)
  have h2 : HasDerivAt (fun x => ∑ j ∈ Finset.range (N + 1), vxblock D ε j t x)
      (∑ j ∈ Finset.range (N + 1), vxxblock D ε j t x) x :=
    HasDerivAt.fun_sum fun j _ => hasDerivAt_vxblock_x D ε j t x
  exact h1.add h2

theorem hasDerivAt_βN_x (N : ℕ) (t x : ℝ) :
    HasDerivAt (fun x => βN D N t x) (βxN D N t x) x := by
  show HasDerivAt (fun x => ∑ j ∈ Finset.range (N + 1), βblock D j t x)
    (∑ j ∈ Finset.range (N + 1), βxblock D j t x) x
  exact HasDerivAt.fun_sum fun j _ => hasDerivAt_βblock_x D j t x

theorem hasDerivAt_aN_x (N : ℕ) (ε : ℝ) (t x : ℝ) :
    HasDerivAt (fun x => aN D N ε t x) (ε * βxN D N t x) x := by
  have h := (hasDerivAt_βN_x D N t x).const_mul ε
  exact (h.const_add (1 : ℝ))

/-! ## Joint continuity -/

theorem continuous_βN (N : ℕ) : Continuous (fun q : ℝ × ℝ => βN D N q.1 q.2) :=
  continuous_finsetSum _ fun j _ => continuous_βblock D j

theorem continuous_βxN (N : ℕ) : Continuous (fun q : ℝ × ℝ => βxN D N q.1 q.2) :=
  continuous_finsetSum _ fun j _ => continuous_βxblock D j

theorem continuous_aN (N : ℕ) (ε : ℝ) : Continuous (fun q : ℝ × ℝ => aN D N ε q.1 q.2) := by
  have h := continuous_βN D N
  show Continuous fun q : ℝ × ℝ => 1 + ε * βN D N q.1 q.2
  fun_prop

theorem continuous_uxN (N : ℕ) (ε : ℝ) : Continuous (fun q : ℝ × ℝ => uxN D N ε q.1 q.2) := by
  have h1 : Continuous D.ρ := continuous_ρ D
  have h2 : Continuous φ' := continuous_φ'
  have h3 : Continuous (fun q : ℝ × ℝ => ∑ j ∈ Finset.range (N + 1), vxblock D ε j q.1 q.2) :=
    continuous_finsetSum _ fun j _ => continuous_vxblock D ε j
  show Continuous fun q : ℝ × ℝ =>
    D.ρ q.1 * φ' q.2 + ∑ j ∈ Finset.range (N + 1), vxblock D ε j q.1 q.2
  fun_prop

theorem continuous_uxxN (N : ℕ) (ε : ℝ) : Continuous (fun q : ℝ × ℝ => uxxN D N ε q.1 q.2) := by
  have h1 : Continuous D.ρ := continuous_ρ D
  have h2 : Continuous φ'' := continuous_φ''
  have h3 : Continuous (fun q : ℝ × ℝ => ∑ j ∈ Finset.range (N + 1), vxxblock D ε j q.1 q.2) :=
    continuous_finsetSum _ fun j _ => continuous_vxxblock D ε j
  show Continuous fun q : ℝ × ℝ =>
    D.ρ q.1 * φ'' q.2 + ∑ j ∈ Finset.range (N + 1), vxxblock D ε j q.1 q.2
  fun_prop

theorem continuous_utN (N : ℕ) (ε : ℝ) : Continuous (fun q : ℝ × ℝ => utN D N ε q.1 q.2) := by
  have h1 : Continuous D.ρ' := D.ρ'_continuous
  have h2 : Continuous φ := continuous_φ
  have h3 : Continuous (fun q : ℝ × ℝ => ∑ j ∈ Finset.range (N + 1), vtblock D ε j q.1 q.2) :=
    continuous_finsetSum _ fun j _ => continuous_vtblock D ε j
  show Continuous fun q : ℝ × ℝ =>
    D.ρ' q.1 * φ q.2 + ∑ j ∈ Finset.range (N + 1), vtblock D ε j q.1 q.2
  fun_prop

theorem continuous_AuN (N : ℕ) (ε : ℝ) : Continuous (fun q : ℝ × ℝ => AuN D N ε q.1 q.2) := by
  have h1 := continuous_βxN D N
  have h2 := continuous_uxN D N ε
  have h3 := continuous_aN D N ε
  have h4 := continuous_uxxN D N ε
  show Continuous fun q : ℝ × ℝ =>
    -(ε * βxN D N q.1 q.2 * uxN D N ε q.1 q.2) - aN D N ε q.1 q.2 * uxxN D N ε q.1 q.2
  fun_prop

theorem continuous_fN (N : ℕ) (ε : ℝ) : Continuous (fun q : ℝ × ℝ => fN D N ε q.1 q.2) :=
  (continuous_utN D N ε).add (continuous_AuN D N ε)

theorem continuous_fN_x (N : ℕ) (ε t : ℝ) : Continuous (fun x => fN D N ε t x) :=
  (continuous_fN D N ε).comp (continuous_const.prodMk continuous_id)

theorem continuous_utN_x (N : ℕ) (ε t : ℝ) : Continuous (fun x => utN D N ε t x) :=
  (continuous_utN D N ε).comp (continuous_const.prodMk continuous_id)

/-! ## Boundary and initial values -/

theorem uN_initial (N : ℕ) (ε x : ℝ) : uN D N ε 0 x = 0 := by
  have h2 : ∑ j ∈ Finset.range (N + 1), vblock D ε j 0 x = 0 :=
    Finset.sum_eq_zero fun j _ => vblock_eq_zero_of_ηj D ε (ηj_at_zero D j) x
  show D.ρ 0 * φ x + ∑ j ∈ Finset.range (N + 1), vblock D ε j 0 x = 0
  rw [h2, ρ_zero D]
  ring

theorem uN_zero_left (N : ℕ) (ε t : ℝ) : uN D N ε t 0 = 0 := by
  have h2 : ∑ j ∈ Finset.range (N + 1), vblock D ε j t 0 = 0 :=
    Finset.sum_eq_zero fun j _ => by simp [vblock, p_zero]
  show D.ρ t * φ 0 + ∑ j ∈ Finset.range (N + 1), vblock D ε j t 0 = 0
  rw [h2, φ_zero]
  ring

theorem uN_zero_right (N : ℕ) (ε t : ℝ) : uN D N ε t π = 0 := by
  have h2 : ∑ j ∈ Finset.range (N + 1), vblock D ε j t π = 0 :=
    Finset.sum_eq_zero fun j _ => by simp [vblock, p_pi]
  show D.ρ t * φ π + ∑ j ∈ Finset.range (N + 1), vblock D ε j t π = 0
  rw [h2, φ_pi]
  ring

/-! ## Uniform bounds on the truncated coefficient -/

theorem abs_βN_le (N : ℕ) (t x : ℝ) : |βN D N t x| ≤ 1 / 480 := by
  rcases le_total t (τ (N + 1)) with h | h
  · rw [βN_eq_β D N h x]
    exact abs_β_le D t x
  · rw [βN_eq_zero D N h x, abs_zero]
    norm_num

theorem abs_aN_sub_one_le {ε : ℝ} (hε0 : 0 ≤ ε) (N : ℕ) (t x : ℝ) :
    |aN D N ε t x - 1| ≤ ε / 480 := by
  have h : aN D N ε t x - 1 = ε * βN D N t x := by
    show 1 + ε * βN D N t x - 1 = ε * βN D N t x
    ring
  rw [h, abs_mul, abs_of_nonneg hε0]
  have := abs_βN_le D N t x
  have : ε * |βN D N t x| ≤ ε * (1 / 480) := by
    exact mul_le_mul_of_nonneg_left (abs_βN_le D N t x) hε0
  linarith

theorem abs_min_sub_min (a b c : ℝ) : |min a c - min b c| ≤ |a - b| := by
  have hp := le_abs_self (a - b)
  have hn := neg_abs_le (a - b)
  have h0 := abs_nonneg (a - b)
  rcases le_total a c with h1 | h1 <;> rcases le_total b c with h2 | h2
  · rw [min_eq_left h1, min_eq_left h2]
  · rw [min_eq_left h1, min_eq_right h2, abs_le]
    constructor <;> linarith
  · rw [min_eq_right h1, min_eq_left h2, abs_le]
    constructor <;> linarith
  · rw [min_eq_right h1, min_eq_right h2, abs_le]
    constructor <;> linarith

/-- The truncated perturbation is the full one evaluated at the truncated time. -/
theorem βN_eq_β_min (N : ℕ) (t x : ℝ) : βN D N t x = β D (min t (τ (N + 1))) x := by
  rcases le_total t (τ (N + 1)) with h | h
  · rw [min_eq_left h, βN_eq_β D N h x]
  · rw [min_eq_right h, βN_eq_zero D N h x]
    exact (β_eq_zero D (fun j => notMem_I_τ N j) x).symm

theorem abs_aN_sub_le (N : ℕ) (ε : ℝ) (s t x : ℝ) :
    |aN D N ε t x - aN D N ε s x| ≤ 2 * |ε| * Cβ D * Real.sqrt |t - s| := by
  set σ := τ (N + 1) with hσ
  have h1 : aN D N ε t x - aN D N ε s x
      = ε * (β D (min t σ) x - β D (min s σ) x) := by
    show (1 + ε * βN D N t x) - (1 + ε * βN D N s x) = ε * (β D (min t σ) x - β D (min s σ) x)
    rw [βN_eq_β_min D N t x, βN_eq_β_min D N s x]
    ring
  have h2 : |β D (min t σ) x - β D (min s σ) x|
      ≤ 2 * Cβ D * Real.sqrt |min t σ - min s σ| := abs_β_sub_le D _ _ _
  have h3 : Real.sqrt |min t σ - min s σ| ≤ Real.sqrt |t - s| :=
    Real.sqrt_le_sqrt (abs_min_sub_min t s σ)
  have h4 : (0 : ℝ) ≤ Cβ D := Cβ_nonneg D
  rw [h1, abs_mul]
  calc |ε| * |β D (min t σ) x - β D (min s σ) x|
      ≤ |ε| * (2 * Cβ D * Real.sqrt |t - s|) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ε)
        refine h2.trans ?_
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 * |ε| * Cβ D * Real.sqrt |t - s| := by ring

/-! ## Uniform bounds on the truncated forcing -/

theorem abs_fN_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (N : ℕ) (t x : ℝ) :
    |fN D N ε t x| ≤ Cf D := by
  rcases le_total t (τ (N + 1)) with h | h
  · rw [fN_eq_f_of_le D N ε h x]
    exact abs_f_le D hε0 hε1 t x
  · rw [fN_eq_f0_of_ge D N ε h x]
    have h0 := abs_f0_le D t x
    have hCη := D.Cη_nonneg
    show |f0 D t x| ≤ D.Cρ + 2 + (D.Cη + 5) + 1 / 60
    linarith

theorem normSq_fN_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (N : ℕ) (t : ℝ) :
    normSq (fN D N ε t) ≤ π * Cf D ^ 2 := by
  have hint1 : IntervalIntegrable (fun x => (fN D N ε t x) ^ 2) MeasureTheory.volume 0 π :=
    ((continuous_fN_x D N ε t).pow 2).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun _ : ℝ => (Cf D) ^ 2) MeasureTheory.volume 0 π :=
    intervalIntegrable_const
  have hmono : (∫ x in (0 : ℝ)..π, (fN D N ε t x) ^ 2) ≤ ∫ _ in (0 : ℝ)..π, (Cf D) ^ 2 := by
    refine intervalIntegral.integral_mono_on Real.pi_pos.le hint1 hint2 fun x _ => ?_
    have h := abs_fN_le D hε0 hε1 N t x
    nlinarith [abs_nonneg (fN D N ε t x), sq_abs (fN D N ε t x)]
  rw [intervalIntegral.integral_const] at hmono
  simpa [normSq, smul_eq_mul] using hmono

/-! ## Continuity of the `L²`-norms in time -/

theorem continuous_normSq_fN (N : ℕ) (ε : ℝ) : Continuous (fun t => normSq (fN D N ε t)) := by
  have hc : Continuous (Function.uncurry fun t x => (fN D N ε t x) ^ 2) := by
    exact (continuous_fN D N ε).pow 2
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 π

theorem continuous_normSq_utN (N : ℕ) (ε : ℝ) : Continuous (fun t => normSq (utN D N ε t)) := by
  have hc : Continuous (Function.uncurry fun t x => (utN D N ε t x) ^ 2) := by
    exact (continuous_utN D N ε).pow 2
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 π

/-- `‖f_N‖²_{L²(0,1;H)} ≤ π Cf²`, uniformly in `N`. -/
theorem integral_normSq_fN_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (N : ℕ) :
    ∫ t in (0 : ℝ)..1, normSq (fN D N ε t) ≤ π * Cf D ^ 2 := by
  have hcont := continuous_normSq_fN D N ε
  have hmono : (∫ t in (0 : ℝ)..1, normSq (fN D N ε t))
      ≤ ∫ _ in (0 : ℝ)..1, π * Cf D ^ 2 :=
    intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable _ _)
      intervalIntegrable_const fun t _ => normSq_fN_le D hε0 hε1 N t
  rw [intervalIntegral.integral_const] at hmono
  simpa using hmono

/-! ## The lower bound on the middle thirds -/

theorem sum_integral_J_le {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), g t)
      ≤ ∫ t in (τ 1)..(τ (N + 1)), g t := by
  induction N with
  | zero =>
      have hIcc : Finset.Icc 1 0 = (∅ : Finset ℕ) := by decide
      rw [hIcc, Finset.sum_empty]
      simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hℓ : 0 < ℓ (n + 1) := ℓ_pos (by omega)
      have hτ : τ (n + 1) + ℓ (n + 1) = τ (n + 1 + 1) := τ_add_ℓ (by omega)
      have h1 : (∫ t in (τ (n + 1) + ℓ (n + 1) / 3)..(τ (n + 1) + 2 * ℓ (n + 1) / 3), g t)
          ≤ ∫ t in (τ (n + 1))..(τ (n + 1 + 1)), g t :=
        intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
          (Filter.Eventually.of_forall hg0) (hg.intervalIntegrable _ _)
      have h2 : (∫ t in (τ 1)..(τ (n + 1)), g t) + (∫ t in (τ (n + 1))..(τ (n + 1 + 1)), g t)
          = ∫ t in (τ 1)..(τ (n + 1 + 1)), g t :=
        intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _)
          (hg.intervalIntegrable _ _)
      linarith

theorem sum_integral_J_le_unit {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), g t)
      ≤ ∫ t in (0 : ℝ)..1, g t := by
  refine (sum_integral_J_le hg hg0 N).trans ?_
  have h1 : (0 : ℝ) ≤ τ 1 := by rw [τ_one]; norm_num
  have h2 : τ 1 ≤ τ (N + 1) := τ_mono (by omega) (by omega)
  have h3 : τ (N + 1) ≤ 1 := by
    have := τ_lt (j := N + 1) (by omega)
    linarith
  exact intervalIntegral.integral_mono_interval h1 h2 h3
    (Filter.Eventually.of_forall hg0) (hg.intervalIntegrable _ _)

/-- `‖∂_t u_N‖²_{L²(0,1;H)} ≥ (π ε²/1536) ∑_{j=1}^N 1/(j+1)`. -/
theorem integral_normSq_utN_ge (ε : ℝ) (N : ℕ) :
    π * ε ^ 2 / 1536 * ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / ((j : ℝ) + 1)
      ≤ ∫ t in (0 : ℝ)..1, normSq (utN D N ε t) := by
  have hcont := continuous_normSq_utN D N ε
  have hnn : ∀ t, 0 ≤ normSq (utN D N ε t) := fun t => normSq_nonneg _
  have hstep : ∀ j ∈ Finset.Icc 1 N,
      π * ε ^ 2 / 1536 * ((1 : ℝ) / ((j : ℝ) + 1))
        ≤ ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), normSq (utN D N ε t) := by
    intro j hj
    obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.mp hj
    have hℓ : 0 < ℓ j := ℓ_pos hj1
    have hcongr : (∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), normSq (utN D N ε t))
        = ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), utNormSq D ε t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by linarith)] at ht
      obtain ⟨_, ht2⟩ := Set.mem_Icc.1 ht
      have htle : t ≤ τ (N + 1) := by
        have ha : τ (j + 1) ≤ τ (N + 1) := τ_mono (by omega) (by omega)
        have hb : τ j + ℓ j = τ (j + 1) := τ_add_ℓ hj1
        linarith
      have heq : utN D N ε t = ut D ε t := funext fun x => utN_eq_ut_of_le D N ε htle x
      show normSq (utN D N ε t) = normSq (ut D ε t)
      rw [heq]
    rw [hcongr]
    have hmain := integral_utNormSq_J D ε hj1
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have heq2 : π * ε ^ 2 / 1536 * ((1 : ℝ) / ((j : ℝ) + 1))
        = π * ε ^ 2 / (1536 * ((j : ℝ) + 1)) := by
      field_simp
    rw [heq2]
    exact hmain
  calc π * ε ^ 2 / 1536 * ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / ((j : ℝ) + 1)
      = ∑ j ∈ Finset.Icc 1 N, π * ε ^ 2 / 1536 * ((1 : ℝ) / ((j : ℝ) + 1)) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 N,
          ∫ t in (τ j + ℓ j / 3)..(τ j + 2 * ℓ j / 3), normSq (utN D N ε t) :=
        Finset.sum_le_sum hstep
    _ ≤ ∫ t in (0 : ℝ)..1, normSq (utN D N ε t) := sum_integral_J_le_unit hcont hnn N

/-! ## Logarithmic growth -/

/-- `∑_{j=1}^N 1/(j+1) ≥ log(N+2) − 1`. -/
theorem sum_inv_succ_ge_log (N : ℕ) :
    Real.log ((N : ℝ) + 2) - 1 ≤ ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / ((j : ℝ) + 1) := by
  have hH : Real.log ((N : ℝ) + 2) ≤ ((harmonic (N + 1) : ℚ) : ℝ) := by
    have h := log_add_one_le_harmonic (N + 1)
    have hc : ((N + 1 + 1 : ℕ) : ℝ) = (N : ℝ) + 2 := by push_cast; ring
    rwa [hc] at h
  have hsplit : ((harmonic (N + 1) : ℚ) : ℝ)
      = 1 + ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / ((j : ℝ) + 1) := by
    have hrange : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have h0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
    rw [harmonic]
    push_cast
    rw [hrange, Finset.sum_insert h0]
    norm_num [one_div]
  linarith

/-- Growth of the maximal-regularity constant. -/
theorem maximal_regularity_constant_growth (ε : ℝ) (N : ℕ) :
    π * ε ^ 2 / 1536 * (Real.log ((N : ℝ) + 2) - 1)
      ≤ ∫ t in (0 : ℝ)..1, normSq (utN D N ε t) := by
  refine le_trans ?_ (integral_normSq_utN_ge D ε N)
  have hc : (0 : ℝ) ≤ π * ε ^ 2 / 1536 := by positivity
  exact mul_le_mul_of_nonneg_left (sum_inv_succ_ge_log N) hc

end LionsC12

end

