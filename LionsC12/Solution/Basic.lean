module

public import LionsC12.Construction.Defs
public import LionsC12.Coefficient.Blocks
public import LionsC12.Coefficient.Support
public import LionsC12.Modes.Trig
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Topology.Algebra.Order.Group

/-!
# Section 4: the candidate solution, its derivatives, and the ODE (4.2)

This file contains the differential calculus for the candidate solution
`u = ρ φ + v`:

* the derivative of the phase `θ_{j,m}` and of the mode amplitudes `y_{j,m}`,
* the ODE (4.2) `y' + K² y = -ε η_j sin θ + r`,
* the pointwise bounds on `y`, `r`, `y'`,
* all spatial derivatives (blockwise and globally),
* the time derivative of `u` at every time,
* the boundary and initial values,
* formula (4.6) for `∂_t u` on the middle third `J_j`.
-/


@[expose] public section

noncomputable section

namespace LionsC12

open Real

variable (D : Cutoffs)

/-! ## Elementary trigonometric bounds -/

private lemma abs_sin_sub_cos_le (z : ℝ) : |sin z - cos z| ≤ 2 := by
  have h1 := neg_one_le_sin z
  have h2 := sin_le_one z
  have h3 := neg_one_le_cos z
  have h4 := cos_le_one z
  rw [abs_le]
  constructor <;> linarith

private lemma abs_cos_add_sin_le (z : ℝ) : |cos z + sin z| ≤ 2 := by
  have h1 := neg_one_le_sin z
  have h2 := sin_le_one z
  have h3 := neg_one_le_cos z
  have h4 := cos_le_one z
  rw [abs_le]
  constructor <;> linarith

/-! ## The phase and the mode amplitudes -/

theorem hasDerivAt_θ (j m : ℕ) (t : ℝ) : HasDerivAt (θ j m) ((K j m : ℝ) ^ 2) t := by
  have h : HasDerivAt (fun s : ℝ => (K j m : ℝ) ^ 2 * (s - τ j)) ((K j m : ℝ) ^ 2 * 1) t :=
    HasDerivAt.const_mul _ ((hasDerivAt_id' t).sub_const (τ j))
  rw [mul_one] at h
  exact h

theorem hasDerivAt_y (ε : ℝ) (j m : ℕ) (t : ℝ) :
    HasDerivAt (y D ε j m) (y' D ε j m t) t := by
  have hθ : HasDerivAt (θ j m) ((K j m : ℝ) ^ 2) t := hasDerivAt_θ j m t
  have hsc : HasDerivAt (fun s => sin (θ j m s) - cos (θ j m s))
      (cos (θ j m t) * (K j m : ℝ) ^ 2 - -sin (θ j m t) * (K j m : ℝ) ^ 2) t :=
    HasDerivAt.fun_sub hθ.sin hθ.cos
  have hη : HasDerivAt (ηj D j) (ηj' D j t) t := hasDerivAt_ηj D j t
  have key := HasDerivAt.fun_mul (hη.const_mul (-(ε / (2 * (K j m : ℝ) ^ 2)))) hsc
  refine key.congr_deriv ?_
  simp only [y']
  ring

/-- Equation (4.2). -/
theorem y_ode (ε : ℝ) (j m : ℕ) (t : ℝ) :
    y' D ε j m t + (K j m : ℝ) ^ 2 * y D ε j m t
      = -ε * ηj D j t * sin (θ j m t) + r D ε j m t := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [y, y', r, ηj_zero_block, ηj'_zero_block]
  · have hKpos : (0 : ℝ) < (K j m : ℝ) := by exact_mod_cast K_pos hj
    have hk2 : ((K j m : ℝ)) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hKpos)
    simp only [y, y', r]
    field_simp
    try ring

/-! ## Bounds on `y`, `r`, `y'` -/

private lemma abs_y_le_abs (ε : ℝ) {j : ℕ} (hj : 1 ≤ j) (m : ℕ) (t : ℝ) :
    |y D ε j m t| ≤ |ε| / (K j m : ℝ) ^ 2 := by
  have hKpos : (0 : ℝ) < (K j m : ℝ) := by exact_mod_cast K_pos hj
  have hk2 : (0 : ℝ) < ((K j m : ℝ)) ^ 2 := pow_pos hKpos 2
  have hk2' : ((K j m : ℝ)) ^ 2 ≠ 0 := ne_of_gt hk2
  have hc : (0 : ℝ) ≤ |ε| / (2 * (K j m : ℝ) ^ 2) := by positivity
  have h1 : |ηj D j t| ≤ 1 := abs_ηj_le_one D j t
  calc |y D ε j m t|
      = |ε| / (2 * (K j m : ℝ) ^ 2) * |ηj D j t| * |sin (θ j m t) - cos (θ j m t)| := by
        rw [y, abs_mul, abs_mul, abs_neg, abs_div,
          abs_of_nonneg (show (0 : ℝ) ≤ 2 * (K j m : ℝ) ^ 2 by positivity)]
    _ ≤ |ε| / (2 * (K j m : ℝ) ^ 2) * 1 * 2 := by
        refine mul_le_mul ?_ (abs_sin_sub_cos_le _) (abs_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left h1 hc
    _ = |ε| / (K j m : ℝ) ^ 2 := by
        field_simp

theorem abs_y_le {ε : ℝ} (hε : 0 ≤ ε) {j : ℕ} (hj : 1 ≤ j) (m : ℕ) (t : ℝ) :
    |y D ε j m t| ≤ ε / (K j m : ℝ) ^ 2 := by
  have h := abs_y_le_abs D ε hj m t
  rwa [abs_of_nonneg hε] at h

theorem abs_r_le {ε : ℝ} (hε : 0 ≤ ε) {j : ℕ} (hj : 1 ≤ j) (m : ℕ) (t : ℝ) :
    |r D ε j m t| ≤ ε * D.Cη / ((K j m : ℝ) ^ 2 * ℓ j) := by
  have hKpos : (0 : ℝ) < (K j m : ℝ) := by exact_mod_cast K_pos hj
  have hk2 : (0 : ℝ) < ((K j m : ℝ)) ^ 2 := pow_pos hKpos 2
  have hk2' : ((K j m : ℝ)) ^ 2 ≠ 0 := ne_of_gt hk2
  have hℓ : 0 < ℓ j := ℓ_pos hj
  have hℓ' : ℓ j ≠ 0 := ne_of_gt hℓ
  have hc : (0 : ℝ) ≤ ε / (2 * (K j m : ℝ) ^ 2) := div_nonneg hε (by positivity)
  have hCη : (0 : ℝ) ≤ D.Cη / ℓ j := div_nonneg D.Cη_nonneg hℓ.le
  have h1 : |ηj' D j t| ≤ D.Cη / ℓ j := abs_ηj'_le D hj t
  calc |r D ε j m t|
      = ε / (2 * (K j m : ℝ) ^ 2) * |ηj' D j t| * |sin (θ j m t) - cos (θ j m t)| := by
        rw [r, abs_mul, abs_mul, abs_neg, abs_of_nonneg hc]
    _ ≤ ε / (2 * (K j m : ℝ) ^ 2) * (D.Cη / ℓ j) * 2 := by
        refine mul_le_mul ?_ (abs_sin_sub_cos_le _) (abs_nonneg _) (mul_nonneg hc hCη)
        exact mul_le_mul_of_nonneg_left h1 hc
    _ = ε * D.Cη / ((K j m : ℝ) ^ 2 * ℓ j) := by
        field_simp

theorem abs_y'_le {ε : ℝ} (hε : 0 ≤ ε) {j : ℕ} (hj : 1 ≤ j) (m : ℕ) (t : ℝ) :
    |y' D ε j m t| ≤ ε * (D.Cη + 1) := by
  have hKpos : (0 : ℝ) < (K j m : ℝ) := by exact_mod_cast K_pos hj
  have hk2 : (0 : ℝ) < ((K j m : ℝ)) ^ 2 := pow_pos hKpos 2
  have hk2' : ((K j m : ℝ)) ^ 2 ≠ 0 := ne_of_gt hk2
  have hℓ : 0 < ℓ j := ℓ_pos hj
  have hℓ' : ℓ j ≠ 0 := ne_of_gt hℓ
  have hkl : 1 ≤ (K j m : ℝ) ^ 2 * ℓ j := one_le_K_sq_mul_ℓ hj
  have hc : (0 : ℝ) ≤ ε / (2 * (K j m : ℝ) ^ 2) := div_nonneg hε (by positivity)
  have h1 : |ηj' D j t| ≤ D.Cη / ℓ j := abs_ηj'_le D hj t
  have h2 : |ηj D j t| ≤ 1 := abs_ηj_le_one D j t
  have hA : |ηj' D j t * (sin (θ j m t) - cos (θ j m t))| ≤ D.Cη / ℓ j * 2 := by
    rw [abs_mul]
    exact mul_le_mul h1 (abs_sin_sub_cos_le _) (abs_nonneg _) (div_nonneg D.Cη_nonneg hℓ.le)
  have hB : |ηj D j t * (K j m : ℝ) ^ 2 * (cos (θ j m t) + sin (θ j m t))|
      ≤ (K j m : ℝ) ^ 2 * 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hk2.le]
    have h3 : |ηj D j t| * (K j m : ℝ) ^ 2 ≤ 1 * (K j m : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right h2 hk2.le
    calc |ηj D j t| * (K j m : ℝ) ^ 2 * |cos (θ j m t) + sin (θ j m t)|
        ≤ 1 * (K j m : ℝ) ^ 2 * 2 :=
          mul_le_mul h3 (abs_cos_add_sin_le _) (abs_nonneg _) (by positivity)
      _ = (K j m : ℝ) ^ 2 * 2 := by ring
  have hsum : |y' D ε j m t|
      ≤ ε / (2 * (K j m : ℝ) ^ 2) * (D.Cη / ℓ j * 2 + (K j m : ℝ) ^ 2 * 2) := by
    rw [y', abs_mul, abs_neg, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hA hB)) hc
  refine hsum.trans ?_
  have hdiv : D.Cη / ((K j m : ℝ) ^ 2 * ℓ j) ≤ D.Cη := div_le_self D.Cη_nonneg hkl
  have hexp : ε / (2 * (K j m : ℝ) ^ 2) * (D.Cη / ℓ j * 2 + (K j m : ℝ) ^ 2 * 2)
      = ε * (D.Cη / ((K j m : ℝ) ^ 2 * ℓ j)) + ε := by
    field_simp
  rw [hexp]
  have h4 : ε * (D.Cη / ((K j m : ℝ) ^ 2 * ℓ j)) ≤ ε * D.Cη :=
    mul_le_mul_of_nonneg_left hdiv hε
  nlinarith

/-! ## Spatial derivatives -/

theorem hasDerivAt_βblock_x (j : ℕ) (t x : ℝ) :
    HasDerivAt (fun x => βblock D j t x) (βxblock D j t x) x := by
  simp only [βblock, βxblock]
  refine HasDerivAt.fun_sum (fun m hm => ?_)
  simp only [Finset.mem_Icc, M] at hm
  have hj : 1 ≤ j := le_trans hm.1 hm.2
  have hKR : ((K j m : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (K_pos hj).ne'
  have hcos : HasDerivAt (fun x : ℝ => cos ((K j m : ℝ) * x))
      (-sin ((K j m : ℝ) * x) * ((K j m : ℝ) * 1)) x :=
    (HasDerivAt.const_mul ((K j m : ℝ)) (hasDerivAt_id' x)).cos
  have h := hcos.const_mul (ηj D j t * ((K j m : ℝ))⁻¹ * sin (θ j m t))
  show HasDerivAt (fun x => βmode D j m t x) _ x
  refine h.congr_deriv ?_
  field_simp

theorem hasDerivAt_β_x (t x : ℝ) : HasDerivAt (fun x => β D t x) (βx D t x) x := by
  obtain ⟨j, hj⟩ := exists_block t
  by_cases ht : t ∈ I j
  · exact ((hasDerivAt_βblock_x D j t x).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => β_eq_block D ht s)).congr_deriv
        (βx_eq_block D ht x).symm
  · have hall : ∀ i, t ∉ I i := by
      intro i
      by_cases hij : i = j
      · subst hij; exact ht
      · exact hj i hij
    exact (((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => β_eq_zero D hall s)).congr_deriv
        (βx_eq_zero D hall x).symm)

theorem hasDerivAt_a_x (ε : ℝ) (t x : ℝ) :
    HasDerivAt (fun x => a D ε t x) (ε * βx D t x) x := by
  simp only [a]
  exact ((hasDerivAt_β_x D t x).const_mul ε).const_add 1

theorem hasDerivAt_vblock_x (ε : ℝ) (j : ℕ) (t x : ℝ) :
    HasDerivAt (fun x => vblock D ε j t x) (vxblock D ε j t x) x := by
  simp only [vblock, vxblock]
  exact HasDerivAt.fun_sum (fun m _ => (hasDerivAt_p (K j m) x).const_mul (y D ε j m t))

theorem hasDerivAt_vxblock_x (ε : ℝ) (j : ℕ) (t x : ℝ) :
    HasDerivAt (fun x => vxblock D ε j t x) (vxxblock D ε j t x) x := by
  simp only [vxblock, vxxblock]
  exact HasDerivAt.fun_sum (fun m _ => (hasDerivAt_p' (K j m) x).const_mul (y D ε j m t))

theorem hasDerivAt_v_x (ε : ℝ) (t x : ℝ) : HasDerivAt (fun x => v D ε t x) (vx D ε t x) x := by
  obtain ⟨j, hj⟩ := exists_block t
  by_cases ht : t ∈ I j
  · exact ((hasDerivAt_vblock_x D ε j t x).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => v_eq_block D ε ht s)).congr_deriv
        (vx_eq_block D ε ht x).symm
  · have hall : ∀ i, t ∉ I i := by
      intro i
      by_cases hij : i = j
      · subst hij; exact ht
      · exact hj i hij
    exact ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => v_eq_zero D ε hall s)).congr_deriv
        (vx_eq_zero D ε hall x).symm

theorem hasDerivAt_vx_x (ε : ℝ) (t x : ℝ) : HasDerivAt (fun x => vx D ε t x) (vxx D ε t x) x := by
  obtain ⟨j, hj⟩ := exists_block t
  by_cases ht : t ∈ I j
  · exact ((hasDerivAt_vxblock_x D ε j t x).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => vx_eq_block D ε ht s)).congr_deriv
        (vxx_eq_block D ε ht x).symm
  · have hall : ∀ i, t ∉ I i := by
      intro i
      by_cases hij : i = j
      · subst hij; exact ht
      · exact hj i hij
    exact ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => vx_eq_zero D ε hall s)).congr_deriv
        (vxx_eq_zero D ε hall x).symm

theorem hasDerivAt_u_x (ε : ℝ) (t x : ℝ) : HasDerivAt (fun x => u D ε t x) (ux D ε t x) x := by
  simp only [u, ux]
  exact HasDerivAt.fun_add ((hasDerivAt_φ x).const_mul (D.ρ t)) (hasDerivAt_v_x D ε t x)

theorem hasDerivAt_ux_x (ε : ℝ) (t x : ℝ) : HasDerivAt (fun x => ux D ε t x) (uxx D ε t x) x := by
  simp only [ux, uxx]
  exact HasDerivAt.fun_add ((hasDerivAt_φ' x).const_mul (D.ρ t)) (hasDerivAt_vx_x D ε t x)

/-- The flux `𝔞 ∂_x u` has spatial derivative `-𝒜u`. -/
theorem hasDerivAt_flux (ε : ℝ) (t x : ℝ) :
    HasDerivAt (fun x => a D ε t x * ux D ε t x) (-(Au D ε t x)) x := by
  have h := HasDerivAt.fun_mul (hasDerivAt_a_x D ε t x) (hasDerivAt_ux_x D ε t x)
  refine h.congr_deriv ?_
  simp only [Au]
  ring

/-! ## Vanishing of the oscillatory part where all cutoffs vanish -/

private lemma v_eq_zero_of_ηj (ε : ℝ) {s : ℝ} (h : ∀ i, ηj D i s = 0) (x : ℝ) :
    v D ε s x = 0 := by
  rw [v]
  exact finsum_eq_zero_of_forall_eq_zero fun i => vblock_eq_zero_of_ηj D ε (h i) x

private lemma vt_eq_zero_of_ηj (ε : ℝ) {s : ℝ} (h : ∀ i, ηj D i s = 0) (h' : ∀ i, ηj' D i s = 0)
    (x : ℝ) : vt D ε s x = 0 := by
  rw [vt]
  exact finsum_eq_zero_of_forall_eq_zero fun i => vtblock_eq_zero_of_ηj D ε (h i) (h' i) x

/-! ## Time derivatives -/

theorem hasDerivAt_vblock_t (ε : ℝ) (j : ℕ) (t x : ℝ) :
    HasDerivAt (fun t => vblock D ε j t x) (vtblock D ε j t x) t := by
  simp only [vblock, vtblock]
  exact HasDerivAt.fun_sum (fun m _ => (hasDerivAt_y D ε j m t).mul_const (p (K j m) x))

theorem hasDerivAt_u_t_of_mem_I (ε : ℝ) {j : ℕ} {t : ℝ} (ht : t ∈ I j) (x : ℝ) :
    HasDerivAt (fun t => u D ε t x) (ut D ε t x) t := by
  have hd : HasDerivAt (fun s => D.ρ s * φ x + vblock D ε j s x)
      (D.ρ' t * φ x + vtblock D ε j t x) t :=
    HasDerivAt.fun_add ((D.ρ_hasDerivAt t).mul_const (φ x)) (hasDerivAt_vblock_t D ε j t x)
  refine (hd.congr_of_eventuallyEq (u_eventuallyEq_block D ε ht x)).congr_deriv ?_
  rw [ut, vt_eq_block D ε ht x]

theorem hasDerivAt_u_t_of_notMem_Icc (ε : ℝ) {t : ℝ} (ht : t ∉ Set.Icc (1 / 4 : ℝ) (5 / 16))
    (x : ℝ) : HasDerivAt (fun t => u D ε t x) (ut D ε t x) t := by
  have hmem : (Set.Icc (1 / 4 : ℝ) (5 / 16))ᶜ ∈ nhds t := isClosed_Icc.isOpen_compl.mem_nhds ht
  have hIco : ∀ s : ℝ, s ∉ Set.Icc (1 / 4 : ℝ) (5 / 16) → ∀ i, s ∉ I i := by
    intro s hs
    refine notMem_I_of_notMem_Ico ?_
    intro hmem'
    exact hs ⟨hmem'.1, le_of_lt hmem'.2⟩
  have heq : (fun s => u D ε s x) =ᶠ[nhds t] fun s => D.ρ s * φ x := by
    filter_upwards [hmem] with s hs
    rw [u, v_eq_zero D ε (hIco s hs) x, add_zero]
  have hd : HasDerivAt (fun s => D.ρ s * φ x) (D.ρ' t * φ x) t :=
    (D.ρ_hasDerivAt t).mul_const (φ x)
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [ut, vt_eq_zero D ε (hIco t ht) x, add_zero]

/-! ### Behaviour near the block endpoints `τ j` -/

/-- At the block endpoints `τ_j` all cutoffs vanish nearby, so `u` equals `ρ φ` on a
neighbourhood of `τ_j`. -/
theorem hasDerivAt_u_t_at_τ (ε : ℝ) {j : ℕ} (hj : 1 ≤ j) (x : ℝ) :
    HasDerivAt (fun t => u D ε t x) (ut D ε (τ j) x) (τ j) := by
  have hev := eventually_ηj_zero_at_τ D hj
  have heq : (fun s => u D ε s x) =ᶠ[nhds (τ j)] fun s => D.ρ s * φ x := by
    filter_upwards [hev] with s hs
    rw [u, v_eq_zero_of_ηj D ε (fun i => (hs i).1) x, add_zero]
  have h0 := hev.self_of_nhds
  have hvt : vt D ε (τ j) x = 0 :=
    vt_eq_zero_of_ηj D ε (fun i => (h0 i).1) (fun i => (h0 i).2) x
  have hd : HasDerivAt (fun s => D.ρ s * φ x) (D.ρ' (τ j) * φ x) (τ j) :=
    (D.ρ_hasDerivAt (τ j)).mul_const (φ x)
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [ut, hvt, add_zero]

/-! ### The accumulation point `t = 5/16` -/

/-- The quadratic bound `|v(t,x)| ≤ |ε|/255 · (t - 5/16)²` used at the accumulation point. -/
private lemma abs_v_le_sq (ε : ℝ) (t x : ℝ) : |v D ε t x| ≤ |ε| / 255 * (t - 5 / 16) ^ 2 := by
  by_cases hI : ∃ j, t ∈ I j
  · obtain ⟨j, ht⟩ := hI
    have hj : 1 ≤ j := one_le_of_mem_I ht
    have hj' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hℓ : 0 < ℓ j := ℓ_pos hj
    have hle : ℓ j ≤ 5 / 16 - t := by
      have h1 : t < τ (j + 1) := ht.2
      have h2 : τ (j + 1) = 5 / 16 - 1 / (16 * ((j : ℝ) + 1)) := by
        rw [τ]
        push_cast
        try ring
      have h3 : ℓ j ≤ 1 / (16 * ((j : ℝ) + 1)) := by
        rw [ℓ]
        refine one_div_le_one_div_of_le ?_ ?_
        · nlinarith
        · nlinarith
      linarith
    have hsq : ℓ j ^ 2 ≤ (t - 5 / 16) ^ 2 := by
      have h1 : 0 ≤ 5 / 16 - t - ℓ j := by linarith
      have h2 : 0 ≤ 5 / 16 - t + ℓ j := by linarith
      nlinarith [mul_nonneg h1 h2]
    have hmain : |v D ε t x| ≤ |ε| * (ℓ j ^ 2 / 255) := by
      rw [v_eq_block D ε ht x, vblock]
      calc |∑ m ∈ Finset.Icc 1 (M j), y D ε j m t * p (K j m) x|
          ≤ ∑ m ∈ Finset.Icc 1 (M j), |y D ε j m t * p (K j m) x| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Icc 1 (M j), |ε| * ((K j m : ℝ))⁻¹ ^ 2 := by
            refine Finset.sum_le_sum fun m _ => ?_
            have hKpos : (0 : ℝ) < (K j m : ℝ) := by exact_mod_cast K_pos hj
            have h1 : |y D ε j m t| ≤ |ε| / (K j m : ℝ) ^ 2 := abs_y_le_abs D ε hj m t
            have h2 : |p (K j m) x| ≤ 1 := abs_p_le_one _ _
            rw [abs_mul]
            calc |y D ε j m t| * |p (K j m) x|
                ≤ |ε| / (K j m : ℝ) ^ 2 * 1 :=
                  mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
              _ = |ε| * ((K j m : ℝ))⁻¹ ^ 2 := by
                  rw [inv_pow, mul_one, div_eq_mul_inv]
        _ = |ε| * ∑ m ∈ Finset.Icc 1 (M j), ((K j m : ℝ))⁻¹ ^ 2 := by
            rw [Finset.mul_sum]
        _ ≤ |ε| * (ℓ j ^ 2 / 255) :=
            mul_le_mul_of_nonneg_left (sum_K_inv_sq_le hj) (abs_nonneg ε)
    refine hmain.trans ?_
    have habs : (0 : ℝ) ≤ |ε| := abs_nonneg ε
    nlinarith
  · push Not at hI
    rw [v_eq_zero D ε hI x, abs_zero]
    positivity

/-- At the accumulation point `t = 5/16` the quadratic bound `|v| ≲ (t - 5/16)²` gives
`∂_t v(5/16) = 0`. -/
theorem hasDerivAt_u_t_at_five_sixteenths (ε : ℝ) (x : ℝ) :
    HasDerivAt (fun t => u D ε t x) (ut D ε (5 / 16) x) (5 / 16) := by
  have hv0 : v D ε (5 / 16) x = 0 := v_eq_zero D ε five_sixteenths_notMem_I x
  have hvt0 : vt D ε (5 / 16) x = 0 := vt_eq_zero D ε five_sixteenths_notMem_I x
  have hvd : HasDerivAt (fun t => v D ε t x) 0 (5 / 16 : ℝ) := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hb : ∀ s : ℝ, ‖slope (fun t => v D ε t x) (5 / 16) s‖
        ≤ |ε| / 255 * |s - 5 / 16| := by
      intro s
      rcases eq_or_ne s (5 / 16 : ℝ) with rfl | hs
      · simp [slope_same]
      · have hne : s - (5 / 16 : ℝ) ≠ 0 := sub_ne_zero.mpr hs
        rw [Real.norm_eq_abs]
        simp only [slope_def_field, hv0, sub_zero]
        rw [abs_div, div_le_iff₀ (abs_pos.mpr hne)]
        calc |v D ε s x| ≤ |ε| / 255 * (s - 5 / 16) ^ 2 := abs_v_le_sq D ε s x
          _ = |ε| / 255 * |s - 5 / 16| * |s - 5 / 16| := by
              rw [← sq_abs (s - 5 / 16)]
              ring
    have htend : Filter.Tendsto (fun s : ℝ => |ε| / 255 * |s - 5 / 16|)
        (nhdsWithin (5 / 16 : ℝ) {(5 / 16 : ℝ)}ᶜ) (nhds 0) := by
      have hcont : Continuous (fun s : ℝ => |s - 5 / 16|) :=
        (continuous_id.sub continuous_const).abs
      have hlim : Filter.Tendsto (fun s : ℝ => |s - 5 / 16|) (nhds (5 / 16 : ℝ)) (nhds 0) := by
        have h := hcont.tendsto (5 / 16 : ℝ)
        simpa using h
      have h0 := hlim.const_mul (|ε| / 255)
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    exact squeeze_zero_norm hb htend
  have hd : HasDerivAt (fun t => u D ε t x) (D.ρ' (5 / 16 : ℝ) * φ x + 0) (5 / 16 : ℝ) := by
    simp only [u]
    exact HasDerivAt.fun_add ((D.ρ_hasDerivAt (5 / 16 : ℝ)).mul_const (φ x)) hvd
  refine hd.congr_deriv ?_
  rw [ut, hvt0]

theorem hasDerivAt_u_t (ε : ℝ) (t x : ℝ) :
    HasDerivAt (fun t => u D ε t x) (ut D ε t x) t := by
  by_cases hI : ∃ j, t ∈ I j
  · obtain ⟨j, hj⟩ := hI
    exact hasDerivAt_u_t_of_mem_I D ε hj x
  · push Not at hI
    by_cases hIcc : t ∈ Set.Icc (1 / 4 : ℝ) (5 / 16)
    · obtain ⟨hl, hr⟩ := hIcc
      rcases eq_or_lt_of_le hr with hEq | hlt
      · subst hEq
        exact hasDerivAt_u_t_at_five_sixteenths D ε x
      · have hw0 : (0 : ℝ) < 5 / 16 - t := by linarith
        have hge1 : (1 : ℝ) ≤ 1 / (16 * (5 / 16 - t)) := by
          rw [le_div_iff₀ (by linarith)]
          linarith
        obtain ⟨j, hj1, hfl, hfl2⟩ : ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ) ≤ 1 / (16 * (5 / 16 - t)) ∧
            1 / (16 * (5 / 16 - t)) < (j : ℝ) + 1 :=
          ⟨⌊1 / (16 * (5 / 16 - t))⌋₊, Nat.le_floor (by exact_mod_cast hge1),
            Nat.floor_le (div_nonneg zero_le_one (by linarith)), Nat.lt_floor_add_one _⟩
        have hjR : (0 : ℝ) < (j : ℝ) := by
          have hjn : 0 < j := hj1
          exact_mod_cast hjn
        have hA : τ j ≤ t := by
          rw [le_div_iff₀ (by linarith)] at hfl
          have h2 : 5 / 16 - t ≤ 1 / (16 * (j : ℝ)) := by
            rw [le_div_iff₀ (by linarith)]
            nlinarith
          rw [τ]
          linarith
        have hB : t < τ (j + 1) := by
          rw [div_lt_iff₀ (by linarith)] at hfl2
          have h2 : 1 / (16 * ((j : ℝ) + 1)) < 5 / 16 - t := by
            rw [div_lt_iff₀ (by positivity)]
            nlinarith
          rw [τ]
          push_cast
          linarith
        rcases eq_or_lt_of_le hA with hEq2 | hlt2
        · rw [← hEq2]
          exact hasDerivAt_u_t_at_τ D ε hj1 x
        · exact absurd (Set.mem_Ioo.mpr ⟨hlt2, hB⟩ : t ∈ I j) (hI j)
    · exact hasDerivAt_u_t_of_notMem_Icc D ε hIcc x

/-! ## Boundary and initial values -/

theorem u_zero_left (ε t : ℝ) : u D ε t 0 = 0 := by
  have hv : v D ε t 0 = 0 := by
    rw [v]
    exact finsum_eq_zero_of_forall_eq_zero fun j => by simp [vblock, p_zero]
  simp [u, hv, φ_zero]

theorem u_zero_right (ε t : ℝ) : u D ε t π = 0 := by
  have hv : v D ε t π = 0 := by
    rw [v]
    exact finsum_eq_zero_of_forall_eq_zero fun j => by simp [vblock, p_pi]
  simp [u, hv, φ_pi]

theorem u_initial (ε x : ℝ) : u D ε 0 x = 0 := by
  have hv : v D ε 0 x = 0 := v_eq_zero_of_ηj D ε (fun i => ηj_at_zero D i) x
  simp [u, hv, ρ_zero]

theorem ux_zero_left (ε t : ℝ) : ux D ε t 0 = 0 := by
  have hv : vx D ε t 0 = 0 := by
    rw [vx]
    exact finsum_eq_zero_of_forall_eq_zero fun j => by simp [vxblock, p'_zero]
  simp [ux, hv, φ'_zero]

theorem ux_zero_right (ε t : ℝ) : ux D ε t π = 0 := by
  have hv : vx D ε t π = 0 := by
    rw [vx]
    exact finsum_eq_zero_of_forall_eq_zero fun j => by simp [vxblock, p'_pi]
  simp [ux, hv, φ'_pi]

/-! ## Formula (4.6) on the middle third -/

theorem ut_on_J (ε : ℝ) {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ J j) (x : ℝ) :
    ut D ε t x
      = ∑ m ∈ Finset.Icc 1 (M j), (-(ε / 2) * (cos (θ j m t) + sin (θ j m t))) * p (K j m) x := by
  have htI : t ∈ I j := J_subset_I hj ht
  rw [ut, ρ'_eq_zero_of_mem_I D htI, zero_mul, zero_add, vt_eq_block D ε htI x, vtblock]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hKpos : (0 : ℝ) < (K j m : ℝ) := by exact_mod_cast K_pos hj
  have hk2 : ((K j m : ℝ)) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hKpos)
  rw [y', ηj'_eq_zero_of_mem_J D hj ht, ηj_eq_one_of_mem_J D hj ht]
  field_simp
  try ring

end LionsC12

end
