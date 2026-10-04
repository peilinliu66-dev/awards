import Erdos524.UpperMeshCutoff
import Erdos524.InverseCovarianceOrder
import Erdos524.GaussianCovarianceBox

/-! An under-dense logarithmic mesh with a uniformly small sample-cube Gaussian energy. -/

namespace Erdos524.DilationMesh

open Matrix Filter
open scoped BigOperators
open Erdos524.CauchyKernel Erdos524.FiniteKernelPerturbation
open Erdos524.InverseCovarianceOrder Erdos524.GaussianCovarianceBox Erdos524.GaussianBoxDensity

noncomputable def density (L : ℝ) : ℝ := L / (2 * Real.pi ^ 2)
noncomputable def count (L : ℝ) : ℕ := ⌊(L - 4 * Real.log L) * density L⌋₊
noncomputable def node (L : ℝ) (i : ℕ) : ℝ := 4 * Real.log L + ((i : ℝ) + 1 / 2) / density L

theorem density_pos {L : ℝ} (hL : 0 < L) : 0 < density L := by unfold density; positivity

theorem count_bounds {L : ℝ} (hL : 16 ≤ L) (hlog : 4 * Real.log L ≤ L / 4) :
    L ^ 2 / (4 * Real.pi ^ 2) ≤ (count L : ℝ) ∧ (count L : ℝ) ≤ L ^ 2 ∧ 0 < count L := by
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hLp : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have htotal : 0 ≤ (L - 4 * Real.log L) * density L := mul_nonneg (by linarith) (density_pos hLp).le
  have hfloor := Nat.floor_le htotal
  have hfloor' := Nat.lt_floor_add_one ((L - 4 * Real.log L) * density L)
  change (count L : ℝ) ≤ _ at hfloor
  change _ < (count L : ℝ) + 1 at hfloor'
  have hlowtotal : L ^ 2 / (4 * Real.pi ^ 2) + 1 ≤ (L - 4 * Real.log L) * density L := by
    unfold density
    field_simp
    have hm := mul_nonneg (by linarith : 0 ≤ L - 16 * Real.log L) hLp.le
    nlinarith [Real.pi_lt_four, Real.pi_pos, sq_nonneg (L - 16)]
  have hlower : L ^ 2 / (4 * Real.pi ^ 2) ≤ (count L : ℝ) := by linarith
  have hupper : (count L : ℝ) ≤ L ^ 2 := by
    apply hfloor.trans
    unfold density
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 2 * Real.pi ^ 2)]
    have hm := mul_nonneg hLp.le hlog0
    have hp1 : 1 ≤ 2 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have h := mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hp1)
    nlinarith
  refine ⟨hlower, hupper, ?_⟩
  have hc : (0 : ℝ) < count L := lt_of_lt_of_le (by positivity) hlower
  exact_mod_cast hc

theorem node_bounds {L : ℝ} (hL : 0 < L) {i : ℕ} (hi : i < count L) :
    4 * Real.log L ≤ node L i ∧ node L i ≤ L := by
  have hr := density_pos hL
  have hwidth : 0 ≤ L - 4 * Real.log L := by
    by_contra hh
    have hneg : (L - 4 * Real.log L) * density L < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hh) hr
    have hzero : count L = 0 := Nat.floor_of_nonpos hneg.le
    omega
  have hfloor := Nat.floor_le (mul_nonneg hwidth hr.le)
  have hi' : (i : ℝ) + 1 ≤ count L := by exact_mod_cast hi
  constructor
  · unfold node
    exact le_add_of_nonneg_right (by positivity)
  · unfold node
    have h : ((i : ℝ) + 1 / 2) / density L ≤ L - 4 * Real.log L := by
      apply (div_le_iff₀ hr).mpr
      change (count L : ℝ) ≤ _ at hfloor
      linarith
    linarith

theorem node_separation {L : ℝ} (hL : 0 < L) {n : ℕ} :
    ∀ i j : Fin (n + 1), i < j → ((j : ℝ) - (i : ℝ)) / density L ≤ node L j - node L i := by
  intro i j hij
  unfold node
  ring_nf
  exact le_rfl

theorem sample_half_gap {L : ℝ} (hL : 16 ≤ L) (hlog : 4 * Real.log L ≤ L / 4)
    {n : ℕ} (hn : count L = n + 1) :
    (normalizedFiniteKernel (fun i : Fin (n + 1) ↦ Real.exp (node L i)) -
      (1 / 2 : ℝ) • normalized (fun i : Fin (n + 1) ↦ Real.exp (node L i))).PosSemidef := by
  have hLp : 0 < L := by linarith
  have hN := (count_bounds hL hlog).2.1
  rw [hn] at hN
  apply separated_normalizedFiniteKernel_half_gap _ (density_pos hLp) (node_separation hLp) (L ^ 4)
  · intro i
    have hb := (node_bounds hLp (by simpa only [hn] using i.isLt)).1
    have he : Real.exp (4 * Real.log L) = L ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hLp]
    rw [← he]
    exact Real.exp_le_exp.mpr hb
  · have hcut := cutoff_scalar_bound (by linarith : 2 ≤ L) (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ)) (by simpa using hN)
    apply le_trans _ hcut
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    unfold density
    have he : L / (2 * Real.pi ^ 2) * Real.pi ^ 2 = L / 2 := by field_simp
    rw [he]
    linarith

theorem sample_posDef {L : ℝ} (hL : 16 ≤ L) (hlog : 4 * Real.log L ≤ L / 4)
    {n : ℕ} (hn : count L = n + 1) :
    (normalizedFiniteKernel (fun i : Fin (n + 1) ↦ Real.exp (node L i))).PosDef := by
  have hLp : 0 < L := by linarith
  have hC := posDef_normalized_fin (fun i : Fin (n + 1) ↦ Real.exp (node L i))
    (fun _ ↦ Real.exp_pos _) (Real.exp_injective.comp
      (separated_grid_strictMono _ (density_pos hLp) (node_separation hLp)).injective)
  exact (half_gap_inverse hC (sample_half_gap hL hlog hn)).1

theorem sample_inverse_diagonal {L : ℝ} (hL : 16 ≤ L) (hlog : 4 * Real.log L ≤ L / 4)
    {n : ℕ} (hn : count L = n + 1) (i : Fin (n + 1)) :
    (normalizedFiniteKernel (fun j : Fin (n + 1) ↦ Real.exp (node L j)))⁻¹ i i ≤ 4 * Real.exp (L / 2) := by
  have hLp : 0 < L := by linarith
  have hC := posDef_normalized_fin (fun i : Fin (n + 1) ↦ Real.exp (node L i))
    (fun _ ↦ Real.exp_pos _) (Real.exp_injective.comp
      (separated_grid_strictMono _ (density_pos hLp) (node_separation hLp)).injective)
  have h := half_gap_inverse_diagonal hC (sample_half_gap hL hlog hn) i
  have hc := separated_inverse_diagonal_le (fun i : Fin (n + 1) ↦ node L i)
    (density_pos hLp) (node_separation hLp) i
  have he : density L * Real.pi ^ 2 = L / 2 := by unfold density; field_simp
  rw [he] at hc
  linarith

theorem sample_box_energy {L : ℝ} (hL : 16 ≤ L) (hlog : 4 * Real.log L ≤ L / 4)
    {n : ℕ} (hn : count L = n + 1)
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ box (fun i ↦ Real.sqrt (Real.exp (node L i)) * Real.exp (-L))) :
    x ⬝ᵥ (normalizedFiniteKernel (fun i : Fin (n + 1) ↦ Real.exp (node L i)))⁻¹ *ᵥ x ≤
      4 * (n + 1 : ℝ) ^ 2 * Real.exp (-L / 2) := by
  have hLp : 0 < L := by linarith
  have hA := sample_posDef hL hlog hn
  have h := quadratic_le_box_diagonal_budget hA.posSemidef.inv _ hx
  apply h.trans
  have hterm (i : Fin (n + 1)) :
      (Real.sqrt (Real.exp (node L i)) * Real.exp (-L)) ^ 2 *
          (normalizedFiniteKernel (fun j : Fin (n + 1) ↦ Real.exp (node L j)))⁻¹ i i ≤
        4 * Real.exp (-L / 2) := by
    have hnode := (node_bounds hLp (by simpa only [hn] using i.isLt)).2
    have hw : (Real.sqrt (Real.exp (node L i)) * Real.exp (-L)) ^ 2 ≤ Real.exp (-L) := by
      rw [mul_pow, Real.sq_sqrt (Real.exp_pos _).le, ← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      norm_num
      linarith
    have hi := sample_inverse_diagonal hL hlog hn i
    calc
      _ ≤ Real.exp (-L) * (4 * Real.exp (L / 2)) :=
        mul_le_mul hw hi hA.posSemidef.inv.diag_nonneg (Real.exp_pos _).le
      _ = _ := by
        rw [show Real.exp (-L) * (4 * Real.exp (L / 2)) = 4 * (Real.exp (-L) * Real.exp (L / 2)) by ring,
          ← Real.exp_add]
        congr 2
        ring
  calc
    _ ≤ (n + 1 : ℝ) * ∑ _i : Fin (n + 1), 4 * Real.exp (-L / 2) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hterm i)) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring

theorem energy_budget_small {L N : ℝ} (hL : 100 ≤ L) (hN : 0 ≤ N) (hNmax : N ≤ L ^ 2) :
    4 * N ^ 2 * Real.exp (-L / 2) ≤ N / 6 := by
  have hLp : 0 < L := by linarith
  have he := Real.pow_div_factorial_le_exp (L / 2) (show 0 ≤ L / 2 by positivity) 4
  norm_num at he
  have hLsq : 9216 ≤ L ^ 2 := by nlinarith
  have hm := mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hLsq)
  have he24 : 24 * N ≤ Real.exp (L / 2) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left he24 hN
  rw [show -L / 2 = -(L / 2) by ring, Real.exp_neg]
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  nlinarith

theorem eventually_dilation_mesh :
    ∀ᶠ L : ℝ in atTop, 100 ≤ L ∧ 4 * Real.log L ≤ L / 4 ∧
      L ^ 2 / (4 * Real.pi ^ 2) ≤ (count L : ℝ) ∧ (count L : ℝ) ≤ L ^ 2 ∧ 0 < count L := by
  have hlog := Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 16)
  filter_upwards [hlog, eventually_ge_atTop (100 : ℝ)] with L hlog hL
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  rw [id_eq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0,
    abs_of_nonneg (by linarith : 0 ≤ L)] at hlog
  have hsmall : 4 * Real.log L ≤ L / 4 := by linarith
  exact ⟨hL, hsmall, count_bounds (by linarith) hsmall⟩

end Erdos524.DilationMesh
