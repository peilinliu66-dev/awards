import Erdos524.AffineLowerMeshMoments
import Erdos524.RegressionWeightBounds

/-! Only the left boundary band can lose aggregate potential relative to the deficit. -/

namespace Erdos524.QuantileCounting

open Set MeasureTheory Filter
open scoped BigOperators
open Erdos524.RegressionWeightBounds

 theorem lower_left_node_count {L : ℝ} (hL : 2 ≤ L) (mesh : LowerMesh L) :
    ((Finset.univ.filter (fun i ↦ mesh.node i < 0)).card : ℝ) ≤
      lowerMaxDensity L * (4 * Real.log L) + 1 := by
  classical
  obtain ⟨hab, hB, hr⟩ := lower_parameters_valid hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hz : (0 : ℝ) ∈ Icc (lowerLeft L) (lowerRight L) := by
    unfold lowerLeft lowerRight
    constructor <;> linarith
  have hc := (abs_le.mp (affine_quantile_discrepancy hab.le hB hr mesh hz)).2
  have hs := (affineCDF_slope_bounds (A := lowerIntercept L) hB (left_mem_Icc.mpr hab.le) hz hz.1).2
  rw [affineCDF_left, sub_zero] at hs
  have hs' : affineCDF (lowerLeft L) (lowerIntercept L) lowerSlope 0 ≤
      lowerMaxDensity L * (4 * Real.log L) := by
    simpa only [lowerMaxDensity, lowerLeft, zero_sub, neg_mul, neg_neg] using hs
  have hcard : ((Finset.univ.filter (fun i ↦ mesh.node i < 0)).card : ℝ) ≤
      ((Finset.univ.filter (fun i ↦ mesh.node i ≤ 0)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (show Finset.univ.filter (fun i ↦ mesh.node i < 0) ⊆
      Finset.univ.filter (fun i ↦ mesh.node i ≤ 0) from by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.le⟩)
  calc
    _ ≤ ((Finset.univ.filter (fun i ↦ mesh.node i ≤ 0)).card : ℝ) := hcard
    _ ≤ affineCDF (lowerLeft L) (lowerIntercept L) lowerSlope 0 + 1 := by
      convert (sub_le_iff_le_add.mp hc) using 1 <;> simp [lowerTotal, add_comm]
      congr 1
    _ ≤ _ := add_le_add hs' le_rfl

theorem lower_aggregate_potential_deficit {L : ℝ} (hL : 2 ≤ L) (mesh : LowerMesh L)
    (hcore : ∀ i, 0 ≤ mesh.node i → mesh.node i ≤ 2 * L + 4 * Real.log L →
      L - mesh.node i / 2 ≤ omittedPotential mesh.node i (mesh.node i)) :
    (∑ i, (L - mesh.node i / 2)) -
      (lowerMaxDensity L * (4 * Real.log L) + 1) * (L + 2 * Real.log L) ≤
        ∑ i, omittedPotential mesh.node i (mesh.node i) := by
  classical
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hC : 0 ≤ L + 2 * Real.log L := by linarith
  have hpoint (i) : (L - mesh.node i / 2) - omittedPotential mesh.node i (mesh.node i) ≤
      if mesh.node i < 0 then L + 2 * Real.log L else 0 := by
    have hU := omittedPotential_nonneg mesh.node i (mesh.node i)
    split_ifs with hi
    · have hn := (mesh.node_mem i).1
      unfold lowerLeft at hn
      linarith
    · have hi0 : 0 ≤ mesh.node i := le_of_not_gt hi
      by_cases hic : mesh.node i ≤ 2 * L + 4 * Real.log L
      · linarith [hcore i hi0 hic]
      · have htail : 2 * L + 4 * Real.log L < mesh.node i := lt_of_not_ge hic
        linarith
  have hsum : (∑ i, (L - mesh.node i / 2)) -
      (∑ i, omittedPotential mesh.node i (mesh.node i)) ≤
      ((Finset.univ.filter (fun i ↦ mesh.node i < 0)).card : ℝ) * (L + 2 * Real.log L) := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, if mesh.node i < 0 then L + 2 * Real.log L else 0 :=
        Finset.sum_le_sum (fun i _ ↦ hpoint i)
      _ = _ := by rw [← Finset.sum_filter]; simp; ring
  have hcount := mul_le_mul_of_nonneg_right (lower_left_node_count hL mesh) hC
  linarith

theorem lower_aggregate_remainder {L : ℝ} (hL : 2 ≤ L) (mesh : LowerMesh L)
    (hM : lowerMaxDensity L ≤ L)
    (hcore : ∀ i, 0 ≤ mesh.node i → mesh.node i ≤ 2 * L + 4 * Real.log L →
      L - mesh.node i / 2 ≤ omittedPotential mesh.node i (mesh.node i)) :
    (∑ i, (L - mesh.node i / 2)) - 15 * L ^ 2 * (Real.log L + 1) ≤
      ∑ i, omittedPotential mesh.node i (mesh.node i) := by
  have h := lower_aggregate_potential_deficit hL mesh hcore
  have hL0 : 0 ≤ L := by linarith
  have hr0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hrL := Real.log_le_self hL0
  have hMmul := mul_le_mul_of_nonneg_right hM (by positivity : 0 ≤ 4 * Real.log L)
  have hcost : (lowerMaxDensity L * (4 * Real.log L) + 1) * (L + 2 * Real.log L) ≤
      (4 * L * Real.log L + 1) * (3 * L) := by
    apply mul_le_mul
    · linarith
    · linarith
    · positivity
    · positivity
  have hpos : 0 ≤ L ^ 2 * Real.log L := by positivity
  nlinarith

theorem eventually_lower_aggregate_deficit {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ mesh : LowerMesh L,
      (∀ i, 0 ≤ mesh.node i → mesh.node i ≤ 2 * L + 4 * Real.log L →
        L - mesh.node i / 2 ≤ omittedPotential mesh.node i (mesh.node i)) →
      (∑ i, (L - mesh.node i / 2)) - ε * L ^ 3 ≤
        ∑ i, omittedPotential mesh.node i (mesh.node i) := by
  filter_upwards [Erdos524.CauchyKernel.eventually_log_remainder_le
    (by norm_num : (0 : ℝ) < 15) heps, eventually_lower_size_controls,
    eventually_ge_atTop (2 : ℝ)] with L herr hsize hL
  intro mesh hcore
  have h := lower_aggregate_remainder hL mesh hsize.2.1 hcore
  linarith

end Erdos524.QuantileCounting
