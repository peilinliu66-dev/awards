import Erdos524.LogCauchyDeterminant

namespace Erdos524.CauchyKernel
open scoped BigOperators

noncomputable def blockPoint (center r : ℝ) {m : ℕ} (i : Fin m) : ℝ :=
  center + ((i : ℝ) - ((m : ℝ)-1)/2)/r

theorem blockPoint_strictMono (center : ℝ) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    StrictMono (blockPoint center r (m := m)) := by
  intro i j hij
  have hcast : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
  unfold blockPoint
  linarith [(div_lt_div_iff_of_pos_right hr).mpr (sub_lt_sub_right hcast (((m:ℝ)-1)/2))]

theorem blockPoint_within {m : ℕ} (center : ℝ) {r width : ℝ}
    (hr : 0 < r) (hm : (m : ℝ) ≤ r*width) (i : Fin m) :
    |blockPoint center r i-center| ≤ width/2 := by
  have hlo : (0 : ℝ) ≤ (i : ℝ) := by positivity
  have hhi : (i : ℝ)+1 ≤ m := by exact_mod_cast i.isLt
  unfold blockPoint
  rw [add_sub_cancel_left, abs_le]
  constructor
  · apply (le_div_iff₀ hr).mpr
    nlinarith
  · apply (div_le_iff₀ hr).mpr
    nlinarith

theorem blockPoint_gap {m : ℕ} (center : ℝ) (r : ℝ) (i j : Fin m) :
    blockPoint center r j - blockPoint center r i = ((j:ℝ)-(i:ℝ))/r := by
  unfold blockPoint
  ring


theorem sum_range_natCast_twice (m : ℕ) :
    2 * (∑ i ∈ Finset.range m, (i : ℝ)) = (m : ℝ)*((m : ℝ)-1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith

theorem sum_blockPoint (center r : ℝ) (m : ℕ) :
    (∑ i : Fin m, blockPoint center r i) = (m : ℝ)*center := by
  have hsum : (∑ i : Fin m, (i : ℝ)) = (m : ℝ)*((m : ℝ)-1)/2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℝ)) m]
    have h := sum_range_natCast_twice m
    linarith
  unfold blockPoint
  rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib, hsum]
  simp
  left
  ring

theorem sum_block_deficit (center r L : ℝ) (m : ℕ) :
    (∑ i : Fin m, (L-blockPoint center r i/2)) = (m : ℝ)*(L-center/2) := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, sum_blockPoint]
  simp
  ring

theorem blockPoint_log_det_lower {m : ℕ} (center : ℝ) {r : ℝ} (hr : 0 < r) :
    -(m : ℝ)*Real.log 2 - (m : ℝ)*r*(Real.pi^2/2) ≤
      Real.log (normalized (fun i : Fin m => Real.exp (blockPoint center r i))).det := by
  have he : blockPoint center r (m := m) =
      (fun i : Fin m => (center-((m:ℝ)-1)/(2*r))+(i:ℝ)/r) := by
    funext i
    unfold blockPoint
    ring
  rw [he]
  exact log_det_affine_mesh_lower _ hr

noncomputable def blockCount (r width : ℝ) : ℕ := ⌊r*width⌋₊

theorem blockCount_le {r width : ℝ} (hr : 0 ≤ r) (hw : 0 ≤ width) :
    (blockCount r width : ℝ) ≤ r*width := Nat.floor_le (mul_nonneg hr hw)

theorem blockCount_lower (r width : ℝ) :
    r*width-1 < (blockCount r width : ℝ) := by
  have h := Nat.lt_floor_add_one (r*width)
  unfold blockCount
  linarith

end Erdos524.CauchyKernel
