import Erdos524.ProductCoordinateReplacement
import Erdos524.SmoothedSoftMaximum

namespace Erdos524.LinearStatistic
open MeasureTheory
open Erdos524.ProductCoordinateReplacement Erdos524.SoftMaximum Erdos524.SmoothCutoff

noncomputable def linearStatistic {N d : ℕ} (c : Fin N → Fin d → ℝ) (z : Fin N → ℝ) (l : Fin d) : ℝ :=
  ∑ i, z i*c i l

noncomputable def smoothStatistic {N d : ℕ} (b η r : ℝ) (c : Fin N → Fin d → ℝ) (z : Fin N → ℝ) : ℝ :=
  cutoff ((softMax (b/η) (linearStatistic c z)-r)/η)

theorem linearStatistic_continuous {N d : ℕ} (c : Fin N → Fin d → ℝ) : Continuous (linearStatistic c) := by
  unfold linearStatistic
  fun_prop

theorem smoothStatistic_continuous {N d : ℕ} (hd : 0<d) (b η r : ℝ) (c : Fin N → Fin d → ℝ) :
    Continuous (smoothStatistic b η r c) := by
  have hp : Continuous (fun z : Fin N → ℝ => partition (b/η) (linearStatistic c z)) := by
    unfold partition linearStatistic
    fun_prop
  unfold smoothStatistic softMax
  exact cutoff_contDiff 0 |>.continuous |>.comp
    ((((hp.log (fun z => ne_of_gt (partition_pos hd (b/η) _))).div_const (b/η)).sub continuous_const).div_const η)

theorem smoothStatistic_norm_le_one {N d : ℕ} (b η r : ℝ) (c : Fin N → Fin d → ℝ) (z : Fin N → ℝ) :
    ‖smoothStatistic b η r c z‖≤1 := by
  unfold smoothStatistic
  rw [Real.norm_eq_abs,abs_of_nonneg (cutoff_mem_Icc _).1]
  exact (cutoff_mem_Icc _).2

theorem linearStatistic_insert {n d : ℕ} (c : Fin (n+1) → Fin d → ℝ)
    (i : Fin (n+1)) (t : ℝ) (y : Fin n → ℝ) :
    linearStatistic c (insertCoordinate i t y)=fun l => linearStatistic (fun j => c (i.succAbove j)) y l+t*c i l := by
  funext l
  unfold linearStatistic
  rw [Fin.sum_univ_succAbove _ i]
  simp [insertCoordinate,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,add_comm]

end Erdos524.LinearStatistic
