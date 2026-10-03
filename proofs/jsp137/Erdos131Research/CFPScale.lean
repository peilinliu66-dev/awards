/-
Copyright (c) 2026. Released under Apache 2.0.
Original conversion of the proved canonical CFP integer scale to the
natural-log scale in the projective paper. Compiled and audited; see BUILD_REPORT.json.
-/
import ErdosProblems.Erdos186.CFP.IntegerHigherDimensionalFinal
import ErdosProblems.Erdos186.PZ.Reduction.CanonicalScale

open Filter
open scoped Topology

namespace Erdos131Research
noncomputable section
open Erdos186.PZ.Reduction

def structureScale (m : ℕ) : ℝ := (m : ℝ) / (Real.log (m : ℝ)) ^ 2

def scaleRatio {β η : ℝ} (C : HigherDimensionalContext β η) (d : ℕ) : ℝ :=
  (Real.log 2) ^ 2 / (2 * (C.scaleDen d : ℝ))

def lossRatio {β η : ℝ} (C : HigherDimensionalContext β η) (d : ℕ) : ℝ :=
  (C.lossConstant d : ℝ) / Real.log 2 + 1

theorem scaleRatio_pos {β η : ℝ} (C : HigherDimensionalContext β η) (d : ℕ) :
    0 < scaleRatio C d := by
  unfold scaleRatio
  exact div_pos (sq_pos_of_pos (Real.log_pos (by norm_num)))
    (mul_pos (by norm_num) (by exact_mod_cast C.scaleDen_pos d))

theorem lossRatio_pos {β η : ℝ} (C : HigherDimensionalContext β η) (d : ℕ) :
    0 < lossRatio C d := by
  dsimp [lossRatio]
  positivity

theorem eventually_canonicalScale_comparison {β η : ℝ}
    (C : HigherDimensionalContext β η) (d : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      (canonicalScale C d m : ℝ) ≤ structureScale m ∧
      scaleRatio C d * structureScale m ≤ (canonicalScale C d m : ℝ) ∧
      (C.lossConstant d : ℝ) * canonicalScale C d m * Real.logb 2 (m : ℝ) + 1 ≤
        lossRatio C d * (m : ℝ) / Real.log (m : ℝ) := by
  have htwo := eventually_const_mul_logb_sq_le_nat_rpow
    (R := 2 * (C.scaleDen d : ℝ)) (q := 1) (by norm_num)
  filter_upwards [htwo, eventually_ge_atTop (2 : ℕ)] with m hm hm2
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hden : 0 < (C.scaleDen d : ℝ) := by exact_mod_cast C.scaleDen_pos d
  have hden1 : (1 : ℝ) ≤ C.scaleDen d := by exact_mod_cast C.scaleDen_pos d
  have hlogb : 0 < Real.logb 2 (m : ℝ) := div_pos hlog hl2
  have hS : 0 ≤ structureScale m := by unfold structureScale; positivity
  have heq : canonicalScaleReal C d m =
      ((Real.log 2) ^ 2 / (C.scaleDen d : ℝ)) * structureScale m := by
    unfold canonicalScaleReal structureScale
    rw [Real.logb]
    field_simp <;> ring
  have hreal2 : 2 ≤ canonicalScaleReal C d m := by
    rw [canonicalScaleReal, le_div_iff₀ (mul_pos hden (sq_pos_of_pos hlogb))]
    simpa [Real.rpow_one, mul_assoc] using hm
  have hfloor : (canonicalScale C d m : ℝ) ≤ canonicalScaleReal C d m :=
    Nat.floor_le (by linarith)
  have hhalf : canonicalScaleReal C d m / 2 ≤ (canonicalScale C d m : ℝ) := by
    have h := Nat.sub_one_lt_floor (canonicalScaleReal C d m)
    change canonicalScaleReal C d m - 1 < (canonicalScale C d m : ℝ) at h
    linarith
  have hratio : (Real.log 2) ^ 2 / (C.scaleDen d : ℝ) ≤ 1 := by
    apply (div_le_one hden).mpr
    nlinarith
  have hupper : (canonicalScale C d m : ℝ) ≤ structureScale m := by
    apply hfloor.trans
    rw [heq]
    exact mul_le_of_le_one_left hS hratio
  refine ⟨hupper, ?_, ?_⟩
  · have hhalfEq : canonicalScaleReal C d m / 2 = scaleRatio C d * structureScale m := by
      rw [heq]
      unfold scaleRatio
      field_simp <;> ring
    rwa [hhalfEq] at hhalf
  · have hlogm : Real.log (m : ℝ) ≤ (m : ℝ) :=
      (Real.log_le_sub_one_of_pos hmpos).trans (by linarith)
    have hone : 1 ≤ (m : ℝ) / Real.log (m : ℝ) :=
      (le_div_iff₀ hlog).mpr (by simpa using hlogm)
    have hb : (C.lossConstant d : ℝ) * canonicalScale C d m * Real.logb 2 (m : ℝ) ≤
        (C.lossConstant d : ℝ) / Real.log 2 * ((m : ℝ) / Real.log (m : ℝ)) := by
      calc
        _ ≤ (C.lossConstant d : ℝ) * structureScale m * Real.logb 2 (m : ℝ) := by gcongr
        _ = _ := by unfold structureScale; rw [Real.logb]; field_simp <;> ring
    calc
      _ ≤ (C.lossConstant d : ℝ) / Real.log 2 * ((m : ℝ) / Real.log (m : ℝ)) +
          ((m : ℝ) / Real.log (m : ℝ)) := add_le_add hb hone
      _ = _ := by unfold lossRatio; ring

end
end Erdos131Research
