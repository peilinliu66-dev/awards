import Erdos776.Uniform.FiniteProfileChecker
import Erdos776.Uniform.GlobalThreshold

/-!
# Exact finite threshold for `4 ≤ r ≤ 10`

For each of the seven values, one closed Boolean certificate verifies:

* level-two overflow of the full recurrence at `n = 2r+4`;
* feasibility of the full recurrence at `n = 2r+5`;
* feasibility of the canonical core recurrence on `r+5` points.

The generic profile sufficiency theorem realizes the first successful full
profile.  The checked core carries the already formalized explicit free sets,
so persistent padding and `coreToFull` construct every later profile.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- All three finite recurrence checks for the seven small uniform values. -/
def smallThresholdFiniteCheck : Bool :=
  (List.range 7).all fun d =>
    let r := 4 + d
    (constantProfileLevelTwoOverflowCheck (2 * r + 4) r &&
      constantProfileCheck (2 * r + 5) r 2 (2 * r + 3)) &&
      constantProfileCheck (r + 5) r 2 (r + 2)

theorem smallThresholdFiniteCheck_verified :
    smallThresholdFiniteCheck = true := by
  set_option maxRecDepth 100000 in
    decide +kernel

theorem smallThresholdChecks_eq_true_of_ge_4_le_10
    {r : ℕ} (hr4 : 4 ≤ r) (hr10 : r ≤ 10) :
    constantProfileLevelTwoOverflowCheck (2 * r + 4) r = true ∧
      constantProfileCheck (2 * r + 5) r 2 (2 * r + 3) = true ∧
      constantProfileCheck (r + 5) r 2 (r + 2) = true := by
  have hall : ∀ d ∈ List.range 7,
      ((constantProfileLevelTwoOverflowCheck (2 * (4 + d) + 4) (4 + d) &&
        constantProfileCheck (2 * (4 + d) + 5) (4 + d) 2
          (2 * (4 + d) + 3)) &&
        constantProfileCheck ((4 + d) + 5) (4 + d) 2 ((4 + d) + 2)) = true := by
    simpa [smallThresholdFiniteCheck] using
      (List.all_eq_true.mp smallThresholdFiniteCheck_verified)
  let d := r - 4
  have hd : d ∈ List.range 7 := by
    simp [d]
    omega
  have h := hall d hd
  have hparts :
      (constantProfileLevelTwoOverflowCheck (2 * (4 + d) + 4) (4 + d) = true ∧
      constantProfileCheck (2 * (4 + d) + 5) (4 + d) 2
        (2 * (4 + d) + 3) = true) ∧
      constantProfileCheck ((4 + d) + 5) (4 + d) 2 ((4 + d) + 2) = true := by
    simpa only [Bool.and_eq_true] using h
  have hparts' :
      constantProfileLevelTwoOverflowCheck (2 * (4 + d) + 4) (4 + d) = true ∧
      constantProfileCheck (2 * (4 + d) + 5) (4 + d) 2
        (2 * (4 + d) + 3) = true ∧
      constantProfileCheck ((4 + d) + 5) (4 + d) 2 ((4 + d) + 2) = true := by
    exact ⟨hparts.1.1, hparts.1.2, hparts.2⟩
  simpa only [d, show 4 + (r - 4) = r by omega] using hparts'

/-- The bad full profile at `2r+4` is semantically impossible. -/
theorem not_fullMiddleProfileExists_of_ge_4_le_10
    (r : ℕ) (hr4 : 4 ≤ r) (hr10 : r ≤ 10) :
    ¬ FullMiddleProfileExists (2 * r + 4) r := by
  exact constantProfileLevelTwoOverflowCheck_sound (by omega)
    (smallThresholdChecks_eq_true_of_ge_4_le_10 hr4 hr10).1

/-- The first successful full profile at `2r+5` is realized by colex. -/
theorem fullMiddleProfileExists_next_of_ge_4_le_10
    (r : ℕ) (hr4 : 4 ≤ r) (hr10 : r ≤ 10) :
    FullMiddleProfileExists (2 * r + 5) r := by
  apply fullMiddleProfileExists_of_constantProfileCheck (by omega)
  simpa only [show 2 * r + 5 - 2 = 2 * r + 3 by omega] using
    (smallThresholdChecks_eq_true_of_ge_4_le_10 hr4 hr10).2.1

/-- The checked canonical core carries the explicit free family. -/
theorem hasSuitableFreeCore_of_ge_4_le_10
    (r : ℕ) (hr4 : 4 ≤ r) (hr10 : r ≤ 10) :
    HasSuitableFreeCore r := by
  have hcheck := (smallThresholdChecks_eq_true_of_ge_4_le_10 hr4 hr10).2.2
  have hrec := constantProfileCheck_sound
    (n := r + 5) (load := r) (lo := 2) (hi := r + 2)
    (by omega) hcheck
  apply hasSuitableFreeCore_of_recurrence r
  simpa only [upperCoreChain] using hrec

/-- The full-profile threshold occurs at `2r+4` for every `4 ≤ r ≤ 10`. -/
theorem fullMiddleProfileThresholdAt_of_ge_4_le_10
    (r : ℕ) (hr4 : 4 ≤ r) (hr10 : r ≤ 10) :
    FullMiddleProfileThresholdAt r (2 * r + 4) := by
  refine ⟨not_fullMiddleProfileExists_of_ge_4_le_10 r hr4 hr10, ?_⟩
  intro n hn
  by_cases hnext : n = 2 * r + 5
  · subst n
    exact fullMiddleProfileExists_next_of_ge_4_le_10 r hr4 hr10
  · exact fullMiddleProfileExists_of_suitableFreeCore
      (hasSuitableFreeCore_of_ge_4_le_10 r hr4 hr10) (by omega)

/-- The least global Erdős threshold for the complete small uniform range. -/
theorem isErdosThreshold_of_ge_4_le_10
    (r : ℕ) (hr4 : 4 ≤ r) (hr10 : r ≤ 10) :
    IsErdosThreshold r (2 * r + 4) := by
  exact isErdosThreshold_of_fullMiddleProfileThresholdAt hr4 (by omega)
    (fullMiddleProfileThresholdAt_of_ge_4_le_10 r hr4 hr10)

end Erdos776.Uniform

#print axioms Erdos776.Uniform.smallThresholdFiniteCheck_verified
#print axioms Erdos776.Uniform.isErdosThreshold_of_ge_4_le_10
