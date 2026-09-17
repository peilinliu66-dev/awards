import Mathlib
import JSP636UpperBound
import Erdos776.Uniform.ProblemDefinitions
import Erdos776.Uniform.FiniteProfileChecker

/-!
# The missing small-parameter branches for Erdős 776

Mathematical values `n₀(2)=3`, `n₀(3)=8`: Yixin He and Quanyu Tang,
arXiv:2602.09803v2, Appendix A.  The large-ground-set witnesses in this
extension use Thiim's proved `r=4` construction, without altering it.

All new finite certificates are ordinary Lean-kernel `decide` proofs.
The upstream core is supplied and ported separately; no upstream source is
changed here.  Upstream copyright (c) 2026 mthiim and contributors, MIT;
see LICENSE-JSP636-MIT.txt.  New proof bodies prepared with OpenAI ChatGPT.
Target: Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
See verification/ for actual local build and terminal axiom reports.
-/

namespace JSP636

open Finset
open Erdos776.Antichain Erdos776.Uniform Erdos776.KruskalKatona

/-- The public problem predicate is monotone in its multiplicity parameter. -/
theorem problemAdmissible_mono {n r s : ℕ} {F : Family (Fin n)}
    (hrs : r ≤ s) (hF : ProblemAdmissible F s) :
    ProblemAdmissible F r :=
  ⟨hF.1, fun t ht => hrs.trans (hF.2 t ht)⟩

theorem problemTargetExists_mono {n r s : ℕ}
    (hrs : r ≤ s) (h : ProblemTargetExists n s) :
    ProblemTargetExists n r := by
  obtain ⟨F, hF, hcard⟩ := h
  exact ⟨F, problemAdmissible_mono hrs hF, hcard⟩

/-- Only the forward conversion from a full middle profile is needed here.
Unlike the upstream iff, this direction is valid for every positive `r`. -/
theorem target_of_fullMiddleProfile
    {n r : ℕ} (hr : 1 ≤ r) (h : FullMiddleProfileExists n r) :
    ProblemTargetExists n r := by
  obtain ⟨F, hanti, hlevels⟩ := h
  have hM : IsMultiplicityAntichain (middlePart F) r :=
    isMultiplicityAntichain_middlePart hr hanti hlevels
  refine ⟨middlePart F,
    problemAdmissible_iff_isMultiplicityAntichain.mpr hM, ?_⟩
  rw [occupiedLevels_middlePart_eq hr hlevels, Nat.card_Icc]
  omega

/-! ## All the finite success checks: nine plus four cases -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_r2_profile_checks (n : ℕ) (hn4 : 4 ≤ n) (hn12 : n ≤ 12) :
    constantProfileCheck n 2 2 (n - 2) = true := by
  interval_cases n <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_r3_profile_checks (n : ℕ) (hn9 : 9 ≤ n) (hn12 : n ≤ 12) :
    constantProfileCheck n 3 2 (n - 2) = true := by
  interval_cases n <;> decide

/-- Every ground size at least 13 is handled by the already proved `r=4`
construction.  No new asymptotic or padding assumption is introduced. -/
theorem target_of_ge_thirteen_of_le_four
    {n r : ℕ} (hn : 13 ≤ n) (hr : r ≤ 4) :
    ProblemTargetExists n r := by
  apply problemTargetExists_mono hr
  exact (problemLastFailure_of_fullMiddleProfileThresholdAt
    (r := 4) (N := 12) (by omega) (by omega)
    (fullMiddleProfileThresholdAt_of_ge_4_le_10 4 (by omega) (by omega))).2 n (by omega)

/-- All successful ground sizes for `r=2`, not merely the checked finite list. -/
theorem r2_target_everywhere (n : ℕ) (hn : 4 ≤ n) :
    ProblemTargetExists n 2 := by
  by_cases hn12 : n ≤ 12
  · exact target_of_fullMiddleProfile (by omega)
      (fullMiddleProfileExists_of_constantProfileCheck hn
        (small_r2_profile_checks n hn hn12))
  · exact target_of_ge_thirteen_of_le_four (by omega) (by omega)

/-- All successful ground sizes for `r=3`, not merely the checked finite list. -/
theorem r3_target_everywhere (n : ℕ) (hn : 9 ≤ n) :
    ProblemTargetExists n 3 := by
  by_cases hn12 : n ≤ 12
  · exact target_of_fullMiddleProfile (by omega)
      (fullMiddleProfileExists_of_constantProfileCheck (by omega)
        (small_r3_profile_checks n hn hn12))
  · exact target_of_ge_thirteen_of_le_four (by omega) (by omega)

/-! ## The last obstruction for r=3 -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- These are the exact ground-bounded recurrence states, with the final
level-two demand 29 and its actual capacity 28. -/
theorem r3_eight_numeric_certificate :
    checkedConstantProfileState 8 3 6 0 = some 3 ∧
    checkedConstantProfileState 8 3 6 1 = some 18 ∧
    checkedConstantProfileState 8 3 6 2 = some 37 ∧
    checkedConstantProfileState 8 3 6 3 = some 43 ∧
    3 + boundedShadow 8 3 43 = 29 ∧
    fastBinom 8 2 = 28 ∧
    constantProfileLevelTwoOverflowCheck 8 3 = true := by
  decide

/-- The checked overflow is passed to the proved profile necessity theorem. -/
theorem r3_eight_no_full_middle : ¬ FullMiddleProfileExists 8 3 := by
  exact constantProfileLevelTwoOverflowCheck_sound (by omega)
    r3_eight_numeric_certificate.2.2.2.2.2.2

/-- Boundary levels are first excluded by actual antichain arguments.
Only then is the full middle profile forced and the profile contradiction used. -/
theorem r3_eight_upper (F : Family (Fin 8))
    (hF : IsMultiplicityAntichain F 3) :
    (occupiedLevels F).card ≤ 4 := by
  classical
  by_cases hone : 1 ∈ occupiedLevels F
  · have h := card_occupiedLevels_le_pred_of_one
      (by omega) (by omega) hF hone
    norm_num at h
    exact h
  by_cases hpen : 7 ∈ occupiedLevels F
  · have h := card_occupiedLevels_le_pred_of_penultimate
      (by omega) (by omega) hF (by simpa using hpen)
    norm_num at h
    exact h
  have hsub : occupiedLevels F ⊆ Finset.Icc 2 6 := by
    simpa using occupiedLevels_subset_middle_of_boundary_free
      (by omega : 2 ≤ 3) hF hone (by simpa using hpen)
  by_contra hnot
  have hcard : (Finset.Icc 2 6).card ≤ (occupiedLevels F).card := by
    have hIcc : (Finset.Icc (2 : ℕ) 6).card = 5 := by decide
    rw [hIcc]
    omega
  have heq : occupiedLevels F = Finset.Icc 2 6 :=
    Finset.eq_of_subset_of_card_le hsub hcard
  apply r3_eight_no_full_middle
  refine ⟨F, hF.1, ?_⟩
  intro i hi2 hi6
  change 3 ≤ (level F i).card
  apply hF.2 i
  rw [heq]
  exact Finset.mem_Icc.mpr ⟨hi2, by simpa using hi6⟩

/-- No five-level admissible family exists at (n,r)=(8,3). -/
theorem r3_eight_target_fails : ¬ ProblemTargetExists 8 3 := by
  rintro ⟨F, hF, hcard⟩
  have hupper := r3_eight_upper F
    (problemAdmissible_iff_isMultiplicityAntichain.mp hF)
  norm_num at hcard
  omega

/-! ## The last obstruction for r=2 is a maximum-value obstruction -/

/-- Two distinct singletons on a three-point ground set. -/
def twoSingletonsThree : Family (Fin 3) := {{0}, {1}}

theorem twoSingletonsThree_admissible :
    ProblemAdmissible twoSingletonsThree 2 := by
  refine ⟨?_, ?_⟩
  · intro s hs t ht hne hsub
    have hs' : s = {0} ∨ s = {1} := by simpa [twoSingletonsThree] using hs
    have ht' : t = {0} ∨ t = {1} := by simpa [twoSingletonsThree] using ht
    rcases hs' with hs0 | hs1 <;> rcases ht' with ht0 | ht1
    all_goals simp_all
  · intro t ht
    obtain ⟨s, hs⟩ := ht
    have hscard : s.card = t := (mem_level.mp hs).2
    have hsF : s ∈ twoSingletonsThree := (mem_level.mp hs).1
    have ht1 : t = 1 := by
      simp only [twoSingletonsThree, Finset.mem_insert, Finset.mem_singleton] at hsF
      rcases hsF with rfl | rfl <;> simpa using hscard.symm
    rw [ht1]
    decide +kernel

theorem twoSingletonsThree_occupied : occupiedLevels twoSingletonsThree = {1} := by
  decide

theorem twoSingletonsThree_card : (occupiedLevels twoSingletonsThree).card = 1 := by
  rw [twoSingletonsThree_occupied]
  simp

/-- At n=3 and multiplicity 2, no admissible family can occupy two levels. -/
theorem r2_three_upper (F : Family (Fin 3))
    (hF : IsMultiplicityAntichain F 2) :
    (occupiedLevels F).card ≤ 1 := by
  classical
  by_cases hone : 1 ∈ occupiedLevels F
  · have h := card_occupiedLevels_le_of_one
      (by omega) (by omega) hF hone
    simpa using h
  have hsub : occupiedLevels F ⊆ {2} := by
    intro i hi
    have hin := (mem_occupiedLevels.mp hi).1
    have hi0 : i ≠ 0 := by
      intro heq
      subst i
      exact zero_not_mem_occupiedLevels (by omega) hF hi
    have hi3 : i ≠ 3 := by
      intro heq
      subst i
      exact top_not_mem_occupiedLevels (by omega) hF hi
    have hi1 : i ≠ 1 := by
      intro heq
      subst i
      exact hone hi
    have hi2 : i = 2 := by omega
    simpa using hi2
  simpa using Finset.card_le_card hsub

end JSP636

#print axioms JSP636.r2_target_everywhere
#print axioms JSP636.r3_target_everywhere
#print axioms JSP636.r3_eight_upper
#print axioms JSP636.twoSingletonsThree_admissible
