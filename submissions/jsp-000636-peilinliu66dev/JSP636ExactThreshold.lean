import Mathlib
import JSP636Maximum
import Erdos776.Uniform.ProblemStatement

/-!
# Complete maximum-value and strict-threshold formulation of Erdős 776

The original threshold is about the MAXIMUM number of occupied levels,
not only existence of a family with `n-3` levels.  In particular the latter
existence-only definition has an unwanted natural-subtraction boundary at r=2.
We keep every upstream API unchanged and define the correct interface here.

Small parameter values: Yixin He and Quanyu Tang (2026).
All r≥4 values and their construction/obstruction proofs: Thiim's upstream
mthiim/erdos_776, commit 1ca43203123642edaac45bf00b6fc333c848b4c9.
Upstream copyright (c) 2026 mthiim and contributors, MIT;
see LICENSE-JSP636-MIT.txt. New extension proof bodies prepared with ChatGPT.

Target: Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
See verification/ for actual build reports, including native-evaluation dependencies.
-/

namespace JSP636
noncomputable section

open Finset
open Erdos776.Antichain Erdos776.Uniform

/-- The full four-branch answer. Values at r=0,1 are immaterial;
all public resolution theorems require r≥2. -/
def thresholdFormula (r : ℕ) : ℕ :=
  if r = 2 then 3 else if r = 3 then 8 else
    if r ≤ 10 then 2 * r + 4 else 2 * r + 5

@[simp] theorem thresholdFormula_two : thresholdFormula 2 = 3 := by
  norm_num [thresholdFormula]

@[simp] theorem thresholdFormula_three : thresholdFormula 3 = 8 := by
  norm_num [thresholdFormula]

theorem thresholdFormula_ge_four {r : ℕ} (hr : 4 ≤ r) :
    thresholdFormula r = erdosThresholdFromFour r := by
  simp [thresholdFormula, erdosThresholdFromFour,
    show r ≠ 2 by omega, show r ≠ 3 by omega]

theorem thresholdFormula_small {r : ℕ} (hr4 : 4 ≤ r) (hr10 : r ≤ 10) :
    thresholdFormula r = 2 * r + 4 := by
  rw [thresholdFormula_ge_four hr4]
  simp [erdosThresholdFromFour, hr10]

theorem thresholdFormula_large {r : ℕ} (hr : 11 ≤ r) :
    thresholdFormula r = 2 * r + 5 := by
  rw [thresholdFormula_ge_four (by omega)]
  simp [erdosThresholdFromFour, show ¬ r ≤ 10 by omega]

theorem three_le_thresholdFormula {r : ℕ} (hr : 2 ≤ r) :
    3 ≤ thresholdFormula r := by
  by_cases h2 : r = 2
  · subst r
    simp
  by_cases h3 : r = 3
  · subst r
    simp
  have hr4 : 4 ≤ r := by omega
  rw [thresholdFormula_ge_four hr4]
  unfold erdosThresholdFromFour
  split_ifs <;> omega

/-- Every r≥4 public upstream endpoint is bridged to the true maximum.
The upper bound is independently supplied by the all-r extension. -/
theorem last_failure_ge_four (r : ℕ) (hr : 4 ≤ r) :
    (¬ OptimalLevels (erdosThresholdFromFour r) r
      (erdosThresholdFromFour r - 3)) ∧
    (∀ n : ℕ, erdosThresholdFromFour r < n →
      OptimalLevels n r (n - 3)) := by
  have hupstream := erdos776_lastFailure r hr
  refine ⟨fun h => hupstream.1 h.1, ?_⟩
  intro n hn
  have hn4 : 4 ≤ n := by
    unfold erdosThresholdFromFour at hn
    split_ifs at hn <;> omega
  exact optimalLevels_of_target (by omega) hn4 (hupstream.2 n hn)

/-- Unconditional last-failure plus all-larger-success certificate, for every r≥2.
All branches are proved; no construction, profile criterion, or obstruction is
left as an input parameter. -/
theorem all_parameters_last_failure (r : ℕ) (hr : 2 ≤ r) :
    (¬ OptimalLevels (thresholdFormula r) r (thresholdFormula r - 3)) ∧
    (∀ n : ℕ, thresholdFormula r < n → OptimalLevels n r (n - 3)) := by
  by_cases h2 : r = 2
  · subst r
    rw [thresholdFormula_two]
    refine ⟨r2_three_not_optimal, ?_⟩
    intro n hn
    exact optimalLevels_of_target (by omega) (by omega)
      (r2_target_everywhere n (by omega))
  by_cases h3 : r = 3
  · subst r
    rw [thresholdFormula_three]
    refine ⟨r3_eight_not_optimal, ?_⟩
    intro n hn
    exact optimalLevels_of_target (by omega) (by omega)
      (r3_target_everywhere n (by omega))
  have hr4 : 4 ≤ r := by omega
  simpa only [thresholdFormula_ge_four hr4] using last_failure_ge_four r hr4

/-- A last failure proves strict-threshold leastness for the maximum predicate. -/
theorem exactThreshold_of_last_failure {r N : ℕ}
    (hbad : ¬ OptimalLevels N r (N - 3))
    (hgood : ∀ n : ℕ, N < n → OptimalLevels n r (n - 3)) :
    ExactThreshold r N := by
  refine ⟨hgood, ?_⟩
  intro M hM
  by_contra hnot
  exact hbad (hM N (by omega))

/-- Main correct all-parameter least-threshold theorem. -/
theorem erdos776_exactThreshold (r : ℕ) (hr : 2 ≤ r) :
    ExactThreshold r (thresholdFormula r) := by
  have h := all_parameters_last_failure r hr
  exact exactThreshold_of_last_failure h.1 h.2

/-- Every least cutoff is exactly the displayed value, not merely bounded by it. -/
theorem erdos776_exactThreshold_iff (r : ℕ) (hr : 2 ≤ r) (N : ℕ) :
    ExactThreshold r N ↔ N = thresholdFormula r := by
  constructor
  · intro hN
    have h := erdos776_exactThreshold r hr
    exact Nat.le_antisymm (hN.2 _ h.1) (h.2 _ hN.1)
  · intro hN
    subst N
    exact erdos776_exactThreshold r hr

/-- The threshold is exactly the last failure of the actual equality g(n,r)=n-3. -/
theorem g_last_failure (r : ℕ) (hr : 2 ≤ r) :
    g (thresholdFormula r) r ≠ thresholdFormula r - 3 := by
  intro h
  exact (all_parameters_last_failure r hr).1
    ((optimalLevels_iff_g_eq _ _ _).mpr h)

/-- Literal all-parameter, all-cutoff resolution. The quantifier uses n>N,
not n≥N, and characterizes EVERY proposed cutoff N, not only one witness. -/
theorem erdos776 (r : ℕ) (hr : 2 ≤ r) (N : ℕ) :
    (∀ n : ℕ, N < n → g n r = n - 3) ↔ thresholdFormula r ≤ N := by
  constructor
  · intro h
    apply (erdos776_exactThreshold r hr).2 N
    intro n hn
    exact (optimalLevels_iff_g_eq n r (n - 3)).mpr (h n hn)
  · intro hN n hn
    exact (optimalLevels_iff_g_eq n r (n - 3)).mp
      ((erdos776_exactThreshold r hr).1 n (lt_of_le_of_lt hN hn))

/-- The same all-cutoff terminal, written with the unchanged upstream maximum. -/
theorem erdos776_upstream_maximum (r : ℕ) (hr : 2 ≤ r) (N : ℕ) :
    (∀ n : ℕ, N < n → extremalOccupiedLevels n r = n - 3) ↔
      thresholdFormula r ≤ N := by
  simpa only [← g_eq_extremalOccupiedLevels] using erdos776 r hr N

/-- A terminal directly in the original exact-r convention, with all cutoff
quantifiers. No statement is weakened to a single parameter or mere existence. -/
theorem erdos776_original_exact_multiplicity
    (r : ℕ) (hr : 2 ≤ r) (N : ℕ) :
    (∀ n : ℕ, N < n → ExactOptimalLevels n r (n - 3)) ↔
      thresholdFormula r ≤ N := by
  constructor
  · intro h
    apply (erdos776 r hr N).mp
    intro n hn
    exact (optimalLevels_iff_g_eq n r (n - 3)).mp
      ((exactOptimalLevels_iff (by omega : 0 < r)).mp (h n hn))
  · intro hN n hn
    apply (exactOptimalLevels_iff (by omega : 0 < r)).mpr
    apply (optimalLevels_iff_g_eq n r (n - 3)).mpr
    exact (erdos776 r hr N).mpr hN n hn

end
end JSP636

#print axioms JSP636.erdos776_exactThreshold
#print axioms JSP636.erdos776_exactThreshold_iff
#print axioms JSP636.erdos776_upstream_maximum
#print axioms JSP636.erdos776
#print axioms JSP636.erdos776_original_exact_multiplicity
