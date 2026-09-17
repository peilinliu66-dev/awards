/-
Released under the MIT license.
Complete original-model classification, assembled from the proved I.A core
and the credited small-polygon and Horton formalizations.
-/
import JSP198NicolasCaseIAComplete

noncomputable section
open Classical Horton
namespace JSP198.FinalAssembly
open Nicolas

theorem four_layer_finish
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) : HasEmptySix P :=
  four_layer_finish_conditional remainingCaseIACore P hgp hmin o ho

theorem hasEmptySix_at_bound
    (P : Finset Point) (hcard : es25Bound ≤ P.card)
    (hgp : GeneralPosition P) : HasEmptySix P :=
  hasEmptySix_at_bound_conditional remainingCaseIACore P hcard hgp

theorem original_six_bound : Prize.Geometry.ForcesEmptyKGon es25Bound 6 :=
  original_six_bound_conditional remainingCaseIACore

theorem original_six_threshold :
    ∃ g6 : ℕ, g6 ≤ es25Bound ∧
      ∀ N, Prize.Geometry.ForcesEmptyKGon N 6 ↔ g6 ≤ N :=
  original_six_threshold_conditional remainingCaseIACore

theorem finite_threshold_iff (k : ℕ) (hk : 3 ≤ k) :
    (∃ N, Prize.Geometry.ForcesEmptyKGon N k) ↔ k ≤ 6 :=
  finite_threshold_iff_conditional remainingCaseIACore k hk

/-- Exact small thresholds, a genuine finite least hexagon threshold with an
explicit upper bound, and arbitrary-size integer-coordinate counterexamples
for every larger polygon size, all in the original at-least-N model. -/
theorem erdos216_classification :
    (∀ N, Prize.Geometry.ForcesEmptyKGon N 3 ↔ 3 ≤ N) ∧
    (∀ N, Prize.Geometry.ForcesEmptyKGon N 4 ↔ 5 ≤ N) ∧
    (∀ N, Prize.Geometry.ForcesEmptyKGon N 5 ↔ 10 ≤ N) ∧
    (∃ g6 : ℕ, g6 ≤ es25Bound ∧
      ∀ N, Prize.Geometry.ForcesEmptyKGon N 6 ↔ g6 ≤ N) ∧
    (∀ k, 7 ≤ k → ∀ N, ∃ P : Finset Point, P.card = N ∧
      Prize.Geometry.GeneralPosition (P : Set Point) ∧
      ¬ Prize.Geometry.HasEmptyKGon k P ∧
      (∀ q ∈ P, ∃ x y : ℤ, q = ((x : ℝ), (y : ℝ)))) :=
  erdos216_classification_conditional remainingCaseIACore

end JSP198.FinalAssembly

#print axioms JSP198.FinalAssembly.remainingCaseIACore
#print axioms JSP198.FinalAssembly.hasEmptySix_at_bound
#print axioms JSP198.FinalAssembly.original_six_threshold
#print axioms JSP198.FinalAssembly.finite_threshold_iff
#print axioms JSP198.FinalAssembly.erdos216_classification
