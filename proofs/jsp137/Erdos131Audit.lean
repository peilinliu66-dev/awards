/-
Literal-scope endpoint audit. Compiled and audited; see BUILD_REPORT.json.
This file imports the actual proof, never the comparator Challenge placeholder.
-/
import Nondividing.FinalAssembly

open scoped BigOperators

namespace Erdos131Research.OriginalStatement

def NonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S.Nonempty → S ⊆ A.erase a → ¬a ∣ ∑ s ∈ S, s

noncomputable def candidates (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter NonDividing

noncomputable def F (N : ℕ) : ℕ := (candidates N).sup Finset.card

theorem nonDividing_eq : NonDividing = Nondividing.NonDividing := rfl

theorem F_eq : F = Nondividing.F := rfl

/-- Full arbitrary-nonempty-subset growth endpoint, with no additional premise. -/
theorem original_growth :
    Filter.Tendsto (fun N : ℕ => Real.log (F N) / Real.log N)
      Filter.atTop (nhds ((1 : ℝ) / 5)) := by
  change Filter.Tendsto (fun N : ℕ => Real.log (Nondividing.F N) / Real.log N)
    Filter.atTop (nhds ((1 : ℝ) / 5))
  exact Nondividing.main_log_limit

end Erdos131Research.OriginalStatement

#check Nondividing.main_log_limit
#check Erdos131Research.OriginalStatement.original_growth
#print Erdos131Research.OriginalStatement.NonDividing
#print Erdos131Research.OriginalStatement.F
#print Erdos131Research.OriginalStatement.candidates
#print axioms Nondividing.External.cfp_structure
#print axioms Nondividing.External.discrete_john
#print axioms Nondividing.External.zonotope_rounding
#print axioms Nondividing.External.convex_density_set
#print axioms Nondividing.External.blaschke_selection
#print axioms Nondividing.External.convexBody_volume_tendsto
#print axioms Nondividing.External.rogers_shephard
#print axioms Nondividing.External.full_rank_lattice_points_le_volume
#print axioms Nondividing.main_log_limit
#print axioms Erdos131Research.OriginalStatement.original_growth
