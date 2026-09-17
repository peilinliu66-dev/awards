/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/SmallHoles.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Forces
import EmptyPentagon.Parabola
import EmptyPentagon.Monotone
import EmptyPentagon.Triangle
import EmptyPentagon.FourWitness
import EmptyPentagon.Quadrilateral
import EmptyPentagon.NineWitness
import EmptyPentagon.Harborth

noncomputable section
namespace Horton

/-- `h(3) = 3`: three points force an empty triangle, and no smaller number does. -/
theorem forces_empty_triangle_iff (n : ℕ) : ForcesEmptyKGon 3 n ↔ 3 ≤ n :=
  ⟨fun h ↦ h.le, fun h ↦ forcesEmptyKGon_of_le forcesEmptyKGon_three_three h⟩

/-- `h(4) = 5`: five points force an empty convex quadrilateral, and no smaller number does. -/
theorem forces_empty_quadrilateral_iff (n : ℕ) : ForcesEmptyKGon 4 n ↔ 5 ≤ n := by
  refine ⟨fun h ↦ ?_, fun h ↦ forcesEmptyKGon_of_le forcesEmptyKGon_four_five h⟩
  by_contra hn
  exact not_forcesEmptyKGon_of_le not_forcesEmptyKGon_four_four (by omega) h

/-- `h(5) = 10` (Harborth 1978): ten points force an empty convex pentagon, and no smaller
number does. -/
theorem forces_empty_pentagon_iff (n : ℕ) : ForcesEmptyKGon 5 n ↔ 10 ≤ n := by
  constructor
  · intro h
    by_contra hlt
    exact not_forcesEmptyKGon_of_le not_forcesEmptyKGon_five_nine (by omega) h
  · intro h
    exact forcesEmptyKGon_of_le forcesEmptyKGon_five_ten h

end Horton

#print axioms Horton.forces_empty_triangle_iff
#print axioms Horton.forces_empty_quadrilateral_iff
#print axioms Horton.forces_empty_pentagon_iff
