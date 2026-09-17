import JSP198FiniteRamsey
import ESSelection

/-!
# The finite planar Erdős--Szekeres theorem for 25 points

The classical theorem is instantiated at a deliberately non-optimal finite
Ramsey bound. No finite Ramsey or geometric theorem is assumed as a parameter.
This is a prerequisite for the empty-hexagon problem, not its geometric core.
-/

noncomputable section
namespace Horton

/-- An explicit, unevaluated finite bound. Its recurrence is proved in
`JSP198.FiniteRamsey.tripleFanBound_succ_eq_pow`. -/
def es25Bound : ℕ := JSP198.FiniteRamsey.tripleBound 25

/-- Every sufficiently large finite planar set in general position contains
25 points in convex position, at the explicit finite Ramsey bound. -/
theorem exists_convex25_at_bound (S : Finset Point)
    (hS : es25Bound ≤ S.card) (hgp : GeneralPosition S) :
    ∃ T : Finset Point, T ⊆ S ∧ T.card = 25 ∧
      ConvexIndependent ℝ (fun x : (T : Set Point) => (x : Point)) := by
  apply exists_convex25_of_orderedTripleRamsey es25Bound ?_ S hS hgp
  intro C
  exact JSP198.finite_ramsey_triples_ordered_at_bound 25 C

/-- The unconditional finite ES(25) existence statement. -/
theorem erdos_szekeres_25 :
    ∃ N : ℕ, ∀ S : Finset Point, N ≤ S.card → GeneralPosition S →
      ∃ T : Finset Point, T ⊆ S ∧ T.card = 25 ∧
        ConvexIndependent ℝ (fun x : (T : Set Point) => (x : Point)) := by
  exact ⟨es25Bound, exists_convex25_at_bound⟩

end Horton

#print axioms Horton.exists_convex25_at_bound
#print axioms Horton.erdos_szekeres_25
