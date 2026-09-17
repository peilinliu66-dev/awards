import ES25
import JSP198NicolasLocal

/-!
# Unconditional reduction to a minimal 25-vertex outer layer

This composes the proved finite Ramsey/ES bound with the proved geometric
minimum and safe ambient restriction.  The remaining Nicolás global covering
theorem is not assumed or asserted here.
-/

noncomputable section
namespace JSP198.Nicolas
open Horton

theorem minimal25_setup_at_es_bound
    (P : Finset Point) (hcard : Horton.es25Bound ≤ P.card)
    (hgp : GeneralPosition P) :
    ∃ S : Finset Point,
      S ⊆ P ∧ S.card = 25 ∧ InConvexPosition S ∧
      MinimalOuter (hullCut P S) ∧
      GeneralPosition (hullCut P S) ∧
      hullVertices (hullCut P S) = S ∧
      (∀ T : Finset Point, EmptyConvexPolygon (hullCut P S) T →
        EmptyConvexPolygon P T) := by
  obtain ⟨S, hSP, hS25, hconv⟩ :=
    Horton.exists_convex25_at_bound P hcard hgp
  exact convex25_minimal_setup P hgp ⟨S, hSP, hconv, hS25⟩

theorem hexagon_free_minimal25_reduction
    (P : Finset Point) (hcard : Horton.es25Bound ≤ P.card)
    (hgp : GeneralPosition P) (hno : ¬ HasEmptySix P) :
    ∃ Q : Finset Point, Q ⊆ P ∧ GeneralPosition Q ∧
      MinimalOuter Q ∧ (hullVertices Q).card = 25 ∧ ¬ HasEmptySix Q := by
  obtain ⟨S, _, hS25, _, hmin, hgpQ, hHull, htransport⟩ :=
    minimal25_setup_at_es_bound P hcard hgp
  refine ⟨hullCut P S, hullCut_subset P S, hgpQ, hmin, ?_, ?_⟩
  · rw [hHull]
    exact hS25
  · rintro ⟨T, hT6, hT⟩
    exact hno ⟨T, hT6, htransport T hT⟩

end JSP198.Nicolas

#print axioms JSP198.Nicolas.minimal25_setup_at_es_bound
#print axioms JSP198.Nicolas.hexagon_free_minimal25_reduction
