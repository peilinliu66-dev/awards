import EmptyPentagon.Comparators
import EmptyPentagon.Monotone
import Prize.Geometry.EmptyPolygon

/-!
# Exact correspondence of the two reused empty-polygon models

This module proves the correspondence of the actual definitions used by the
MIT-licensed PR283 small-k library and the PR73 Horton construction.  It adds
no geometrical assumption.  In particular the passage from exactly N points
to at least N points uses the proved hull-vertex deletion theorem; arbitrary
restriction of the ambient point set would not preserve emptiness.

Upstream provenance and licenses are retained under EmptyPentagon/ and Prize/.
This is an integration module, not a new mathematical discovery.
-/

noncomputable section

namespace JSP198.ModelBridge

theorem generalPosition_iff (P : Finset Horton.Point) :
    Horton.GeneralPosition P ↔
      Prize.Geometry.GeneralPosition (P : Set Horton.Point) := by
  exact Horton.generalPosition_iff_not_collinear P

theorem emptyConvexPolygon_iff (P V : Finset Horton.Point) :
    Horton.EmptyConvexPolygon P V ↔
      Prize.Geometry.EmptyConvex (P : Set Horton.Point) (V : Set Horton.Point) := by
  classical
  constructor
  · rintro ⟨hsub, hconv, hempty⟩
    refine ⟨hsub, hconv, ?_⟩
    intro x hx hinterior
    by_contra hout
    exact hempty x hx hout hinterior
  · intro h
    refine ⟨h.subset, h.convexIndependent, ?_⟩
    intro x hx hout hinterior
    exact hout (h.empty x hx hinterior)

theorem hasEmptyKGon_iff (k : ℕ) (P : Finset Horton.Point) :
    (∃ V : Finset Horton.Point, V.card = k ∧ Horton.EmptyConvexPolygon P V) ↔
      Prize.Geometry.HasEmptyKGon k P := by
  constructor
  · rintro ⟨V, hcard, hV⟩
    exact ⟨V, hcard, (emptyConvexPolygon_iff P V).mp hV⟩
  · rintro ⟨V, hcard, hV⟩
    exact ⟨V, hcard, (emptyConvexPolygon_iff P V).mpr hV⟩

theorem forcesEmptyKGon_iff (k N : ℕ) :
    Horton.ForcesEmptyKGon k N ↔ Prize.Geometry.ForcesEmptyKGon N k := by
  constructor
  · intro h P hcard hgp
    apply (hasEmptyKGon_iff k P).mp
    exact Horton.forcesEmptyKGon_of_le h hcard P rfl
      ((generalPosition_iff P).mpr hgp)
  · intro h P hcard hgp
    apply (hasEmptyKGon_iff k P).mpr
    exact h P (Nat.le_of_eq hcard.symm) ((generalPosition_iff P).mp hgp)

end JSP198.ModelBridge

#print axioms JSP198.ModelBridge.generalPosition_iff
#print axioms JSP198.ModelBridge.emptyConvexPolygon_iff
#print axioms JSP198.ModelBridge.hasEmptyKGon_iff
#print axioms JSP198.ModelBridge.forcesEmptyKGon_iff
