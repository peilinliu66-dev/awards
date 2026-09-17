/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/FourWitness.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Forces
import EmptyPentagon.Certificate
import EmptyPentagon.TriangleInterior

noncomputable section
namespace Horton

/-- A triangle with one interior point has no empty convex quadrilateral. -/
theorem not_forcesEmptyKGon_four_four : ¬ ForcesEmptyKGon 4 4 := by
  intro h
  set S : Finset Point := {((0 : ℝ), (0 : ℝ)), (4, 0), (0, 4), (1, 1)} with hS
  have hcard : S.card = 4 := by
    rw [hS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair] <;>
      norm_num [Prod.ext_iff]
  have hgen : GeneralPosition S := by
    intro a ha b hb c hc hab hac hbc
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at ha hb hc
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hab
      | exact absurd rfl hac
      | exact absurd rfl hbc
      | norm_num [orient]
  obtain ⟨V, hV4, hVS, hconv, -⟩ := h S hcard hgen
  have hVeq : V = S := Finset.eq_of_subset_of_card_le hVS (by rw [hcard, hV4])
  subst hVeq
  refine not_convexIndependent_of_mem_convexHull_triple S (0, 0) (4, 0) (0, 4) (1, 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hconv
  · simp [hS]
  · simp [hS]
  · simp [hS]
  · simp [hS]
  · norm_num [Prod.ext_iff]
  · norm_num [Prod.ext_iff]
  · norm_num [Prod.ext_iff]
  · exact interior_subset (mem_interior_triangle_of_orient_pos _ _ _ _
      (by norm_num [orient]) (by norm_num [orient]) (by norm_num [orient]) (by norm_num [orient]))

end Horton
