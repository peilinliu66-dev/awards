/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Wedge.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Certificate
import EmptyPentagon.TriangleInterior
import EmptyPentagon.Pentagon

noncomputable section
namespace Horton

/-- Wedge partition: a point of general position outside a counterclockwise pentagon `P` with
interior point `M` lies beyond some edge `i`, between the rays from `M` through `P i` and
`P (i+1)`. -/
theorem exists_wedge (P : Fin 5 → Point) (M R : Point)
    (hccw : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (P i) (P (i + 1)) (P j))
    (hM : M ∈ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point)))
    (hR : R ∉ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point)))
    (hRM : ∀ i, orient M (P i) R ≠ 0) (hRE : ∀ i, orient (P i) (P (i + 1)) R ≠ 0) :
    ∃ i : Fin 5, 0 < orient M (P i) R ∧ orient M (P (i + 1)) R < 0 ∧
      orient (P i) (P (i + 1)) R < 0 := by
  have hRM' : R ≠ M := by
    intro h
    apply hRM 0
    rw [h]
    exact orient_self_left _ _
  have hnotpos : ¬ ∀ i, 0 < orient M (P i) R := by
    intro hall
    refine not_mem_interior_convexHull_of_halfplane _ R M M hRM' ?_ ?_ hM
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      have := hall i
      rw [orient_cyc, orient_cyc] at this
      exact le_of_lt this
    · exact le_of_eq (orient_self_right _ _)
  have hnotneg : ¬ ∀ i, orient M (P i) R < 0 := by
    intro hall
    refine not_mem_interior_convexHull_of_halfplane _ M R M hRM'.symm ?_ ?_ hM
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      have := hall i
      rw [orient_swap] at this
      linarith
    · exact le_of_eq (orient_self_left _ _)
  push Not at hnotpos hnotneg
  obtain ⟨i0, hi0⟩ := hnotneg
  have hstep : ∃ i, 0 < orient M (P i) R ∧ orient M (P (i + 1)) R < 0 := by
    by_contra hcon
    push Not at hcon
    have hpos : ∀ i, 0 < orient M (P i) R → 0 < orient M (P (i + 1)) R :=
      fun i h => lt_of_le_of_ne (hcon i h) (hRM _).symm
    have h0 : 0 < orient M (P i0) R := lt_of_le_of_ne hi0 (hRM _).symm
    have h1 := hpos _ h0
    have h2 := hpos _ h1
    have h3 := hpos _ h2
    have h4 := hpos _ h3
    obtain ⟨j, hj⟩ := hnotpos
    have key : ∀ i j : Fin 5, j = i ∨ j = i + 1 ∨ j = i + 1 + 1 ∨ j = i + 1 + 1 + 1 ∨
        j = i + 1 + 1 + 1 + 1 := by decide
    rcases key i0 j with rfl | rfl | rfl | rfl | rfl
    · exact absurd h0 (not_lt.mpr hj)
    · exact absurd h1 (not_lt.mpr hj)
    · exact absurd h2 (not_lt.mpr hj)
    · exact absurd h3 (not_lt.mpr hj)
    · exact absurd h4 (not_lt.mpr hj)
  obtain ⟨i, hi, hi1⟩ := hstep
  refine ⟨i, hi, hi1, ?_⟩
  rcases lt_or_gt_of_ne (hRE i) with h | h
  · exact h
  · exfalso
    apply hR
    have htri : 0 < orient M (P i) (P (i + 1)) := by
      have := orient_edge_pos_of_mem_interior P M hM hccw i
      rwa [orient_cyc, orient_cyc] at this
    have hc : 0 < orient (P (i + 1)) M R := by
      rw [orient_cyc, orient_swap]
      linarith
    have hint := mem_interior_triangle_of_orient_pos M (P i) (P (i + 1)) R htri hi h hc
    refine interior_mono (convexHull_min ?_ (convex_convexHull ℝ _)) hint
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact interior_subset hM
    · exact subset_convexHull ℝ _ (by simp)
    · exact subset_convexHull ℝ _ (by simp)

end Horton
