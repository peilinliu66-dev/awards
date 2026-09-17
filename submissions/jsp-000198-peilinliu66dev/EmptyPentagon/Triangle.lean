/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Triangle.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Forces
import EmptyPentagon.Certificate

noncomputable section
namespace Horton

/-- In a triangle `{u, w, v}` with `orient u w v < 0`, the line through `u` and `w` separates
`v` from the remaining vertices, which lie on that line. -/
theorem separated_of_orient_neg (V : Finset Point) (u w v : Point) (hu : u ∈ V) (hw : w ∈ V)
    (huw : u ≠ w) (h : orient u w v < 0) (hV : ∀ x ∈ V, x = u ∨ x = w ∨ x = v) :
    ∃ u' ∈ V, ∃ w' ∈ V, u' ≠ w' ∧ orient u' w' v < 0 ∧
      ∀ x ∈ V, x ≠ v → 0 ≤ orient u' w' x := by
  refine ⟨u, hu, w, hw, huw, h, fun x hx hxv => ?_⟩
  rcases hV x hx with rfl | rfl | rfl
  · exact le_of_eq (by unfold orient; ring)
  · exact le_of_eq (by unfold orient; ring)
  · exact absurd rfl hxv

/-- Three points in general position form an empty convex triangle. -/
theorem forcesEmptyKGon_three_three : ForcesEmptyKGon 3 3 := by
  intro S hcard hgp
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  refine ⟨{a, b, c}, hcard, ?_⟩
  unfold EmptyConvexPolygon
  refine ⟨Finset.Subset.refl _, ?_, fun p hp hpn => absurd hp hpn⟩
  have hD : orient a b c ≠ 0 := hgp a (by simp) b (by simp) c (by simp) hab hac hbc
  have hmem : ∀ x ∈ ({a, b, c} : Finset Point), x = a ∨ x = b ∨ x = c := fun x hx => by
    simpa using hx
  apply convexIndependent_of_separated
  intro v hv
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · rcases hmem v hv with hva | hvb | hvc
    · rw [hva]
      exact separated_of_orient_neg _ b c a (by simp) (by simp) hbc
        (by rw [show orient b c a = orient a b c by unfold orient; ring]; exact hneg)
        fun x hx => by have := hmem x hx; tauto
    · rw [hvb]
      exact separated_of_orient_neg _ c a b (by simp) (by simp) hac.symm
        (by rw [show orient c a b = orient a b c by unfold orient; ring]; exact hneg)
        fun x hx => by have := hmem x hx; tauto
    · rw [hvc]
      exact separated_of_orient_neg _ a b c (by simp) (by simp) hab hneg
        fun x hx => by have := hmem x hx; tauto
  · rcases hmem v hv with hva | hvb | hvc
    · rw [hva]
      exact separated_of_orient_neg _ c b a (by simp) (by simp) hbc.symm
        (by rw [show orient c b a = -orient a b c by unfold orient; ring]; linarith)
        fun x hx => by have := hmem x hx; tauto
    · rw [hvb]
      exact separated_of_orient_neg _ a c b (by simp) (by simp) hac
        (by rw [show orient a c b = -orient a b c by unfold orient; ring]; linarith)
        fun x hx => by have := hmem x hx; tauto
    · rw [hvc]
      exact separated_of_orient_neg _ b a c (by simp) (by simp) hab.symm
        (by rw [show orient b a c = -orient a b c by unfold orient; ring]; linarith)
        fun x hx => by have := hmem x hx; tauto

end Horton
