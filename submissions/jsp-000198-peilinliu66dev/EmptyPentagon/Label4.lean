/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Label4.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Certificate
import EmptyPentagon.TriangleInterior
import EmptyPentagon.CyclicLabel

noncomputable section
namespace Horton

/-- A member of a convex-independent set in general position cannot see three other members
in cyclic (all counterclockwise) order: it would lie strictly inside their triangle. -/
theorem not_cyclic_of_convexIndependent (V : Finset Point)
    (hV : ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point))) (o a b c : Point)
    (ho : o ∈ V) (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V)
    (hoa : o ≠ a) (hob : o ≠ b) (hoc : o ≠ c)
    (h1 : 0 < orient o a b) (h2 : 0 < orient o b c) (h3 : 0 < orient o c a) : False := by
  have habc : 0 < orient a b c := by
    unfold orient at *
    linarith
  have hmem := mem_interior_triangle_of_orient_pos a b c o habc
    (by unfold orient at *; linarith) (by unfold orient at *; linarith)
    (by unfold orient at *; linarith)
  exact not_convexIndependent_of_mem_convexHull_triple V a b c o ha hb hc ho hoa hob hoc
    (interior_subset hmem) hV

/-- Three members `w2, w3, w4` of a convex-independent set in general position, seen in
counterclockwise angular order from a fourth member `w1`, give a counterclockwise 4-cycle. -/
theorem ccw_cycle_of_angular_order (V : Finset Point) (hgp : GeneralPosition V)
    (hV : ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point))) (w1 w2 w3 w4 : Point)
    (h1 : w1 ∈ V) (h2 : w2 ∈ V) (h3 : w3 ∈ V) (h4 : w4 ∈ V)
    (h123 : 0 < orient w1 w2 w3) (h134 : 0 < orient w1 w3 w4) (h124 : 0 < orient w1 w2 w4) :
    0 < orient w1 w2 w3 ∧ 0 < orient w2 w3 w4 ∧ 0 < orient w3 w4 w1 ∧ 0 < orient w4 w1 w2 := by
  have h234 := orient_pos_of_angular_order V hgp hV w1 w2 w3 w4 h1 h2 h3 h4 h123 h134 h124
  refine ⟨h123, h234, ?_, ?_⟩
  · have e : orient w3 w4 w1 = orient w1 w3 w4 := by
      unfold orient
      ring
    rw [e]
    exact h134
  · have e : orient w4 w1 w2 = orient w1 w2 w4 := by
      unfold orient
      ring
    rw [e]
    exact h124

/-- A convex-independent 4-set in general position can be labelled counterclockwise. -/
theorem exists_cyclic_labeling4 (V : Finset Point) (hcard : V.card = 4) (hgp : GeneralPosition V)
    (hV : ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point))) :
    ∃ w1 w2 w3 w4 : Point, ({w1, w2, w3, w4} : Finset Point) = V ∧
      0 < orient w1 w2 w3 ∧ 0 < orient w2 w3 w4 ∧ 0 < orient w3 w4 w1 ∧ 0 < orient w4 w1 w2 := by
  classical
  obtain ⟨o, hoV⟩ : V.Nonempty := Finset.card_pos.mp (by omega)
  have hWcard : (V.erase o).card = 3 := by
    rw [Finset.card_erase_of_mem hoV, hcard]
  obtain ⟨a, b, c, hab, hac, hbc, hW⟩ := Finset.card_eq_three.mp hWcard
  have hVeq : V = {o, a, b, c} := by
    rw [← Finset.insert_erase hoV, hW]
  have haW : a ∈ V.erase o := by
    rw [hW]
    simp
  have hbW : b ∈ V.erase o := by
    rw [hW]
    simp
  have hcW : c ∈ V.erase o := by
    rw [hW]
    simp
  have haV : a ∈ V := Finset.mem_of_mem_erase haW
  have hbV : b ∈ V := Finset.mem_of_mem_erase hbW
  have hcV : c ∈ V := Finset.mem_of_mem_erase hcW
  have hoa : o ≠ a := (Finset.ne_of_mem_erase haW).symm
  have hob : o ≠ b := (Finset.ne_of_mem_erase hbW).symm
  have hoc : o ≠ c := (Finset.ne_of_mem_erase hcW).symm
  have sab : orient o a b ≠ 0 := hgp o hoV a haV b hbV hoa hob hab
  have sbc : orient o b c ≠ 0 := hgp o hoV b hbV c hcV hob hoc hbc
  have sca : orient o c a ≠ 0 := hgp o hoV c hcV a haV hoc hoa hac.symm
  have swap : ∀ q r : Point, orient o r q = -orient o q r := by
    intro q r
    unfold orient
    ring
  have hset : ∀ x y z : Point, ({x, y, z} : Finset Point) = {a, b, c} →
      ({o, x, y, z} : Finset Point) = V := by
    intro x y z h
    rw [hVeq, ← h]
  rcases lt_or_gt_of_ne sab with nab | pab <;> rcases lt_or_gt_of_ne sbc with nbc | pbc <;>
    rcases lt_or_gt_of_ne sca with nca | pca
  · -- all negative: `o` is inside triangle `a c b`
    exact absurd hV (fun hV => not_cyclic_of_convexIndependent V hV o a c b hoV haV hcV hbV
      hoa hoc hob (by linarith [swap a c]) (by linarith [swap c b]) (by linarith [swap b a]))
  · -- c < b < a
    refine ⟨o, c, b, a, hset c b a ?_, ccw_cycle_of_angular_order V hgp hV o c b a hoV hcV hbV
      haV (by linarith [swap b c]) (by linarith [swap a b]) pca⟩
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · -- b < a < c
    refine ⟨o, b, a, c, hset b a c ?_, ccw_cycle_of_angular_order V hgp hV o b a c hoV hbV haV
      hcV (by linarith [swap a b]) (by linarith [swap c a]) pbc⟩
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · -- b < c < a
    refine ⟨o, b, c, a, hset b c a ?_, ccw_cycle_of_angular_order V hgp hV o b c a hoV hbV hcV
      haV pbc pca (by linarith [swap a b])⟩
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · -- a < c < b
    refine ⟨o, a, c, b, hset a c b ?_, ccw_cycle_of_angular_order V hgp hV o a c b hoV haV hcV
      hbV (by linarith [swap c a]) (by linarith [swap b c]) pab⟩
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · -- c < a < b
    refine ⟨o, c, a, b, hset c a b ?_, ccw_cycle_of_angular_order V hgp hV o c a b hoV hcV haV
      hbV pca pab (by linarith [swap b c])⟩
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · -- a < b < c
    exact ⟨o, a, b, c, hVeq.symm, ccw_cycle_of_angular_order V hgp hV o a b c hoV haV hbV hcV
      pab pbc (by linarith [swap c a])⟩
  · -- all positive: `o` is inside triangle `a b c`
    exact absurd hV (fun hV => not_cyclic_of_convexIndependent V hV o a b c hoV haV hbV hcV
      hoa hob hoc pab pbc pca)

/-- A 3-set in general position can be labelled counterclockwise. -/
theorem exists_ccw_triangle (V : Finset Point) (hcard : V.card = 3) (hgp : GeneralPosition V) :
    ∃ v1 v2 v3 : Point, ({v1, v2, v3} : Finset Point) = V ∧ 0 < orient v1 v2 v3 := by
  obtain ⟨a, b, c, hab, hac, hbc, hV⟩ := Finset.card_eq_three.mp hcard
  have haV : a ∈ V := by
    rw [hV]
    simp
  have hbV : b ∈ V := by
    rw [hV]
    simp
  have hcV : c ∈ V := by
    rw [hV]
    simp
  have hne : orient a b c ≠ 0 := hgp a haV b hbV c hcV hab hac hbc
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine ⟨a, c, b, ?_, ?_⟩
    · rw [hV, Finset.pair_comm]
    · have e : orient a c b = -orient a b c := by
        unfold orient
        ring
      rw [e]
      linarith
  · exact ⟨a, b, c, hV.symm, hpos⟩

end Horton
