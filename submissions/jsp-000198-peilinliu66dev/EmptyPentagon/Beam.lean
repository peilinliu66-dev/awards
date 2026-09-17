/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Beam.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Certificate
import EmptyPentagon.Signs
import EmptyPentagon.Pentagon

noncomputable section
namespace Horton

/-- Extend a discharged hypothesis list of a sign implication by further literals. -/
theorem litHolds_append {p : Fin 5 → Point} {l₁ l₂ : List Lit} (h₁ : ∀ l ∈ l₁, LitHolds p l)
    (h₂ : ∀ l ∈ l₂, LitHolds p l) : ∀ l ∈ l₁ ++ l₂, LitHolds p l :=
  List.forall_mem_append.2 ⟨h₁, h₂⟩

/-- The line `p u → p w` separates `p v` from the other points of the image of `p`, given the
strict signs at `p v` and at the two remaining points `p a`, `p b`. -/
theorem separated_of_signs (p : Fin 5 → Point) (hinj : Function.Injective p) (u w v a b : Fin 5)
    (huw : u ≠ w) (hcover : ∀ i : Fin 5, i = u ∨ i = w ∨ i = v ∨ i = a ∨ i = b)
    (hneg : orient (p u) (p w) (p v) < 0) (ha : 0 < orient (p u) (p w) (p a))
    (hb : 0 < orient (p u) (p w) (p b)) :
    ∃ u' ∈ (Finset.univ.image p : Finset Point), ∃ w' ∈ (Finset.univ.image p : Finset Point),
      u' ≠ w' ∧ orient u' w' (p v) < 0 ∧
        ∀ x ∈ (Finset.univ.image p : Finset Point), x ≠ p v → 0 ≤ orient u' w' x := by
  refine ⟨p u, Finset.mem_image_of_mem p (Finset.mem_univ u), p w,
    Finset.mem_image_of_mem p (Finset.mem_univ w), fun h => huw (hinj h), hneg, ?_⟩
  intro x hx hxv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
  rcases hcover i with rfl | rfl | rfl | rfl | rfl
  · exact (orient_left_self _ _).ge
  · exact (orient_right_self _ _).ge
  · exact absurd rfl hxv
  · exact ha.le
  · exact hb.le

/-- The seven literal hypotheses of the beam lemma common to both cases. -/
def beamCore : List Lit :=
  [(0, 1, 2, true), (0, 1, 3, true), (0, 3, 2, true), (1, 2, 3, false), (0, 1, 4, true),
    (0, 4, 2, true), (1, 2, 4, false)]

/-- The literal hypotheses of the beam lemma; `b` is the common sign of `z, v1, v3` with respect
to the directed line `p 3 → p 4`. -/
def beamLits (b : Bool) : List Lit :=
  beamCore ++ [(3, 4, 0, b), (3, 4, 1, b), (3, 4, 2, b)]

/-- The literal hypotheses of the cone covering lemma. -/
def coneLits : List Lit :=
  [(0, 1, 2, true), (0, 1, 3, true), (1, 2, 3, true), (2, 0, 3, true)]

/-- The literal hypotheses of the strip lemma. -/
def stripLits : List Lit :=
  [(0, 1, 2, true), (0, 1, 3, true), (2, 3, 0, true), (2, 3, 1, true), (2, 3, 4, false),
    (0, 3, 4, false), (1, 2, 4, true)]

set_option maxHeartbeats 400000 in
/-- Bonnice's beam lemma (corrected): `p 0 = z`, `p 1 = v1`, `p 2 = v3` counterclockwise; `p 3`,
`p 4` lie in the cone at `z` through `v1, v3`, strictly beyond the line `v1 v3`, and the line
through `p 3, p 4` leaves `z, v1, v3` strictly on one side. Then the five points are in convex
position. -/
theorem convexIndependent_beam (p : Fin 5 → Point) (hgp : IndexedGP p)
    (hinj : Function.Injective p) (hz : 0 < orient (p 0) (p 1) (p 2))
    (h3a : 0 < orient (p 0) (p 1) (p 3)) (h3b : 0 < orient (p 0) (p 3) (p 2))
    (h3c : orient (p 1) (p 2) (p 3) < 0)
    (h4a : 0 < orient (p 0) (p 1) (p 4)) (h4b : 0 < orient (p 0) (p 4) (p 2))
    (h4c : orient (p 1) (p 2) (p 4) < 0)
    (hl1 : 0 < orient (p 3) (p 4) (p 0) * orient (p 3) (p 4) (p 1))
    (hl2 : 0 < orient (p 3) (p 4) (p 0) * orient (p 3) (p 4) (p 2)) :
    ConvexIndependent ℝ
      (fun x : ((Finset.univ.image p : Finset Point) : Set Point) => (x : Point)) := by
  apply convexIndependent_of_separated
  intro v hv
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hv
  have h210 : orient (p 2) (p 1) (p 0) < 0 := by
    rw [orient_swap_left, ← orient_cyc]
    exact neg_lt_zero.2 hz
  have h213 : 0 < orient (p 2) (p 1) (p 3) := by
    rw [orient_swap_left]
    exact neg_pos.2 h3c
  have h214 : 0 < orient (p 2) (p 1) (p 4) := by
    rw [orient_swap_left]
    exact neg_pos.2 h4c
  have hc : ∀ l ∈ beamCore, LitHolds p l :=
    litHolds_cons (litHolds_pos p 0 1 2 hz) (litHolds_cons (litHolds_pos p 0 1 3 h3a)
      (litHolds_cons (litHolds_pos p 0 3 2 h3b) (litHolds_cons (litHolds_neg p 1 2 3 h3c)
        (litHolds_cons (litHolds_pos p 0 1 4 h4a) (litHolds_cons (litHolds_pos p 0 4 2 h4b)
          (litHolds_cons (litHolds_neg p 1 2 4 h4c) (litHolds_nil p)))))))
  rcases Ne.lt_or_gt (hgp 3 4 0 (by decide) (by decide) (by decide)) with hA | hA
  · -- `z, v1, v3` lie right of `p 3 → p 4`: the order is `z, v1, p 4, p 3, v3`.
    have h1 : orient (p 3) (p 4) (p 1) < 0 := (neg_iff_neg_of_mul_pos hl1).1 hA
    have h2 : orient (p 3) (p 4) (p 2) < 0 := (neg_iff_neg_of_mul_pos hl2).1 hA
    have hh : ∀ l ∈ beamLits false, LitHolds p l :=
      litHolds_append hc (litHolds_cons (litHolds_neg p 3 4 0 hA)
        (litHolds_cons (litHolds_neg p 3 4 1 h1) (litHolds_cons (litHolds_neg p 3 4 2 h2)
          (litHolds_nil p))))
    fin_cases k
    · exact separated_of_signs p hinj 2 1 0 3 4 (by decide) (by decide) h210 h213 h214
    · exact separated_of_signs p hinj 0 4 1 2 3 (by decide) (by decide)
        (sign_imp_neg (beamLits false) 0 4 1 (by decide +kernel) p hgp hh) h4b
        (sign_imp_pos (beamLits false) 0 4 3 (by decide +kernel) p hgp hh)
    · exact separated_of_signs p hinj 3 0 2 1 4 (by decide) (by decide)
        (sign_imp_neg (beamLits false) 3 0 2 (by decide +kernel) p hgp hh)
        (sign_imp_pos (beamLits false) 3 0 1 (by decide +kernel) p hgp hh)
        (sign_imp_pos (beamLits false) 3 0 4 (by decide +kernel) p hgp hh)
    · exact separated_of_signs p hinj 4 2 3 0 1 (by decide) (by decide)
        (sign_imp_neg (beamLits false) 4 2 3 (by decide +kernel) p hgp hh)
        (sign_imp_pos (beamLits false) 4 2 0 (by decide +kernel) p hgp hh)
        (sign_imp_pos (beamLits false) 4 2 1 (by decide +kernel) p hgp hh)
    · exact separated_of_signs p hinj 1 3 4 0 2 (by decide) (by decide)
        (sign_imp_neg (beamLits false) 1 3 4 (by decide +kernel) p hgp hh)
        (sign_imp_pos (beamLits false) 1 3 0 (by decide +kernel) p hgp hh)
        (sign_imp_pos (beamLits false) 1 3 2 (by decide +kernel) p hgp hh)
  · -- `z, v1, v3` lie left of `p 3 → p 4`: the order is `z, v1, p 3, p 4, v3`.
    have h1 : 0 < orient (p 3) (p 4) (p 1) := (pos_iff_pos_of_mul_pos hl1).1 hA
    have h2 : 0 < orient (p 3) (p 4) (p 2) := (pos_iff_pos_of_mul_pos hl2).1 hA
    have h034 : 0 < orient (p 0) (p 3) (p 4) := by
      rw [orient_cyc]
      exact hA
    have hh : ∀ l ∈ beamLits true, LitHolds p l :=
      litHolds_append hc (litHolds_cons (litHolds_pos p 3 4 0 hA)
        (litHolds_cons (litHolds_pos p 3 4 1 h1) (litHolds_cons (litHolds_pos p 3 4 2 h2)
          (litHolds_nil p))))
    fin_cases k
    · exact separated_of_signs p hinj 2 1 0 3 4 (by decide) (by decide) h210 h213 h214
    · exact separated_of_signs p hinj 0 3 1 2 4 (by decide) (by decide)
        (sign_imp_neg (beamLits true) 0 3 1 (by decide +kernel) p hgp hh) h3b h034
    · exact separated_of_signs p hinj 4 0 2 1 3 (by decide) (by decide)
        (sign_imp_neg (beamLits true) 4 0 2 (by decide +kernel) p hgp hh)
        (sign_imp_pos (beamLits true) 4 0 1 (by decide +kernel) p hgp hh)
        (sign_imp_pos (beamLits true) 4 0 3 (by decide +kernel) p hgp hh)
    · exact separated_of_signs p hinj 1 4 3 0 2 (by decide) (by decide)
        (sign_imp_neg (beamLits true) 1 4 3 (by decide +kernel) p hgp hh)
        (sign_imp_pos (beamLits true) 1 4 0 (by decide +kernel) p hgp hh)
        (sign_imp_pos (beamLits true) 1 4 2 (by decide +kernel) p hgp hh)
    · exact separated_of_signs p hinj 3 2 4 0 1 (by decide) (by decide)
        (sign_imp_neg (beamLits true) 3 2 4 (by decide +kernel) p hgp hh)
        (sign_imp_pos (beamLits true) 3 2 0 (by decide +kernel) p hgp hh)
        (sign_imp_pos (beamLits true) 3 2 1 (by decide +kernel) p hgp hh)

/-- Cone covering: `p 0 = v1, p 1 = v2, p 2 = v3` counterclockwise, `p 3 = z` strictly inside,
`p 4 = y` outside the closed triangle. Then `y` lies in one of the three cones at `z` through
consecutive vertices, strictly beyond the corresponding edge line. -/
theorem cone_cover (p : Fin 5 → Point) (hgp : IndexedGP p)
    (ht : 0 < orient (p 0) (p 1) (p 2))
    (hz1 : 0 < orient (p 0) (p 1) (p 3)) (hz2 : 0 < orient (p 1) (p 2) (p 3))
    (hz3 : 0 < orient (p 2) (p 0) (p 3))
    (hy : orient (p 0) (p 1) (p 4) < 0 ∨ orient (p 1) (p 2) (p 4) < 0 ∨
      orient (p 2) (p 0) (p 4) < 0) :
    (0 < orient (p 3) (p 0) (p 4) ∧ 0 < orient (p 3) (p 4) (p 1) ∧ orient (p 0) (p 1) (p 4) < 0) ∨
    (0 < orient (p 3) (p 1) (p 4) ∧ 0 < orient (p 3) (p 4) (p 2) ∧ orient (p 1) (p 2) (p 4) < 0) ∨
    (0 < orient (p 3) (p 2) (p 4) ∧ 0 < orient (p 3) (p 4) (p 0) ∧ orient (p 2) (p 0) (p 4) < 0) :=
    by
  have hh : ∀ l ∈ coneLits, LitHolds p l :=
    litHolds_cons (litHolds_pos p 0 1 2 ht) (litHolds_cons (litHolds_pos p 0 1 3 hz1)
      (litHolds_cons (litHolds_pos p 1 2 3 hz2) (litHolds_cons (litHolds_pos p 2 0 3 hz3)
        (litHolds_nil p))))
  have sw : ∀ i j : Fin 5, orient (p 3) (p i) (p j) < 0 → 0 < orient (p 3) (p j) (p i) := by
    intro i j h
    rw [orient_swap_right]
    exact neg_pos.2 h
  -- In each cone, `y` outside the triangle is beyond the corresponding edge.
  have c1 : 0 < orient (p 3) (p 0) (p 4) → orient (p 3) (p 1) (p 4) < 0 →
      orient (p 0) (p 1) (p 4) < 0 := by
    intro h0 h1
    rcases hy with h | h | h
    · exact h
    · exact sign_imp_neg (coneLits ++ [(3, 0, 4, true), (3, 1, 4, false), (1, 2, 4, false)]) 0 1 4
        (by decide +kernel) p hgp (litHolds_append hh (litHolds_cons (litHolds_pos p 3 0 4 h0)
          (litHolds_cons (litHolds_neg p 3 1 4 h1) (litHolds_cons (litHolds_neg p 1 2 4 h)
            (litHolds_nil p)))))
    · exact sign_imp_neg (coneLits ++ [(3, 0, 4, true), (3, 1, 4, false), (2, 0, 4, false)]) 0 1 4
        (by decide +kernel) p hgp (litHolds_append hh (litHolds_cons (litHolds_pos p 3 0 4 h0)
          (litHolds_cons (litHolds_neg p 3 1 4 h1) (litHolds_cons (litHolds_neg p 2 0 4 h)
            (litHolds_nil p)))))
  have c2 : 0 < orient (p 3) (p 1) (p 4) → orient (p 3) (p 2) (p 4) < 0 →
      orient (p 1) (p 2) (p 4) < 0 := by
    intro h1 h2
    rcases hy with h | h | h
    · exact sign_imp_neg (coneLits ++ [(3, 1, 4, true), (3, 2, 4, false), (0, 1, 4, false)]) 1 2 4
        (by decide +kernel) p hgp (litHolds_append hh (litHolds_cons (litHolds_pos p 3 1 4 h1)
          (litHolds_cons (litHolds_neg p 3 2 4 h2) (litHolds_cons (litHolds_neg p 0 1 4 h)
            (litHolds_nil p)))))
    · exact h
    · exact sign_imp_neg (coneLits ++ [(3, 1, 4, true), (3, 2, 4, false), (2, 0, 4, false)]) 1 2 4
        (by decide +kernel) p hgp (litHolds_append hh (litHolds_cons (litHolds_pos p 3 1 4 h1)
          (litHolds_cons (litHolds_neg p 3 2 4 h2) (litHolds_cons (litHolds_neg p 2 0 4 h)
            (litHolds_nil p)))))
  have c3 : 0 < orient (p 3) (p 2) (p 4) → orient (p 3) (p 0) (p 4) < 0 →
      orient (p 2) (p 0) (p 4) < 0 := by
    intro h2 h0
    rcases hy with h | h | h
    · exact sign_imp_neg (coneLits ++ [(3, 2, 4, true), (3, 0, 4, false), (0, 1, 4, false)]) 2 0 4
        (by decide +kernel) p hgp (litHolds_append hh (litHolds_cons (litHolds_pos p 3 2 4 h2)
          (litHolds_cons (litHolds_neg p 3 0 4 h0) (litHolds_cons (litHolds_neg p 0 1 4 h)
            (litHolds_nil p)))))
    · exact sign_imp_neg (coneLits ++ [(3, 2, 4, true), (3, 0, 4, false), (1, 2, 4, false)]) 2 0 4
        (by decide +kernel) p hgp (litHolds_append hh (litHolds_cons (litHolds_pos p 3 2 4 h2)
          (litHolds_cons (litHolds_neg p 3 0 4 h0) (litHolds_cons (litHolds_neg p 1 2 4 h)
            (litHolds_nil p)))))
    · exact h
  rcases Ne.lt_or_gt (hgp 3 0 4 (by decide) (by decide) (by decide)) with s0 | s0 <;>
    rcases Ne.lt_or_gt (hgp 3 1 4 (by decide) (by decide) (by decide)) with s1 | s1 <;>
    rcases Ne.lt_or_gt (hgp 3 2 4 (by decide) (by decide) (by decide)) with s2 | s2
  · exact absurd (sign_imp_pos (coneLits ++ [(3, 0, 4, false), (3, 1, 4, false)]) 3 2 4
      (by decide +kernel) p hgp (litHolds_append hh (litHolds_cons (litHolds_neg p 3 0 4 s0)
        (litHolds_cons (litHolds_neg p 3 1 4 s1) (litHolds_nil p))))) (not_lt.2 s2.le)
  · exact Or.inr (Or.inr ⟨s2, sw 0 4 s0, c3 s2 s0⟩)
  · exact Or.inr (Or.inl ⟨s1, sw 2 4 s2, c2 s1 s2⟩)
  · exact Or.inr (Or.inr ⟨s2, sw 0 4 s0, c3 s2 s0⟩)
  · exact Or.inl ⟨s0, sw 1 4 s1, c1 s0 s1⟩
  · exact Or.inl ⟨s0, sw 1 4 s1, c1 s0 s1⟩
  · exact Or.inr (Or.inl ⟨s1, sw 2 4 s2, c2 s1 s2⟩)
  · exact absurd (sign_imp_neg (coneLits ++ [(3, 0, 4, true), (3, 1, 4, true)]) 3 2 4
      (by decide +kernel) p hgp (litHolds_append hh (litHolds_cons (litHolds_pos p 3 0 4 s0)
        (litHolds_cons (litHolds_pos p 3 1 4 s1) (litHolds_nil p))))) (not_lt.2 s2.le)

/-- Strip pentagon: `p 0 = z1`, `p 1 = z2`, `p 2 = v2`, `p 3 = v3`, `p 4 = y`, where the line
`z1 → z2` has `v2, v3` strictly on its left, `z1, z2` are strictly left of `v2 → v3`, and `y`
lies strictly beyond `v2 v3`, right of `z1 → v3` and left of `z2 → v2`. Then
`{z1, z2, v2, y, v3}` is in convex position. -/
theorem convexIndependent_strip (p : Fin 5 → Point) (hgp : IndexedGP p)
    (hinj : Function.Injective p)
    (hv2 : 0 < orient (p 0) (p 1) (p 2)) (hv3 : 0 < orient (p 0) (p 1) (p 3))
    (hz1 : 0 < orient (p 2) (p 3) (p 0)) (hz2 : 0 < orient (p 2) (p 3) (p 1))
    (hy1 : orient (p 2) (p 3) (p 4) < 0) (hy2 : orient (p 0) (p 3) (p 4) < 0)
    (hy3 : 0 < orient (p 1) (p 2) (p 4)) :
    ConvexIndependent ℝ
      (fun x : ((Finset.univ.image p : Finset Point) : Set Point) => (x : Point)) := by
  apply convexIndependent_of_separated
  intro v hv
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hv
  have hh : ∀ l ∈ stripLits, LitHolds p l :=
    litHolds_cons (litHolds_pos p 0 1 2 hv2) (litHolds_cons (litHolds_pos p 0 1 3 hv3)
      (litHolds_cons (litHolds_pos p 2 3 0 hz1) (litHolds_cons (litHolds_pos p 2 3 1 hz2)
        (litHolds_cons (litHolds_neg p 2 3 4 hy1) (litHolds_cons (litHolds_neg p 0 3 4 hy2)
          (litHolds_cons (litHolds_pos p 1 2 4 hy3) (litHolds_nil p)))))))
  -- The convex order is `z1, z2, v2, y, v3`.
  fin_cases k
  · exact separated_of_signs p hinj 3 1 0 2 4 (by decide) (by decide)
      (sign_imp_neg stripLits 3 1 0 (by decide +kernel) p hgp hh)
      (sign_imp_pos stripLits 3 1 2 (by decide +kernel) p hgp hh)
      (sign_imp_pos stripLits 3 1 4 (by decide +kernel) p hgp hh)
  · exact separated_of_signs p hinj 0 2 1 3 4 (by decide) (by decide)
      (sign_imp_neg stripLits 0 2 1 (by decide +kernel) p hgp hh)
      (sign_imp_pos stripLits 0 2 3 (by decide +kernel) p hgp hh)
      (sign_imp_pos stripLits 0 2 4 (by decide +kernel) p hgp hh)
  · exact separated_of_signs p hinj 1 4 2 0 3 (by decide) (by decide)
      (sign_imp_neg stripLits 1 4 2 (by decide +kernel) p hgp hh)
      (sign_imp_pos stripLits 1 4 0 (by decide +kernel) p hgp hh)
      (sign_imp_pos stripLits 1 4 3 (by decide +kernel) p hgp hh)
  · exact separated_of_signs p hinj 4 0 3 1 2 (by decide) (by decide)
      (sign_imp_neg stripLits 4 0 3 (by decide +kernel) p hgp hh)
      (sign_imp_pos stripLits 4 0 1 (by decide +kernel) p hgp hh)
      (sign_imp_pos stripLits 4 0 2 (by decide +kernel) p hgp hh)
  · exact separated_of_signs p hinj 2 3 4 0 1 (by decide) (by decide) hy1 hz1 hz2

end Horton
