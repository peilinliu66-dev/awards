/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Cover332.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Signs
import EmptyPentagon.Beam

noncomputable section
namespace Horton

/-- Covering lemma for Bonnice's `(3,3,2)` case. Triangle `v1 v2 v3` counterclockwise; `z1, z2`
strictly inside; the line `z1 → z2` has `v1` strictly on its right and `v2, v3` strictly on its
left. Then every point `y` in general position outside the closed triangle lies in the cone at
`z1` through `v3, v1` beyond the edge `v3 v1`, or in the cone at `z2` through `v1, v2` beyond
the edge `v1 v2`, or in the strip beyond `v2 v3` right of `z1 → v3` and left of `z2 → v2`. -/
theorem cover_332 (v1 v2 v3 z1 z2 y : Point)
    (hgp1 : IndexedGP ![v1, v2, v3, z1, y]) (hgp2 : IndexedGP ![v1, v2, v3, z2, y])
    (ht : 0 < orient v1 v2 v3)
    (hz1 : 0 < orient v1 v2 z1 ∧ 0 < orient v2 v3 z1 ∧ 0 < orient v3 v1 z1)
    (hz2 : 0 < orient v1 v2 z2 ∧ 0 < orient v2 v3 z2 ∧ 0 < orient v3 v1 z2)
    (hl1 : orient z1 z2 v1 < 0) (_hl2 : 0 < orient z1 z2 v2) (_hl3 : 0 < orient z1 z2 v3)
    (hy : orient v1 v2 y < 0 ∨ orient v2 v3 y < 0 ∨ orient v3 v1 y < 0) :
    (0 < orient z1 v3 y ∧ 0 < orient z1 y v1 ∧ orient v3 v1 y < 0) ∨
    (0 < orient z2 v1 y ∧ 0 < orient z2 y v2 ∧ orient v1 v2 y < 0) ∨
    (orient v2 v3 y < 0 ∧ orient z1 v3 y < 0 ∧ 0 < orient z2 v2 y) := by
  have hc1 : (0 < orient z1 v1 y ∧ 0 < orient z1 y v2 ∧ orient v1 v2 y < 0) ∨
      (0 < orient z1 v2 y ∧ 0 < orient z1 y v3 ∧ orient v2 v3 y < 0) ∨
      (0 < orient z1 v3 y ∧ 0 < orient z1 y v1 ∧ orient v3 v1 y < 0) :=
    cone_cover ![v1, v2, v3, z1, y] hgp1 ht hz1.1 hz1.2.1 hz1.2.2 hy
  have hc2 : (0 < orient z2 v1 y ∧ 0 < orient z2 y v2 ∧ orient v1 v2 y < 0) ∨
      (0 < orient z2 v2 y ∧ 0 < orient z2 y v3 ∧ orient v2 v3 y < 0) ∨
      (0 < orient z2 v3 y ∧ 0 < orient z2 y v1 ∧ orient v3 v1 y < 0) :=
    cone_cover ![v1, v2, v3, z2, y] hgp2 ht hz2.1 hz2.2.1 hz2.2.2 hy
  rcases hc1 with ⟨hA1, -, hA3⟩ | ⟨hB1, hB2, hB3⟩ | hC
  · -- `y` in the cone at `z1` through `v1, v2`, beyond `v1 v2`
    rcases hc2 with hA' | ⟨hB1', -, hB3'⟩ | ⟨-, hC2', -⟩
    · exact Or.inr (Or.inl hA')
    · -- corner at `v2`: `y` beyond `v1 v2` and `v2 v3`, so `y` is right of `z1 → v3`
      have h : orient z1 v3 y < 0 :=
        sign_imp_neg [(0, 1, 2, true), (0, 1, 3, true), (1, 2, 3, true), (2, 0, 3, true),
          (0, 1, 4, false), (1, 2, 4, false)] 3 2 4 (by decide +kernel) ![v1, v2, v3, z1, y] hgp1
          (litHolds_cons (litHolds_pos _ 0 1 2 ht) (litHolds_cons (litHolds_pos _ 0 1 3 hz1.1)
            (litHolds_cons (litHolds_pos _ 1 2 3 hz1.2.1)
              (litHolds_cons (litHolds_pos _ 2 0 3 hz1.2.2)
                (litHolds_cons (litHolds_neg _ 0 1 4 hA3)
                  (litHolds_cons (litHolds_neg _ 1 2 4 hB3') (litHolds_nil _)))))))
      exact Or.inr (Or.inr ⟨hB3', h, hB1'⟩)
    · -- corner at `v1`: impossible, by the rank-two Plücker relation at `v1`
      exfalso
      have h3 : orient v1 z1 z2 < 0 := by unfold orient at hl1 ⊢; linarith
      have h4 : orient v1 z1 y < 0 := by unfold orient at hA1 ⊢; linarith
      have h5 : 0 < orient v1 z2 y := by unfold orient at hC2' ⊢; linarith
      have m1 := mul_pos hz1.1 h5
      have m2 := mul_neg_of_pos_of_neg hz2.1 h4
      have m3 := mul_pos_of_neg_of_neg hA3 h3
      unfold orient at m1 m2 m3
      nlinarith
  · -- `y` in the cone at `z1` through `v2, v3`, beyond `v2 v3`
    have hz1y : orient z1 v3 y < 0 := by unfold orient at hB2 ⊢; linarith
    rcases hc2 with hA' | ⟨hB1', -, -⟩ | ⟨-, -, hC3'⟩
    · exact Or.inr (Or.inl hA')
    · exact Or.inr (Or.inr ⟨hB3, hz1y, hB1'⟩)
    · -- corner at `v3`: `y` beyond `v2 v3` and `v3 v1`, so `y` is left of `z2 → v2`
      have h : 0 < orient z2 v2 y :=
        sign_imp_pos [(0, 1, 2, true), (0, 1, 3, true), (1, 2, 3, true), (2, 0, 3, true),
          (1, 2, 4, false), (2, 0, 4, false)] 3 1 4 (by decide +kernel) ![v1, v2, v3, z2, y] hgp2
          (litHolds_cons (litHolds_pos _ 0 1 2 ht) (litHolds_cons (litHolds_pos _ 0 1 3 hz2.1)
            (litHolds_cons (litHolds_pos _ 1 2 3 hz2.2.1)
              (litHolds_cons (litHolds_pos _ 2 0 3 hz2.2.2)
                (litHolds_cons (litHolds_neg _ 1 2 4 hB3)
                  (litHolds_cons (litHolds_neg _ 2 0 4 hC3') (litHolds_nil _)))))))
      exact Or.inr (Or.inr ⟨hB3, hz1y, h⟩)
  · exact Or.inl hC

end Horton
