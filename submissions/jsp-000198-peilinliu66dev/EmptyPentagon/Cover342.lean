/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Cover342.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Signs
import EmptyPentagon.Quad
import EmptyPentagon.FourOuter

noncomputable section
namespace Horton

/-- Covering lemma for Bonnice's `(3,4,2)` case with a `2–2` split: quadrilateral `w1 w2 w3 w4`
counterclockwise, `z1, z2` strictly inside, the line `z1 → z2` has `w1, w2` strictly on its right
and `w3, w4` strictly on its left. Every point `y` in general position outside the closed
quadrilateral lies in the cone at `z2` through `w2, w3` beyond side `w2 w3`, or in the cone at
`z1` through `w4, w1` beyond side `w4 w1`, or in the strip beyond `w3 w4` (right of `z1 → w4`,
left of `z2 → w3`), or in the strip beyond `w1 w2` (right of `z2 → w2`, left of `z1 → w1`). -/
theorem cover_342 (w1 w2 w3 w4 z1 z2 y : Point)
    (hgp : GeneralPosition ({w1, w2, w3, w4, z1, z2, y} : Finset Point))
    (h1 : 0 < orient w1 w2 w3) (h2 : 0 < orient w2 w3 w4) (h3 : 0 < orient w3 w4 w1)
    (h4 : 0 < orient w4 w1 w2)
    (hz1 : 0 < orient w1 w2 z1 ∧ 0 < orient w2 w3 z1 ∧ 0 < orient w3 w4 z1 ∧ 0 < orient w4 w1 z1)
    (hz2 : 0 < orient w1 w2 z2 ∧ 0 < orient w2 w3 z2 ∧ 0 < orient w3 w4 z2 ∧ 0 < orient w4 w1 z2)
    (hl1 : orient z1 z2 w1 < 0) (hl2 : orient z1 z2 w2 < 0) (hl3 : 0 < orient z1 z2 w3)
    (hl4 : 0 < orient z1 z2 w4)
    (hy : orient w1 w2 y < 0 ∨ orient w2 w3 y < 0 ∨ orient w3 w4 y < 0 ∨ orient w4 w1 y < 0) :
    (0 < orient z2 w2 y ∧ 0 < orient z2 y w3 ∧ orient w2 w3 y < 0) ∨
    (0 < orient z1 w4 y ∧ 0 < orient z1 y w1 ∧ orient w4 w1 y < 0) ∨
    (orient w3 w4 y < 0 ∧ orient z1 w4 y < 0 ∧ 0 < orient z2 w3 y) ∨
    (orient w1 w2 y < 0 ∧ orient z2 w2 y < 0 ∧ 0 < orient z1 w1 y) := by
  obtain ⟨hz11, hz12, hz13, hz14⟩ := hz1
  obtain ⟨hz21, hz22, hz23, hz24⟩ := hz2
  -- pairwise distinctness of the seven points
  obtain ⟨h12, -, h23⟩ := ne_of_orient_ne_zero _ _ _ h1.ne'
  obtain ⟨h34, -, h41⟩ := ne_of_orient_ne_zero _ _ _ h3.ne'
  obtain ⟨-, h1z1, h2z1⟩ := ne_of_orient_ne_zero _ _ _ hz11.ne'
  obtain ⟨-, h3z1, h4z1⟩ := ne_of_orient_ne_zero _ _ _ hz13.ne'
  obtain ⟨-, h1z2, h2z2⟩ := ne_of_orient_ne_zero _ _ _ hz21.ne'
  obtain ⟨-, h3z2, h4z2⟩ := ne_of_orient_ne_zero _ _ _ hz23.ne'
  obtain ⟨hz1z2, -, -⟩ := ne_of_orient_ne_zero _ _ _ hl1.ne
  have hyne : w1 ≠ y ∧ w2 ≠ y ∧ w3 ≠ y ∧ w4 ≠ y ∧ z1 ≠ y ∧ z2 ≠ y := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> rcases hy with h | h | h | h <;>
      unfold orient at h h1 h2 h3 h4 hz11 hz12 hz13 hz14 hz21 hz22 hz23 hz24 <;> linarith
  obtain ⟨h1y, h2y, h3y, h4y, hz1y, hz2y⟩ := hyne
  -- indexed general position of the five-point subfamilies used below
  have gp5 : ∀ p : Fin 5 → Point,
      (∀ i, p i ∈ ({w1, w2, w3, w4, z1, z2, y} : Finset Point)) → Function.Injective p →
      IndexedGP p := indexedGP_of_injective _ hgp
  have hgp12 : IndexedGP ![w1, w2, z1, z2, y] :=
    gp5 _ (by intro i; fin_cases i <;> simp)
      (injective_vec5 _ _ _ _ _ h12 h1z1 h1z2 h1y h2z1 h2z2 h2y hz1z2 hz1y hz2y)
  have hgp34 : IndexedGP ![w3, w4, z1, z2, y] :=
    gp5 _ (by intro i; fin_cases i <;> simp)
      (injective_vec5 _ _ _ _ _ h34 h3z1 h3z2 h3y h4z1 h4z2 h4y hz1z2 hz1y hz2y)
  have hgp41 : IndexedGP ![w4, w1, z1, z2, y] :=
    gp5 _ (by intro i; fin_cases i <;> simp)
      (injective_vec5 _ _ _ _ _ h41 h4z1 h4z2 h4y h1z1 h1z2 h1y hz1z2 hz1y hz2y)
  have hgp23 : IndexedGP ![w2, w3, z1, z2, y] :=
    gp5 _ (by intro i; fin_cases i <;> simp)
      (injective_vec5 _ _ _ _ _ h23 h2z1 h2z2 h2y h3z1 h3z2 h3y hz1z2 hz1y hz2y)
  -- general position of the two six-point subfamilies feeding `cone_cover4`
  have hsub1 : ({w1, w2, w3, w4, z1, y} : Finset Point) ⊆ {w1, w2, w3, w4, z1, z2, y} :=
    Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
      (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))))
  have hsub2 : ({w1, w2, w3, w4, z2, y} : Finset Point) ⊆ {w1, w2, w3, w4, z1, z2, y} :=
    Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
      (Finset.insert_subset_insert _ (Finset.subset_insert _ _))))
  have hgp1 : GeneralPosition ({w1, w2, w3, w4, z1, y} : Finset Point) :=
    fun a ha b hb c hc => hgp a (hsub1 ha) b (hsub1 hb) c (hsub1 hc)
  have hgp2 : GeneralPosition ({w1, w2, w3, w4, z2, y} : Finset Point) :=
    fun a ha b hb c hc => hgp a (hsub2 ha) b (hsub2 hb) c (hsub2 hc)
  /- Reusable five-point facts.  `R1`, `R2`: the cone through `w1, w2` at `z1` (resp. `z2`) lies
  strictly right of the line `z1 → z2`; `L1`, `L2`: the cone through `w3, w4` lies strictly left.
  `A1`: right of the line and left of `z1 → w2` gives left of `z1 → w1`; `A2`: left of the line
  and left of `z2 → w4` gives left of `z2 → w3`. -/
  have R1 : 0 < orient z1 w1 y → 0 < orient z1 y w2 → orient z1 z2 y < 0 := fun a b =>
    sign_imp_neg [(2, 3, 0, false), (2, 3, 1, false), (0, 1, 2, true), (2, 0, 4, true),
      (2, 4, 1, true)] 2 3 4 (by decide +kernel) ![w1, w2, z1, z2, y] hgp12
      (litHolds_cons (litHolds_neg _ 2 3 0 hl1) (litHolds_cons (litHolds_neg _ 2 3 1 hl2)
        (litHolds_cons (litHolds_pos _ 0 1 2 hz11) (litHolds_cons (litHolds_pos _ 2 0 4 a)
          (litHolds_cons (litHolds_pos _ 2 4 1 b) (litHolds_nil _))))))
  have R2 : 0 < orient z2 w1 y → 0 < orient z2 y w2 → orient z1 z2 y < 0 := fun a b =>
    sign_imp_neg [(2, 3, 0, false), (2, 3, 1, false), (0, 1, 3, true), (3, 0, 4, true),
      (3, 4, 1, true)] 2 3 4 (by decide +kernel) ![w1, w2, z1, z2, y] hgp12
      (litHolds_cons (litHolds_neg _ 2 3 0 hl1) (litHolds_cons (litHolds_neg _ 2 3 1 hl2)
        (litHolds_cons (litHolds_pos _ 0 1 3 hz21) (litHolds_cons (litHolds_pos _ 3 0 4 a)
          (litHolds_cons (litHolds_pos _ 3 4 1 b) (litHolds_nil _))))))
  have L1 : 0 < orient z1 w3 y → 0 < orient z1 y w4 → 0 < orient z1 z2 y := fun a b =>
    sign_imp_pos [(2, 3, 0, true), (2, 3, 1, true), (0, 1, 2, true), (2, 0, 4, true),
      (2, 4, 1, true)] 2 3 4 (by decide +kernel) ![w3, w4, z1, z2, y] hgp34
      (litHolds_cons (litHolds_pos _ 2 3 0 hl3) (litHolds_cons (litHolds_pos _ 2 3 1 hl4)
        (litHolds_cons (litHolds_pos _ 0 1 2 hz13) (litHolds_cons (litHolds_pos _ 2 0 4 a)
          (litHolds_cons (litHolds_pos _ 2 4 1 b) (litHolds_nil _))))))
  have L2 : 0 < orient z2 w3 y → 0 < orient z2 y w4 → 0 < orient z1 z2 y := fun a b =>
    sign_imp_pos [(2, 3, 0, true), (2, 3, 1, true), (0, 1, 3, true), (3, 0, 4, true),
      (3, 4, 1, true)] 2 3 4 (by decide +kernel) ![w3, w4, z1, z2, y] hgp34
      (litHolds_cons (litHolds_pos _ 2 3 0 hl3) (litHolds_cons (litHolds_pos _ 2 3 1 hl4)
        (litHolds_cons (litHolds_pos _ 0 1 3 hz23) (litHolds_cons (litHolds_pos _ 3 0 4 a)
          (litHolds_cons (litHolds_pos _ 3 4 1 b) (litHolds_nil _))))))
  have A1 : orient z1 z2 y < 0 → 0 < orient z1 w2 y → 0 < orient z1 w1 y := fun a b =>
    sign_imp_pos [(2, 3, 0, false), (2, 3, 1, false), (2, 3, 4, false), (0, 1, 2, true),
      (2, 1, 4, true)] 2 0 4 (by decide +kernel) ![w1, w2, z1, z2, y] hgp12
      (litHolds_cons (litHolds_neg _ 2 3 0 hl1) (litHolds_cons (litHolds_neg _ 2 3 1 hl2)
        (litHolds_cons (litHolds_neg _ 2 3 4 a) (litHolds_cons (litHolds_pos _ 0 1 2 hz11)
          (litHolds_cons (litHolds_pos _ 2 1 4 b) (litHolds_nil _))))))
  have A2 : 0 < orient z1 z2 y → 0 < orient z2 w4 y → 0 < orient z2 w3 y := fun a b =>
    sign_imp_pos [(2, 3, 0, true), (2, 3, 1, true), (2, 3, 4, true), (0, 1, 3, true),
      (3, 1, 4, true)] 3 0 4 (by decide +kernel) ![w3, w4, z1, z2, y] hgp34
      (litHolds_cons (litHolds_pos _ 2 3 0 hl3) (litHolds_cons (litHolds_pos _ 2 3 1 hl4)
        (litHolds_cons (litHolds_pos _ 2 3 4 a) (litHolds_cons (litHolds_pos _ 0 1 3 hz23)
          (litHolds_cons (litHolds_pos _ 3 1 4 b) (litHolds_nil _))))))
  have hne : orient z1 z2 y ≠ 0 := hgp z1 (by simp) z2 (by simp) y (by simp) hz1z2 hz1y hz2y
  -- the two cone covers
  have hc1 := cone_cover4 w1 w2 w3 w4 z1 y hgp1 h1 h2 h3 h4 ⟨hz11, hz12, hz13, hz14⟩ hy
  have hc2 := cone_cover4 w1 w2 w3 w4 z2 y hgp2 h1 h2 h3 h4 ⟨hz21, hz22, hz23, hz24⟩ hy
  rcases hc1 with ⟨hA1, hA2, hA3⟩ | ⟨hA1, hA2, hA3⟩ | ⟨hA1, hA2, hA3⟩ | hD2
  · -- `y` in the cone at `z1` through `w1, w2`, beyond `w1 w2`
    rcases hc2 with ⟨-, hB2, -⟩ | hD1 | ⟨hB1, hB2, -⟩ | ⟨-, hB2, -⟩
    · exact Or.inr (Or.inr (Or.inr ⟨hA3, by linarith [orient_swap_right z2 w2 y], hA1⟩))
    · exact Or.inl hD1
    · exact absurd (R1 hA1 hA2) (not_lt.2 (L2 hB1 hB2).le)
    · -- corner at `w1`: refuted by the angular order around `w1`
      exfalso
      have h : 0 < orient w1 w2 y :=
        sign_imp_pos [(0, 1, 2, true), (0, 1, 3, true), (0, 1, 4, false), (2, 3, 0, false),
          (2, 0, 4, true), (3, 4, 0, true)] 0 1 4 (by decide +kernel) ![w1, w2, z1, z2, y] hgp12
          (litHolds_cons (litHolds_pos _ 0 1 2 hz11) (litHolds_cons (litHolds_pos _ 0 1 3 hz21)
            (litHolds_cons (litHolds_neg _ 0 1 4 hA3) (litHolds_cons (litHolds_neg _ 2 3 0 hl1)
              (litHolds_cons (litHolds_pos _ 2 0 4 hA1)
                (litHolds_cons (litHolds_pos _ 3 4 0 hB2) (litHolds_nil _)))))))
      exact absurd h (not_lt.2 hA3.le)
  · -- `y` in the cone at `z1` through `w2, w3`, beyond `w2 w3`
    rcases hc2 with ⟨hB1, hB2, hB3⟩ | hD1 | ⟨hB1, -, hB3⟩ | ⟨hB1, hB2, hB3⟩
    · exact Or.inr (Or.inr (Or.inr
        ⟨hB3, by linarith [orient_swap_right z2 w2 y], A1 (R2 hB1 hB2) hA1⟩))
    · exact Or.inl hD1
    · -- corner at `w3`: refuted by the angular order around `w3`
      exfalso
      have h : 0 < orient w3 w4 y :=
        sign_imp_pos [(0, 1, 2, true), (0, 1, 3, true), (0, 1, 4, false), (2, 3, 0, true),
          (3, 0, 4, true), (2, 4, 0, true)] 0 1 4 (by decide +kernel) ![w3, w4, z1, z2, y] hgp34
          (litHolds_cons (litHolds_pos _ 0 1 2 hz13) (litHolds_cons (litHolds_pos _ 0 1 3 hz23)
            (litHolds_cons (litHolds_neg _ 0 1 4 hB3) (litHolds_cons (litHolds_pos _ 2 3 0 hl3)
              (litHolds_cons (litHolds_pos _ 3 0 4 hB1)
                (litHolds_cons (litHolds_pos _ 2 4 0 hA2) (litHolds_nil _)))))))
      exact absurd h (not_lt.2 hB3.le)
    · -- opposite sides `w2 w3` and `w4 w1`: `y` would lie in a triangle `z1 z2 w1` or
      -- `z1 z2 w3` inside the quadrilateral
      exfalso
      rcases hne.lt_or_gt with hneg | hpos
      · have h : 0 < orient w4 w1 y :=
          sign_imp_pos [(2, 3, 1, false), (2, 3, 4, false), (2, 1, 4, true), (3, 4, 1, true),
            (0, 1, 2, true), (0, 1, 3, true)] 0 1 4 (by decide +kernel) ![w4, w1, z1, z2, y] hgp41
            (litHolds_cons (litHolds_neg _ 2 3 1 hl1) (litHolds_cons (litHolds_neg _ 2 3 4 hneg)
              (litHolds_cons (litHolds_pos _ 2 1 4 (A1 hneg hA1))
                (litHolds_cons (litHolds_pos _ 3 4 1 hB2)
                  (litHolds_cons (litHolds_pos _ 0 1 2 hz14)
                    (litHolds_cons (litHolds_pos _ 0 1 3 hz24) (litHolds_nil _)))))))
        exact absurd h (not_lt.2 hB3.le)
      · have h : 0 < orient w2 w3 y :=
          sign_imp_pos [(2, 3, 1, true), (2, 3, 4, true), (3, 1, 4, true), (2, 4, 1, true),
            (0, 1, 2, true), (0, 1, 3, true)] 0 1 4 (by decide +kernel) ![w2, w3, z1, z2, y] hgp23
            (litHolds_cons (litHolds_pos _ 2 3 1 hl3) (litHolds_cons (litHolds_pos _ 2 3 4 hpos)
              (litHolds_cons (litHolds_pos _ 3 1 4 (A2 hpos hB1))
                (litHolds_cons (litHolds_pos _ 2 4 1 hA2)
                  (litHolds_cons (litHolds_pos _ 0 1 2 hz12)
                    (litHolds_cons (litHolds_pos _ 0 1 3 hz22) (litHolds_nil _)))))))
        exact absurd h (not_lt.2 hA3.le)
  · -- `y` in the cone at `z1` through `w3, w4`, beyond `w3 w4`
    have hz1y' : orient z1 w4 y < 0 := by linarith [orient_swap_right z1 w4 y]
    rcases hc2 with ⟨hB1, hB2, -⟩ | hD1 | ⟨hB1, -, -⟩ | ⟨hB1, -, -⟩
    · exact absurd (R2 hB1 hB2) (not_lt.2 (L1 hA1 hA2).le)
    · exact Or.inl hD1
    · exact Or.inr (Or.inr (Or.inl ⟨hA3, hz1y', hB1⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hA3, hz1y', A2 (L1 hA1 hA2) hB1⟩))
  · exact Or.inr (Or.inl hD2)

end Horton
