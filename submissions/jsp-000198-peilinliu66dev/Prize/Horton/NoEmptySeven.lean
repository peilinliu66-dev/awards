/-
Copyright (c) 2026 JSP-000198 formalization contributors.
Released under the MIT license; see Prize/LICENSE_MIT.
Adapted from tester-lean/jsp-000198-horton-lean,
commit 313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0.
Mathematical construction: J. D. Horton.
Local port to Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/

import Prize.Horton.Visibility
import Prize.Horton.Indices

namespace Prize.Horton

open Prize.Geometry

theorem TriangleEmpty.even_upperVisible {depth : ℕ} {p : ℕ → Point} {S : Finset ℕ}
    (he : TriangleEmpty (depth + 1) p S) (hh : IsHorton (depth + 1) p)
    (hS : ∀ i ∈ S, i < 2 ^ (depth + 1))
    (hodd : (childIndices S 1).Nonempty) :
    ∀ a ∈ childIndices S 0, ∀ b ∈ childIndices S 0, a < b →
      UpperVisible (evenPoints p) a b := by
  obtain ⟨c, hc⟩ := hodd
  have hcS : 2 * c + 1 ∈ S := (mem_childIndices (by decide)).mp hc
  have hcB := childIndices_bound (by decide : 1 < 2) hS c hc
  intro a ha b hb hab t hat htb
  have haS : 2 * a ∈ S := by simpa using (mem_childIndices (by decide)).mp ha
  have hbS : 2 * b ∈ S := by simpa using (mem_childIndices (by decide)).mp hb
  have hbB := childIndices_bound (by decide : 0 < 2) hS b hb
  have htB : t < 2 ^ depth := lt_trans htb hbB
  change orient (p (2 * a)) (p (2 * b)) (p (2 * t)) ≤ 0
  by_contra hn
  have hp : 0 < orient (p (2 * a)) (p (2 * b)) (p (2 * t)) := lt_of_not_ge hn
  have hbc : 0 < orient (p (2 * b)) (p (2 * c + 1)) (p (2 * t)) := by
    rw [orient_cycle]
    exact hh.above htb hbB hcB
  have hca : 0 < orient (p (2 * c + 1)) (p (2 * a)) (p (2 * t)) := by
    rw [← orient_cycle]
    exact hh.above hat htB hcB
  have htri := mem_interior_triangle_of_orient_pos (hh.above hab hbB hcB) hp hbc hca
  have htB' : 2 * t < 2 ^ (depth + 1) := by rw [pow_succ]; omega
  have heq := he _ haS _ hbS _ hcS _ htB' htri
  omega

theorem TriangleEmpty.odd_lowerVisible {depth : ℕ} {p : ℕ → Point} {S : Finset ℕ}
    (he : TriangleEmpty (depth + 1) p S) (hh : IsHorton (depth + 1) p)
    (hS : ∀ i ∈ S, i < 2 ^ (depth + 1))
    (heven : (childIndices S 0).Nonempty) :
    ∀ a ∈ childIndices S 1, ∀ b ∈ childIndices S 1, a < b →
      LowerVisible (oddPoints p) a b := by
  obtain ⟨c, hc⟩ := heven
  have hcS : 2 * c ∈ S := by simpa using (mem_childIndices (by decide)).mp hc
  have hcB := childIndices_bound (by decide : 0 < 2) hS c hc
  intro a ha b hb hab t hat htb
  have haS : 2 * a + 1 ∈ S := (mem_childIndices (by decide)).mp ha
  have hbS : 2 * b + 1 ∈ S := (mem_childIndices (by decide)).mp hb
  have hbB := childIndices_bound (by decide : 1 < 2) hS b hb
  have htB : t < 2 ^ depth := lt_trans htb hbB
  change 0 ≤ orient (p (2 * a + 1)) (p (2 * b + 1)) (p (2 * t + 1))
  by_contra hn
  have hp : orient (p (2 * a + 1)) (p (2 * b + 1)) (p (2 * t + 1)) < 0 :=
    lt_of_not_ge hn
  have habc : 0 < orient (p (2 * b + 1)) (p (2 * a + 1)) (p (2 * c)) := by
    rw [orient_swap]
    exact neg_pos.mpr (hh.below hab hbB hcB)
  have habx : 0 < orient (p (2 * b + 1)) (p (2 * a + 1)) (p (2 * t + 1)) := by
    rw [orient_swap]
    exact neg_pos.mpr hp
  have hbcx : 0 < orient (p (2 * a + 1)) (p (2 * c)) (p (2 * t + 1)) := by
    rw [orient_swap_right]
    exact neg_pos.mpr (hh.below hat htB hcB)
  have hcax : 0 < orient (p (2 * c)) (p (2 * b + 1)) (p (2 * t + 1)) := by
    rw [orient_swap, orient_cycle]
    exact neg_pos.mpr (hh.below htb hbB hcB)
  have htri := mem_interior_triangle_of_orient_pos habc habx hbcx hcax
  have htB' : 2 * t + 1 < 2 ^ (depth + 1) := by rw [pow_succ]; omega
  have heq := he _ hbS _ haS _ hcS _ htB' htri
  omega

/-- Every selection with empty triangles in a Horton configuration has at most six indices. -/
theorem IsHorton.triangleEmpty_card_le_six {depth : ℕ} {p : ℕ → Point}
    (hh : IsHorton depth p) {S : Finset ℕ} (hS : ∀ i ∈ S, i < 2 ^ depth)
    (he : TriangleEmpty depth p S) : S.card ≤ 6 := by
  induction depth generalizing p S with
  | zero =>
    have hsub : S ⊆ {0} := by
      intro i hi
      have hb := hS i hi
      simp only [pow_zero] at hb
      have : i = 0 := by omega
      simp [this]
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  | succ depth ih =>
    have hcard := card_children S
    have h0 := childIndices_bound (by decide : 0 < 2) hS
    have h1 := childIndices_bound (by decide : 1 < 2) hS
    by_cases heven : (childIndices S 0).Nonempty
    · by_cases hodd : (childIndices S 1).Nonempty
      · have hc0 := hh.even.upperVisible_card_le_three h0
          (he.even_upperVisible hh hS hodd)
        have hc1 := hh.odd.lowerVisible_card_le_three h1
          (he.odd_lowerVisible hh hS heven)
        omega
      · have hc1 : (childIndices S 1).card = 0 := by
          simpa only [Finset.card_eq_zero, Finset.not_nonempty_iff_eq_empty] using hodd
        have hc0 := ih (p := evenPoints p) hh.even h0
          (by simpa only [TriangleEmpty, evenPoints, Nat.add_zero] using
            he.child (by decide : 0 < 2))
        omega
    · have hc0 : (childIndices S 0).card = 0 := by
        simpa only [Finset.card_eq_zero, Finset.not_nonempty_iff_eq_empty] using heven
      have hc1 := ih hh.odd h1 (he.child (by decide : 1 < 2))
      omega

/-- Geometric consequence of the recursive separation conditions. -/
theorem IsHorton.emptyConvex_card_le_six {depth : ℕ} {p : ℕ → Point}
    (hh : IsHorton depth p) (hinj : Set.InjOn p (Set.Iio (2 ^ depth)))
    {V : Finset Point}
    (he : EmptyConvex (p '' Set.Iio (2 ^ depth)) (V : Set Point)) : V.card ≤ 6 := by
  classical
  let S := (Finset.range (2 ^ depth)).filter fun i => p i ∈ V
  have hmem (i : ℕ) : i ∈ S ↔ i < 2 ^ depth ∧ p i ∈ V := by
    simp [S]
  have hbound : ∀ i ∈ S, i < 2 ^ depth := fun i hi => ((hmem i).mp hi).1
  have himage : S.image p = V := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ((hmem i).mp hi).2
    · intro hx
      obtain ⟨i, hi, rfl⟩ := he.subset hx
      exact ⟨i, (hmem i).mpr ⟨hi, hx⟩, rfl⟩
  have ht : TriangleEmpty depth p S := by
    intro a ha b hb c hc t ht htri
    have hp : p t ∈ ({p a, p b, p c} : Set Point) :=
      he.triangle_empty ((hmem a).mp ha).2 ((hmem b).mp hb).2 ((hmem c).mp hc).2
        (Set.mem_image_of_mem p ht) htri
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hp | hp | hp
    · exact Or.inl (hinj ht (hbound a ha) hp)
    · exact Or.inr (Or.inl (hinj ht (hbound b hb) hp))
    · exact Or.inr (Or.inr (hinj ht (hbound c hc) hp))
  have hcard : (S.image p).card = S.card := Finset.card_image_iff.mpr
    (fun i hi j hj hij => hinj (hbound i hi) (hbound j hj) hij)
  rw [← himage, hcard]
  exact hh.triangleEmpty_card_le_six hbound ht

end Prize.Horton
