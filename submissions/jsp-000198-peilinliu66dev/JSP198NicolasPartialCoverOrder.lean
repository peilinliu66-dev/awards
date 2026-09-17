/-
Copyright (c) 2026 JSP198 formalization contributors.
Released under the MIT license. See LICENSE.

Finite order kernel for Nicolas Case I.A's PARTIAL cap cover.
This file proves an order implication, not an empty-hexagon theorem.
Its triangle inequalities are instantiated from actual geometry in
JSP198NicolasPartialCover.lean. No cover is an input.
-/
import Mathlib

namespace JSP198.Nicolas.PartialCover

/-- The two narrow triangles and the common wide triangle at a coherent join.
The narrow bounds are weak, because the two joining inner vertices may coincide.
The wide bounds are strict; this is essential at a common inner endpoint. -/
structure RankJoin (c d v a b : ℕ) : Prop where
  d_lo : min c (min v a) ≤ d
  d_hi : d ≤ max c (max v a)
  a_lo : min d (min v b) ≤ a
  a_hi : a ≤ max d (max v b)
  d_wide_lo : min c (min v b) < d
  d_wide_hi : d < max c (max v b)
  a_wide_lo : min c (min v b) < a
  a_wide_hi : a < max c (max v b)

/-- Finite, non-circular cap-cover implication. A positive sampled-chain edge
forces one of the two endpoint fans or one of the k right channels. -/
theorem partial_cover_order
    (k A B : ℕ) (r a b : ℕ → ℕ)
    (hra : ∀ j, j ≤ k → r j ≠ a j)
    (hab : ∀ j, j ≤ k → a j ≠ b j)
    (hbr : ∀ j, j < k → b j ≠ r (j + 1))
    (hfirst : min A (min (r 0) (b 0)) < a 0 ∧
      a 0 < max A (max (r 0) (b 0)))
    (hlast : min (a k) (min (r k) B) < b k ∧
      b k < max (a k) (max (r k) B))
    (hj : ∀ j, j < k → RankJoin (a j) (b j) (r (j + 1)) (a (j + 1)) (b (j + 1)))
    (hcap : A < a 0 ∨ (∃ j, j < k ∧ a j < a (j + 1)) ∨
      a k < b k ∨ b k < B) :
    (A < a 0 ∧ a 0 < r 0) ∨
      (∃ j, j < k ∧ r j < a j ∧ a j < b j ∧ b j < r (j + 1)) ∨
      (r k < b k ∧ b k < B) := by
  by_contra hn
  have hnoFirst : ¬ (A < a 0 ∧ a 0 < r 0) :=
    fun h => hn (Or.inl h)
  have hnoLast : ¬ (r k < b k ∧ b k < B) :=
    fun h => hn (Or.inr (Or.inr h))
  have hnoChannel : ∀ j, j < k →
      ¬ (r j < a j ∧ a j < b j ∧ b j < r (j + 1)) := by
    intro j hlt h
    exact hn (Or.inr (Or.inl ⟨j, hlt, h⟩))

  -- A visible inner edge whose own outer vertex is to its left propagates right.
  have forward : ∀ t j : ℕ, j + t = k →
      r j < a j → a j < b j → False := by
    intro t
    induction t with
    | zero =>
        intro j heq hrc hcd
        have he : j = k := by omega
        subst j
        have hbound := hlast.2
        have hbB : b k < B := by
          by_contra h
          have hm : max (a k) (max (r k) B) ≤ b k :=
            max_le hcd.le (max_le (hrc.trans hcd).le (le_of_not_gt h))
          exact (not_lt_of_ge hm) hbound
        exact hnoLast ⟨by omega, hbB⟩
    | succ t ih =>
        intro j heq hrc hcd
        have hjk : j < k := by omega
        have hnot := hnoChannel j hjk
        have hne := hbr j hjk
        have hvd : r (j + 1) < b j := by
          by_contra hbad
          have hright : b j < r (j + 1) := by omega
          exact hnot ⟨hrc, hcd, hright⟩
        have g := hj j hjk
        have hupper := g.d_hi
        have hda : b j ≤ a (j + 1) := by omega
        have hwide := g.a_wide_hi
        have habNext : a (j + 1) < b (j + 1) := by omega
        exact ih (j + 1) (by omega) (by omega) habNext

  -- The opposite state propagates left. This is a separate finite induction,
  -- not an appeal to a reflection symmetry of the matching assignment.
  have backward : ∀ j : ℕ, j ≤ k →
      a j < b j → a j < r j → False := by
    intro j
    induction j with
    | zero =>
        intro _ hcd hcr
        have hbound := hfirst.1
        have hAc : A < a 0 := by
          by_contra h
          have hm : a 0 ≤ min A (min (r 0) (b 0)) :=
            le_min (le_of_not_gt h) (le_min hcr.le hcd.le)
          exact (not_lt_of_ge hm) hbound
        exact hnoFirst ⟨hAc, hcr⟩
    | succ j ih =>
        intro hjk habNext harNext
        have hjlt : j < k := by omega
        have g := hj j hjlt
        have hlower := g.a_lo
        have hda : b j ≤ a (j + 1) := by omega
        have hwide := g.d_wide_lo
        have hcd : a j < b j := by omega
        have hdv : b j < r (j + 1) := by omega
        have hnot := hnoChannel j hjlt
        have hne := hra j (by omega)
        have hcr : a j < r j := by
          by_contra hbad
          have hrc : r j < a j := by omega
          exact hnot ⟨hrc, hcd, hdv⟩
        exact ih (by omega) hcd hcr

  have descending : ∀ j, j ≤ k → b j < a j := by
    intro j hjk
    have hne := hab j hjk
    by_contra hbad
    have hcd : a j < b j := by omega
    have hrcNe := hra j hjk
    rcases lt_or_gt_of_ne hrcNe with hrc | hcr
    · exact forward (k - j) j (by omega) hrc hcd
    · exact backward j hjk hcd hcr

  rcases hcap with hAc | ⟨j, hjk, hstep⟩ | hcd | hdB
  · have hd := descending 0 (Nat.zero_le k)
    have hupper := hfirst.2
    have hcr : a 0 < r 0 := by omega
    exact hnoFirst ⟨hAc, hcr⟩
  · have hd := descending j (by omega)
    have hdNext := descending (j + 1) (by omega)
    have g := hj j hjk
    have hlower := g.d_lo
    have hvd : r (j + 1) ≤ b j := by omega
    have hupper := g.a_wide_hi
    omega
  · have hd := descending k le_rfl
    omega
  · have hd := descending k le_rfl
    have hlower := hlast.1
    have hrd : r k < b k := by omega
    exact hnoLast ⟨hrd, hdB⟩

end JSP198.Nicolas.PartialCover

#print axioms JSP198.Nicolas.PartialCover.partial_cover_order
