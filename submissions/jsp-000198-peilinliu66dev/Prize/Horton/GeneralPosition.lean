/-
Copyright (c) 2026 JSP-000198 formalization contributors.
Released under the MIT license; see Prize/LICENSE_MIT.
Adapted from tester-lean/jsp-000198-horton-lean,
commit 313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0.
Mathematical construction: J. D. Horton.
Local port to Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/

import Prize.Horton.Basic

namespace Prize.Horton

open Prize.Geometry

theorem IsHorton.above_indices {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {a b t : ℕ}
    (hab : a < b) (hb : b < 2 ^ (depth + 1)) (ht : t < 2 ^ (depth + 1))
    (ha0 : a % 2 = 0) (hb0 : b % 2 = 0) (ht1 : t % 2 = 1) :
    0 < orient (p a) (p b) (p t) := by
  have ha : a = 2 * (a / 2) := by omega
  have hb' : b = 2 * (b / 2) := by omega
  have ht' : t = 2 * (t / 2) + 1 := by omega
  rw [pow_succ] at hb ht
  rw [ha, hb', ht']
  exact h.above (by omega) (by omega) (by omega)

theorem IsHorton.below_indices {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {a b t : ℕ}
    (hab : a < b) (hb : b < 2 ^ (depth + 1)) (ht : t < 2 ^ (depth + 1))
    (ha1 : a % 2 = 1) (hb1 : b % 2 = 1) (ht0 : t % 2 = 0) :
    orient (p a) (p b) (p t) < 0 := by
  have ha : a = 2 * (a / 2) + 1 := by omega
  have hb' : b = 2 * (b / 2) + 1 := by omega
  have ht' : t = 2 * (t / 2) := by omega
  rw [pow_succ] at hb ht
  rw [ha, hb', ht']
  exact h.below (by omega) (by omega) (by omega)

theorem IsHorton.orient_ne_zero_sorted {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton depth p) {a b c : ℕ}
    (hab : a < b) (hbc : b < c) (hc : c < 2 ^ depth) :
    orient (p a) (p b) (p c) ≠ 0 := by
  induction depth generalizing p a b c with
  | zero => simp only [pow_zero] at hc; omega
  | succ depth ih =>
    have haB : a < 2 ^ (depth + 1) := by omega
    have hbB : b < 2 ^ (depth + 1) := by omega
    have haP : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hbP : b % 2 = 0 ∨ b % 2 = 1 := by omega
    have hcP : c % 2 = 0 ∨ c % 2 = 1 := by omega
    rcases haP with ha0 | ha1 <;> rcases hbP with hb0 | hb1 <;>
      rcases hcP with hc0 | hc1
    · have ha : a = 2 * (a / 2) := by omega
      have hb : b = 2 * (b / 2) := by omega
      have hc' : c = 2 * (c / 2) := by omega
      rw [pow_succ] at hc
      have hn := ih h.even (a := a / 2) (b := b / 2) (c := c / 2)
        (by omega) (by omega) (by omega)
      simpa only [evenPoints, ← ha, ← hb, ← hc'] using hn
    · exact ne_of_gt (h.above_indices hab hbB hc ha0 hb0 hc1)
    · intro hz
      have hp := h.above_indices (a := a) (b := c) (t := b)
        (by omega) hc hbB ha0 hc0 hb1
      rw [orient_swap_right, hz] at hp
      norm_num at hp
    · rw [← orient_cycle]
      exact ne_of_lt (h.below_indices hbc hc haB hb1 hc1 ha0)
    · rw [← orient_cycle]
      exact ne_of_gt (h.above_indices hbc hc haB hb0 hc0 ha1)
    · intro hz
      have hp := h.below_indices (a := a) (b := c) (t := b)
        (by omega) hc hbB ha1 hc1 hb0
      rw [orient_swap_right, hz] at hp
      norm_num at hp
    · exact ne_of_lt (h.below_indices hab hbB hc ha1 hb1 hc0)
    · have ha : a = 2 * (a / 2) + 1 := by omega
      have hb : b = 2 * (b / 2) + 1 := by omega
      have hc' : c = 2 * (c / 2) + 1 := by omega
      rw [pow_succ] at hc
      have hn := ih h.odd (a := a / 2) (b := b / 2) (c := c / 2)
        (by omega) (by omega) (by omega)
      simpa only [oddPoints, ← ha, ← hb, ← hc'] using hn

theorem IsHorton.orient_ne_zero_of_lt {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton depth p) {a b c : ℕ}
    (_ha : a < 2 ^ depth) (hb : b < 2 ^ depth) (hc : c < 2 ^ depth)
    (hab : a < b) (hac : a ≠ c) (hbc : b ≠ c) :
    orient (p a) (p b) (p c) ≠ 0 := by
  by_cases hbc' : b < c
  · exact h.orient_ne_zero_sorted hab hbc' hc
  · have hcb : c < b := by omega
    by_cases hac' : a < c
    · intro hz
      have hn := h.orient_ne_zero_sorted hac' hcb hb
      rw [orient_swap_right, hz] at hn
      exact hn (neg_zero)
    · have hca : c < a := by omega
      rw [orient_cycle (p c) (p a) (p b)]
      exact h.orient_ne_zero_sorted hca hab hb

theorem IsHorton.orient_ne_zero {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton depth p) {a b c : ℕ}
    (ha : a < 2 ^ depth) (hb : b < 2 ^ depth) (hc : c < 2 ^ depth)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orient (p a) (p b) (p c) ≠ 0 := by
  rcases lt_or_gt_of_ne hab with hab' | hba'
  · exact h.orient_ne_zero_of_lt ha hb hc hab' hac hbc
  · intro hz
    have hn := h.orient_ne_zero_of_lt hb ha hc hba' hbc hac
    rw [orient_swap, hz] at hn
    exact hn (neg_zero)

/-- The separation conditions imply the usual no-three-collinear property. -/
theorem IsHorton.generalPosition {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton depth p) : GeneralPosition (p '' Set.Iio (2 ^ depth)) := by
  rintro a ⟨i, hi, rfl⟩ b ⟨j, hj, rfl⟩ c ⟨k, hk, rfl⟩ hij hik hjk
  apply not_collinear_of_orient_ne_zero
  exact h.orient_ne_zero hi hj hk (fun h => hij (congrArg p h))
    (fun h => hik (congrArg p h)) (fun h => hjk (congrArg p h))

end Prize.Horton
