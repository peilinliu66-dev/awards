/-
Copyright (c) 2026 JSP-000198 formalization contributors.
Released under the MIT license; see Prize/LICENSE_MIT.
Adapted from tester-lean/jsp-000198-horton-lean,
commit 313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0.
Mathematical construction: J. D. Horton.
Local port to Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/

import Prize.Geometry.EmptyPolygon

/-!
# The recursive separation conditions of a Horton configuration

The function is considered only on indices below `2 ^ depth`. The two children
are its even and odd subsequences. The conditions use actual real-plane signed
areas; existence and the empty-polygon bound are separate proof obligations.
-/

namespace Prize.Horton

open Prize.Geometry

def evenPoints (p : ℕ → Point) : ℕ → Point := fun i => p (2 * i)
def oddPoints (p : ℕ → Point) : ℕ → Point := fun i => p (2 * i + 1)

def IsHorton : ℕ → (ℕ → Point) → Prop
  | 0, _ => True
  | depth + 1, p =>
      IsHorton depth (evenPoints p) ∧
      IsHorton depth (oddPoints p) ∧
      (∀ i j t : ℕ, i < j → j < 2 ^ depth → t < 2 ^ depth →
        0 < orient (p (2 * i)) (p (2 * j)) (p (2 * t + 1))) ∧
      (∀ i j t : ℕ, i < j → j < 2 ^ depth → t < 2 ^ depth →
        orient (p (2 * i + 1)) (p (2 * j + 1)) (p (2 * t)) < 0)

theorem IsHorton.even {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) : IsHorton depth (evenPoints p) := h.1

theorem IsHorton.odd {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) : IsHorton depth (oddPoints p) := h.2.1

theorem IsHorton.above {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {i j t : ℕ}
    (hij : i < j) (hj : j < 2 ^ depth) (ht : t < 2 ^ depth) :
    0 < orient (p (2 * i)) (p (2 * j)) (p (2 * t + 1)) :=
  h.2.2.1 i j t hij hj ht

theorem IsHorton.below {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {i j t : ℕ}
    (hij : i < j) (hj : j < 2 ^ depth) (ht : t < 2 ^ depth) :
    orient (p (2 * i + 1)) (p (2 * j + 1)) (p (2 * t)) < 0 :=
  h.2.2.2 i j t hij hj ht

/-- The segment is visible from above: no intermediate-index point is above it. -/
def UpperVisible (p : ℕ → Point) (i j : ℕ) : Prop :=
  ∀ t : ℕ, i < t → t < j → orient (p i) (p j) (p t) ≤ 0

/-- The corresponding visibility condition from below. -/
def LowerVisible (p : ℕ → Point) (i j : ℕ) : Prop :=
  ∀ t : ℕ, i < t → t < j → 0 ≤ orient (p i) (p j) (p t)

theorem upperVisible_odd {p : ℕ → Point} {i j : ℕ}
    (h : UpperVisible p (2 * i + 1) (2 * j + 1)) :
    UpperVisible (oddPoints p) i j := by
  intro t hit htj
  exact h (2 * t + 1) (by omega) (by omega)

theorem lowerVisible_even {p : ℕ → Point} {i j : ℕ}
    (h : LowerVisible p (2 * i) (2 * j)) :
    LowerVisible (evenPoints p) i j := by
  intro t hit htj
  exact h (2 * t) (by omega) (by omega)

theorem IsHorton.not_upperVisible_even {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {i j : ℕ}
    (hij : i < j) (hj : j < 2 ^ depth) :
    ¬UpperVisible p (2 * i) (2 * j) := by
  intro hv
  have hp := h.above hij hj (lt_trans hij hj)
  have hn := hv (2 * i + 1) (by omega) (by omega)
  exact (not_lt_of_ge hn) hp

theorem IsHorton.not_lowerVisible_odd {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {i j : ℕ}
    (hij : i < j) (hj : j < 2 ^ depth) :
    ¬LowerVisible p (2 * i + 1) (2 * j + 1) := by
  intro hv
  have hp := h.below hij hj hj
  have hn := hv (2 * j) (by omega) (by omega)
  exact (not_lt_of_ge hn) hp

end Prize.Horton
