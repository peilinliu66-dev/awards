/-
Copyright (c) 2026 JSP-000198 formalization contributors.
Released under the MIT license; see Prize/LICENSE_MIT.
Adapted from tester-lean/jsp-000198-horton-lean,
commit 313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0.
Mathematical construction: J. D. Horton.
Local port to Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/

import Prize.Horton.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.Order.Archimedean.Basic

namespace Prize.Horton

open Prize.Geometry

theorem IsHorton.map {depth : ℕ} {p : ℕ → Point} (h : IsHorton depth p)
    (f : Point → Point) {r : ℝ} (hr : 0 < r)
    (hf : ∀ a b c, orient (f a) (f b) (f c) = r * orient a b c) :
    IsHorton depth (fun i => f (p i)) := by
  induction depth generalizing p with
  | zero => trivial
  | succ depth ih =>
    refine ⟨ih h.even, ih h.odd, ?_, ?_⟩
    · intro i j t hij hj ht
      rw [hf]
      exact mul_pos hr (h.above hij hj ht)
    · intro i j t hij hj ht
      rw [hf]
      exact mul_neg_of_pos_of_neg hr (h.below hij hj ht)

/-- Double the horizontal coordinate and translate. -/
def stretch (dx dy : ℝ) (a : Point) : Point := (2 * a.1 + dx, a.2 + dy)

theorem orient_stretch (dx dy : ℝ) (a b c : Point) :
    orient (stretch dx dy a) (stretch dx dy b) (stretch dx dy c) = 2 * orient a b c := by
  simp only [orient, stretch]
  ring

/-- Interleave two copies, shifting the odd-indexed copy vertically by `C`. -/
def liftPoints (p : ℕ → Point) (C : ℝ) (i : ℕ) : Point :=
  ((i : ℝ), (p (i / 2)).2 + (i % 2 : ℕ) * C)

@[simp] theorem liftPoints_x (p : ℕ → Point) (C : ℝ) (i : ℕ) :
    (liftPoints p C i).1 = i := rfl

@[simp] theorem liftPoints_even (p : ℕ → Point) (C : ℝ) (i : ℕ) :
    liftPoints p C (2 * i) = (((2 * i : ℕ) : ℝ), (p i).2) := by
  simp [liftPoints]

@[simp] theorem liftPoints_odd (p : ℕ → Point) (C : ℝ) (i : ℕ) :
    liftPoints p C (2 * i + 1) = (((2 * i + 1 : ℕ) : ℝ), (p i).2 + C) := by
  simp [liftPoints, Nat.add_div]

theorem liftPoints_even_stretch {p : ℕ → Point} (hx : ∀ i, (p i).1 = i) (C : ℝ) :
    evenPoints (liftPoints p C) = fun i => stretch 0 0 (p i) := by
  funext i
  simp [evenPoints, liftPoints_even, stretch, hx]

theorem liftPoints_odd_stretch {p : ℕ → Point} (hx : ∀ i, (p i).1 = i) (C : ℝ) :
    oddPoints (liftPoints p C) = fun i => stretch 1 C (p i) := by
  funext i
  simp [oddPoints, liftPoints_odd, stretch, hx]

theorem orient_lift_even_even_odd (p : ℕ → Point) (C : ℝ) (i j t : ℕ) :
    orient (liftPoints p C (2 * i)) (liftPoints p C (2 * j))
        (liftPoints p C (2 * t + 1)) =
      orient (liftPoints p 0 (2 * i)) (liftPoints p 0 (2 * j))
        (liftPoints p 0 (2 * t + 1)) + 2 * ((j : ℝ) - i) * C := by
  simp only [liftPoints_even, liftPoints_odd, orient, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem orient_lift_odd_odd_even (p : ℕ → Point) (C : ℝ) (i j t : ℕ) :
    orient (liftPoints p C (2 * i + 1)) (liftPoints p C (2 * j + 1))
        (liftPoints p C (2 * t)) =
      orient (liftPoints p 0 (2 * i + 1)) (liftPoints p 0 (2 * j + 1))
        (liftPoints p 0 (2 * t)) - 2 * ((j : ℝ) - i) * C := by
  simp only [liftPoints_even, liftPoints_odd, orient, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

/-- One sufficiently large integer vertical shift satisfies all separation
inequalities in the next finite configuration simultaneously. -/
theorem exists_lift_separation (depth : ℕ) (p : ℕ → Point) :
    ∃ C : ℕ,
      (∀ i j t : ℕ, i < j → j < 2 ^ depth → t < 2 ^ depth →
        0 < orient (liftPoints p C (2 * i)) (liftPoints p C (2 * j))
          (liftPoints p C (2 * t + 1))) ∧
      (∀ i j t : ℕ, i < j → j < 2 ^ depth → t < 2 ^ depth →
        orient (liftPoints p C (2 * i + 1)) (liftPoints p C (2 * j + 1))
          (liftPoints p C (2 * t)) < 0) := by
  let A (i j t : ℕ) := orient (liftPoints p 0 (2 * i))
    (liftPoints p 0 (2 * j)) (liftPoints p 0 (2 * t + 1))
  let B (i j t : ℕ) := orient (liftPoints p 0 (2 * i + 1))
    (liftPoints p 0 (2 * j + 1)) (liftPoints p 0 (2 * t))
  let f : Fin (2 ^ depth) × Fin (2 ^ depth) × Fin (2 ^ depth) → ℝ :=
    fun q => |A q.1 q.2.1 q.2.2| + |B q.1 q.2.1 q.2.2|
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  obtain ⟨C, hC⟩ := exists_nat_gt (max M 0)
  have hCM : M < (C : ℝ) := lt_of_le_of_lt (le_max_left _ _) hC
  have hC0 : 0 ≤ (C : ℝ) := Nat.cast_nonneg C
  have hbound (i j t : ℕ) (hij : i < j) (hj : j < 2 ^ depth) (ht : t < 2 ^ depth) :
      |A i j t| + |B i j t| < (C : ℝ) := by
    let q : Fin (2 ^ depth) × Fin (2 ^ depth) × Fin (2 ^ depth) :=
      (⟨i, lt_trans hij hj⟩, ⟨j, hj⟩, ⟨t, ht⟩)
    have hq : f q ≤ M := hM (Set.mem_range_self q)
    exact lt_of_le_of_lt hq hCM
  have hmul (i j : ℕ) (hij : i < j) : (C : ℝ) ≤ 2 * ((j : ℝ) - i) * C := by
    have hgap : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hij)
    have hcoef : 0 ≤ 2 * ((j : ℝ) - i) - 1 := by linarith
    nlinarith [mul_nonneg hcoef hC0]
  refine ⟨C, ?_, ?_⟩
  · intro i j t hij hj ht
    rw [orient_lift_even_even_odd]
    have hb := hbound i j t hij hj ht
    have hm := hmul i j hij
    have ha := neg_abs_le (A i j t)
    have hbn := abs_nonneg (B i j t)
    change 0 < A i j t + 2 * ((j : ℝ) - i) * C
    linarith
  · intro i j t hij hj ht
    rw [orient_lift_odd_odd_even]
    have hb := hbound i j t hij hj ht
    have hm := hmul i j hij
    have hbb := le_abs_self (B i j t)
    have han := abs_nonneg (A i j t)
    change B i j t - 2 * ((j : ℝ) - i) * C < 0
    linarith

/-- Horton configurations of every recursive depth exist with integer coordinates. -/
theorem exists_horton_integer (depth : ℕ) :
    ∃ p : ℕ → Point, IsHorton depth p ∧ (∀ i, (p i).1 = i) ∧
      (∀ i, ∃ z : ℤ, (p i).2 = z) := by
  induction depth with
  | zero =>
    exact ⟨fun i => ((i : ℝ), 0), trivial, fun _ => rfl, fun _ => ⟨0, by simp⟩⟩
  | succ depth ih =>
    obtain ⟨p, hh, hx, hy⟩ := ih
    obtain ⟨C, habove, hbelow⟩ := exists_lift_separation depth p
    refine ⟨liftPoints p C, ?_, fun _ => rfl, ?_⟩
    · refine ⟨?_, ?_, habove, hbelow⟩
      · rw [liftPoints_even_stretch hx]
        exact hh.map (stretch 0 0) (by norm_num) (orient_stretch 0 0)
      · rw [liftPoints_odd_stretch hx]
        exact hh.map (stretch 1 C) (by norm_num) (orient_stretch 1 C)
    · intro i
      obtain ⟨z, hz⟩ := hy (i / 2)
      refine ⟨z + Int.ofNat (i % 2) * Int.ofNat C, ?_⟩
      simp only [liftPoints, hz, Int.cast_add, Int.cast_mul,
        Int.ofNat_eq_natCast, Int.cast_natCast]

end Prize.Horton
