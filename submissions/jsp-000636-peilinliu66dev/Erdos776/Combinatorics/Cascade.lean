import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# Numerical binomial cascades

This file defines the numerical objects used in the cascade formulation of
Kruskal--Katona.  The colex/set-family semantics are added in
`CascadeFamily.lean`; keeping the arithmetic representation separate makes it
possible to test the indexing conventions before introducing finite sets.
-/

namespace Erdos776.KruskalKatona

/--
The value of digits `aₖ, aₖ₋₁, ...` placed at consecutive lower indices
`k, k-1, ...`.
-/
def cascadeValue : ℕ → List ℕ → ℕ
  | _, [] => 0
  | k, a :: digits => a.choose k + cascadeValue (k - 1) digits

@[simp] theorem cascadeValue_nil (k : ℕ) : cascadeValue k [] = 0 := rfl

@[simp] theorem cascadeValue_cons (k a : ℕ) (digits : List ℕ) :
    cascadeValue k (a :: digits) = a.choose k + cascadeValue (k - 1) digits := rfl

theorem cascadeValue_append (k : ℕ) (xs ys : List ℕ) :
    cascadeValue k (xs ++ ys) =
      cascadeValue k xs + cascadeValue (k - xs.length) ys := by
  induction xs generalizing k with
  | nil => simp
  | cons a xs ih =>
      simp only [List.cons_append, cascadeValue_cons, List.length_cons]
      rw [ih]
      rw [show k - (xs.length + 1) = k - 1 - xs.length by omega]
      omega

/-- The value obtained by lowering every lower binomial index by one. -/
def cascadeShadowValue (k : ℕ) (digits : List ℕ) : ℕ :=
  cascadeValue (k - 1) digits

@[simp] theorem cascadeShadowValue_nil (k : ℕ) :
    cascadeShadowValue k [] = 0 := rfl

@[simp] theorem cascadeShadowValue_cons (k a : ℕ) (digits : List ℕ) :
    cascadeShadowValue k (a :: digits) =
      a.choose (k - 1) + cascadeValue (k - 2) digits := by
  simp only [cascadeShadowValue, cascadeValue_cons]
  rw [show k - 1 - 1 = k - 2 by omega]

theorem cascadeShadowValue_append (k : ℕ) (xs ys : List ℕ) :
    cascadeShadowValue k (xs ++ ys) =
      cascadeShadowValue k xs +
        cascadeValue (k - 1 - xs.length) ys := by
  unfold cascadeShadowValue
  rw [cascadeValue_append]

/--
`digits` is a canonical `k`-cascade: every digit is at least its lower index,
the lower indices are consecutive and positive, and the upper digits strictly
decrease.  Consecutive lower indices are built into the recursion.
-/
def IsCanonical : ℕ → List ℕ → Prop
  | _, [] => True
  | 0, _ :: _ => False
  | k + 1, a :: digits =>
      k + 1 ≤ a ∧ (∀ b ∈ digits, b < a) ∧ IsCanonical k digits

@[simp] theorem isCanonical_nil (k : ℕ) : IsCanonical k [] := by
  cases k <;> trivial

@[simp] theorem isCanonical_zero_cons (a : ℕ) (digits : List ℕ) :
    ¬ IsCanonical 0 (a :: digits) := by simp [IsCanonical]

@[simp] theorem isCanonical_succ_cons (k a : ℕ) (digits : List ℕ) :
    IsCanonical (k + 1) (a :: digits) ↔
      k + 1 ≤ a ∧ (∀ b ∈ digits, b < a) ∧ IsCanonical k digits := by
  rfl

theorem isCanonical_cons_of_pos {k a : ℕ} {digits : List ℕ} (hk : 0 < k) :
    IsCanonical k (a :: digits) ↔
      k ≤ a ∧ (∀ b ∈ digits, b < a) ∧ IsCanonical (k - 1) digits := by
  cases k with
  | zero => omega
  | succ k => rfl

theorem IsCanonical.length_le {k : ℕ} {digits : List ℕ}
    (h : IsCanonical k digits) : digits.length ≤ k := by
  induction k generalizing digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at h
  | succ k ih =>
      cases digits with
      | nil => simp
      | cons a digits =>
          simp only [isCanonical_succ_cons] at h
          simp only [List.length_cons, Nat.add_le_add_iff_right]
          exact ih h.2.2

theorem IsCanonical.head_le {k a : ℕ} {digits : List ℕ}
    (h : IsCanonical k (a :: digits)) : k ≤ a := by
  cases k with
  | zero => simp at h
  | succ k => exact h.1

theorem isCanonical_singleton {k a : ℕ} (hk : 1 ≤ k) (hka : k ≤ a) :
    IsCanonical k [a] := by
  cases k with
  | zero => omega
  | succ k => simp [IsCanonical, hka]

theorem IsCanonical.tail {k a : ℕ} {digits : List ℕ}
    (h : IsCanonical k (a :: digits)) : IsCanonical (k - 1) digits := by
  cases k with
  | zero => simp at h
  | succ k => exact h.2.2

theorem IsCanonical.tail_lt_head {k a : ℕ} {digits : List ℕ}
    (h : IsCanonical k (a :: digits)) {b : ℕ} (hb : b ∈ digits) : b < a := by
  cases k with
  | zero => simp at h
  | succ k => exact h.2.1 b hb

theorem IsCanonical.all_lt_of_head {k b : ℕ} {digits : List ℕ}
    (h : IsCanonical k (b :: digits)) {n : ℕ}
    (hb : b < n) : ∀ a ∈ b :: digits, a < n := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hb
  · exact (h.tail_lt_head ha).trans hb

/-- Lowering every occupied cascade position preserves canonicity. -/
theorem IsCanonical.lowerIndex
    {k k' : ℕ} {digits : List ℕ} (h : IsCanonical k digits)
    (hkk : k' ≤ k) (hlen : digits.length ≤ k') :
    IsCanonical k' digits := by
  induction digits generalizing k k' with
  | nil => simp
  | cons a digits ih =>
      cases k' with
      | zero => simp at hlen
      | succ k' =>
          cases k with
          | zero => simp at h
          | succ k =>
              simp only [isCanonical_succ_cons] at h ⊢
              refine ⟨hkk.trans h.1, h.2.1, ?_⟩
              apply ih h.2.2 (by omega)
              simpa using hlen

/-- Concatenate two canonical cascades whose digits are separated. -/
theorem isCanonical_append
    {k : ℕ} {xs ys : List ℕ}
    (hxs : IsCanonical k xs)
    (hys : IsCanonical (k - xs.length) ys)
    (hcross : ∀ a ∈ xs, ∀ b ∈ ys, b < a) :
    IsCanonical k (xs ++ ys) := by
  induction xs generalizing k with
  | nil => simpa using hys
  | cons a xs ih =>
      cases k with
      | zero => simp at hxs
      | succ k =>
          simp only [List.cons_append, isCanonical_succ_cons] at hxs ⊢
          refine ⟨hxs.1, ?_, ?_⟩
          · intro b hb
            rcases List.mem_append.mp hb with hb | hb
            · exact hxs.2.1 b hb
            · exact hcross a List.mem_cons_self b hb
          · apply ih hxs.2.2
              (by simpa [List.length_cons] using hys)
            intro c hc b hb
            exact hcross c (List.mem_cons_of_mem a hc) b hb

/-! ### Diagonal (unary) runs -/

/-- `a, a-1, ...` with the requested number of terms. -/
def diagonalDigits : ℕ → ℕ → List ℕ
  | _, 0 => []
  | a, len + 1 => a :: diagonalDigits (a - 1) len

@[simp] theorem diagonalDigits_zero (a : ℕ) : diagonalDigits a 0 = [] := rfl

@[simp] theorem diagonalDigits_succ (a len : ℕ) :
    diagonalDigits a (len + 1) = a :: diagonalDigits (a - 1) len := rfl

theorem mem_diagonalDigits_le {a len d : ℕ}
    (hd : d ∈ diagonalDigits a len) : d ≤ a := by
  induction len generalizing a with
  | zero => simp at hd
  | succ len ih =>
      rcases List.mem_cons.mp hd with rfl | hd
      · exact le_rfl
      · exact (ih hd).trans (Nat.sub_le a 1)

theorem isCanonical_diagonalDigits {a len : ℕ} (hlen : len ≤ a) :
    IsCanonical a (diagonalDigits a len) := by
  induction len generalizing a with
  | zero => simp
  | succ len ih =>
      cases a with
      | zero => omega
      | succ a =>
          simp only [diagonalDigits_succ, Nat.add_sub_cancel,
            isCanonical_succ_cons]
          refine ⟨le_rfl, ?_, ih (by omega)⟩
          intro d hd
          exact lt_of_le_of_lt (mem_diagonalDigits_le hd) (Nat.lt_succ_self a)

theorem cascadeValue_diagonalDigits {a len : ℕ} (hlen : len ≤ a) :
    cascadeValue a (diagonalDigits a len) = len := by
  induction len generalizing a with
  | zero => simp
  | succ len ih =>
      cases a with
      | zero => omega
      | succ a =>
          have hi := ih (a := a) (by omega)
          simp only [diagonalDigits_succ, cascadeValue_cons, Nat.add_sub_cancel,
            Nat.choose_self]
          rw [hi]
          omega

/-- The lowered value of the full diagonal run is `1 + ... + a`. -/
theorem cascadeShadowValue_diagonalDigits_full (a : ℕ) :
    cascadeShadowValue a (diagonalDigits a a) = (a + 1).choose 2 := by
  induction a with
  | zero => simp [cascadeShadowValue]
  | succ a ih =>
      simp only [diagonalDigits_succ, cascadeShadowValue_cons,
        Nat.add_sub_cancel, show a + 1 - 2 = a - 1 by omega]
      rw [show cascadeValue (a - 1) (diagonalDigits a a) =
          cascadeShadowValue a (diagonalDigits a a) by rfl, ih]
      have hp : (a + 1 + 1).choose 2 = a + 1 + (a + 1).choose 2 := by
        simpa [Nat.choose_one_right] using Nat.choose_succ_succ (a + 1) 1
      rw [hp]
      simp

/-- The lowered value of an arbitrary initial diagonal run. -/
theorem cascadeShadowValue_diagonalDigits {a len : ℕ} (hlen : len ≤ a) :
    cascadeShadowValue a (diagonalDigits a len) =
      (a + 1).choose 2 - (a + 1 - len).choose 2 := by
  induction len generalizing a with
  | zero => simp
  | succ len ih =>
      cases a with
      | zero => omega
      | succ a =>
          have hlen' : len ≤ a := by omega
          have hi := ih (a := a) hlen'
          simp only [diagonalDigits_succ, cascadeShadowValue_cons,
            Nat.add_sub_cancel, show a + 1 - 2 = a - 1 by omega]
          rw [show cascadeValue (a - 1) (diagonalDigits a len) =
              cascadeShadowValue a (diagonalDigits a len) by rfl,
            hi]
          have hp : (a + 2).choose 2 = a + 1 + (a + 1).choose 2 := by
            simpa [Nat.choose_one_right] using Nat.choose_succ_succ (a + 1) 1
          rw [show (a + 1).choose a = a + 1 by
              exact Nat.choose_succ_self_right a,
            hp]
          have hidx : a + 1 + 1 - (len + 1) = a + 1 - len := by omega
          rw [hidx]
          have hchoose : (a + 1 - len).choose 2 ≤ (a + 1).choose 2 :=
            Nat.choose_le_choose 2 (Nat.sub_le (a + 1) len)
          omega

/-- The lowered value of the diagonal run ending at digit `2`. -/
theorem cascadeShadowValue_diagonalDigits_drop_one (a : ℕ) :
    cascadeShadowValue a (diagonalDigits a (a - 1)) =
      (a + 1).choose 2 - 1 := by
  induction a with
  | zero => simp [cascadeShadowValue]
  | succ a ih =>
      cases a with
      | zero => simp [cascadeShadowValue]
      | succ a =>
          simp only [diagonalDigits_succ,
            cascadeShadowValue_cons,
            show a + 1 + 1 - 1 = a + 1 by omega,
            show a + 1 + 1 - 2 = a by omega]
          rw [show cascadeValue a (diagonalDigits (a + 1) a) =
              cascadeShadowValue (a + 1) (diagonalDigits (a + 1) a) by rfl]
          have hi : cascadeShadowValue (a + 1) (diagonalDigits (a + 1) a) =
              (a + 2).choose 2 - 1 := by simpa using ih
          rw [hi]
          have hp : (a + 3).choose 2 = a + 2 + (a + 2).choose 2 := by
            simpa [Nat.choose_one_right] using Nat.choose_succ_succ (a + 2) 1
          have hpos : 1 ≤ (a + 2).choose 2 := Nat.choose_pos (by omega)
          rw [show a + 1 + 1 + 1 = a + 3 by omega,
            show (a + 1 + 1).choose (a + 1) = a + 2 by
              exact Nat.choose_succ_self_right (a + 1), hp]
          omega

end Erdos776.KruskalKatona
