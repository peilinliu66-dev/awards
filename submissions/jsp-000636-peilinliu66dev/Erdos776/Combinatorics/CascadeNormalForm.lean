import Erdos776.Combinatorics.Cascade
import Mathlib.Data.Nat.Find

/-!
# Greedy normal form for binomial cascades

Mathlib's Kruskal--Katona development deliberately leaves the numerical
cascade representation as a TODO.  This file supplies it: every natural
number has a canonical `k`-cascade for `k > 0`, obtained by repeatedly taking
the largest possible upper binomial index.
-/

namespace Erdos776.KruskalKatona

/-- A simple finite bound large enough to contain the greedy head digit. -/
theorem lt_choose_add (m k : ℕ) (hk : 1 ≤ k) :
    m < (m + k).choose k := by
  induction m with
  | zero =>
      simpa only [Nat.zero_add] using (Nat.choose_pos (show k ≤ k from le_rfl))
  | succ m ih =>
      have hpos : 0 < (m + k).choose (k - 1) :=
        Nat.choose_pos (by omega)
      have hp : (m + 1 + k).choose k =
          (m + k).choose (k - 1) + (m + k).choose k := by
        simpa only [Nat.succ_eq_add_one, show k - 1 + 1 = k by omega,
          show m + k + 1 = m + 1 + k by omega] using
            Nat.choose_succ_succ (m + k) (k - 1)
      rw [hp]
      omega

/-- The largest `a ≤ m+k` with `choose a k ≤ m`. -/
def greedyHead (m k : ℕ) : ℕ :=
  Nat.findGreatest (fun a => a.choose k ≤ m) (m + k)

theorem greedyHead_spec {m k : ℕ} (hm : 0 < m) :
    (greedyHead m k).choose k ≤ m := by
  unfold greedyHead
  exact Nat.findGreatest_spec
    (P := fun a => a.choose k ≤ m) (m := k) (n := m + k)
    (by omega) (by simpa only [Nat.choose_self] using Nat.succ_le_of_lt hm)

theorem le_greedyHead {m k : ℕ} (hm : 0 < m) :
    k ≤ greedyHead m k := by
  apply Nat.le_findGreatest
    (P := fun a => a.choose k ≤ m) (m := k) (n := m + k)
  · omega
  · simpa only [Nat.choose_self] using Nat.succ_le_of_lt hm

theorem greedyHead_lt_bound {m k : ℕ} (hm : 0 < m) (hk : 1 ≤ k) :
    greedyHead m k < m + k := by
  have hle := Nat.findGreatest_le (P := fun a => a.choose k ≤ m) (m + k)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hspec := greedyHead_spec (k := k) hm
  rw [heq] at hspec
  exact (Nat.not_lt_of_ge hspec) (lt_choose_add m k hk)

theorem greedyHead_next_gt {m k : ℕ} (hm : 0 < m) (hk : 1 ≤ k) :
    m < (greedyHead m k + 1).choose k := by
  have hnext : greedyHead m k + 1 ≤ m + k := by
    exact greedyHead_lt_bound hm hk
  have hnot := Nat.findGreatest_is_greatest
    (P := fun a => a.choose k ≤ m)
    (Nat.lt_succ_self (greedyHead m k)) hnext
  have hnot' : ¬(greedyHead m k + 1).choose k ≤ m := by
    simpa [Nat.succ_eq_add_one] using hnot
  omega

/-- The remainder after removing the greedy head fits below the next digit. -/
theorem greedyRemainder_lt {m k : ℕ} (hm : 0 < m) (hk : 1 ≤ k) :
    m - (greedyHead m k).choose k <
      (greedyHead m k).choose (k - 1) := by
  have hnext := greedyHead_next_gt hm hk
  have hspec := greedyHead_spec (k := k) hm
  have hp : (greedyHead m k + 1).choose k =
      (greedyHead m k).choose (k - 1) +
        (greedyHead m k).choose k := by
    simpa only [Nat.succ_eq_add_one, show k - 1 + 1 = k by omega] using
      Nat.choose_succ_succ (greedyHead m k) (k - 1)
  rw [hp] at hnext
  omega

/-- Greedy canonical digits, recursively indexed by the lower binomial index. -/
def canonicalDigits : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, m =>
      if m = 0 then []
      else
        let a := greedyHead m (k + 1)
        a :: canonicalDigits k (m - a.choose (k + 1))

@[simp] theorem canonicalDigits_zero (m : ℕ) : canonicalDigits 0 m = [] := rfl

@[simp] theorem canonicalDigits_succ_zero (k : ℕ) :
    canonicalDigits (k + 1) 0 = [] := by
  simp [canonicalDigits]

theorem canonicalDigits_succ_of_pos {k m : ℕ} (hm : 0 < m) :
    canonicalDigits (k + 1) m =
      greedyHead m (k + 1) ::
        canonicalDigits k (m - (greedyHead m (k + 1)).choose (k + 1)) := by
  simp [canonicalDigits, hm.ne']

/-- The greedy digits represent the original value. -/
theorem cascadeValue_canonicalDigits {k m : ℕ} (hk : 1 ≤ k) :
    cascadeValue k (canonicalDigits k m) = m := by
  induction k generalizing m with
  | zero => omega
  | succ k ih =>
      by_cases hm : m = 0
      · subst m
        simp
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        rw [canonicalDigits_succ_of_pos hmpos, cascadeValue_cons]
        have htail :
            cascadeValue k
                (canonicalDigits k
                  (m - (greedyHead m (k + 1)).choose (k + 1))) =
              m - (greedyHead m (k + 1)).choose (k + 1) := by
          by_cases hk0 : k = 0
          · subst k
            have hrem := greedyRemainder_lt hmpos (show 1 ≤ 0 + 1 by omega)
            simp at hrem ⊢
            omega
          · exact ih (Nat.one_le_iff_ne_zero.mpr hk0)
        rw [show k + 1 - 1 = k by omega, htail]
        exact Nat.add_sub_of_le (greedyHead_spec (k := k + 1) hmpos)

/-- Every greedy digit lies below any binomial bound which already exceeds `m`. -/
theorem canonicalDigits_all_lt
    {k m A : ℕ} (hk : 1 ≤ k) (hmA : m < A.choose k) :
    ∀ d ∈ canonicalDigits k m, d < A := by
  induction k generalizing m A with
  | zero => omega
  | succ k ih =>
      by_cases hm : m = 0
      · subst m
        simp
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        rw [canonicalDigits_succ_of_pos hmpos]
        have hheadA : greedyHead m (k + 1) < A := by
          by_contra hnot
          have hchoose : A.choose (k + 1) ≤
              (greedyHead m (k + 1)).choose (k + 1) :=
            Nat.choose_le_choose (k + 1) (by omega)
          exact (Nat.not_lt_of_ge
            (hchoose.trans (greedyHead_spec (k := k + 1) hmpos))) hmA
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hheadA
        · by_cases hk0 : k = 0
          · subst k
            have hrem := greedyRemainder_lt hmpos (show 1 ≤ 0 + 1 by omega)
            simp at hrem hd
          · exact (ih (A := greedyHead m (k + 1))
                (Nat.one_le_iff_ne_zero.mpr hk0)
                (by simpa only [Nat.add_sub_cancel] using greedyRemainder_lt (k := k + 1) hmpos (by omega)) d hd).trans
              hheadA

/-- The greedy representation is canonical. -/
theorem isCanonical_canonicalDigits {k m : ℕ} (hk : 1 ≤ k) :
    IsCanonical k (canonicalDigits k m) := by
  induction k generalizing m with
  | zero => omega
  | succ k ih =>
      by_cases hm : m = 0
      · subst m
        simp
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        rw [canonicalDigits_succ_of_pos hmpos]
        rw [isCanonical_succ_cons]
        refine ⟨le_greedyHead (k := k + 1) hmpos, ?_, ?_⟩
        · by_cases hk0 : k = 0
          · subst k
            have hrem := greedyRemainder_lt hmpos (show 1 ≤ 0 + 1 by omega)
            simp at hrem
            simp [hrem]
          · exact canonicalDigits_all_lt
              (Nat.one_le_iff_ne_zero.mpr hk0)
              (by simpa only [Nat.add_sub_cancel] using greedyRemainder_lt (k := k + 1) hmpos (by omega))
        · by_cases hk0 : k = 0
          · subst k
            simp
          · exact ih (Nat.one_le_iff_ne_zero.mpr hk0)

/-- A bounded canonical cascade is strictly below the next complete block. -/
theorem cascadeValue_lt_choose_of_all_lt
    {k A : ℕ} {digits : List ℕ}
    (hkA : k ≤ A) (hcanon : IsCanonical k digits)
    (hall : ∀ d ∈ digits, d < A) :
    cascadeValue k digits < A.choose k := by
  induction k generalizing A digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at hcanon
  | succ k ih =>
      cases digits with
      | nil =>
          simp only [cascadeValue_nil]
          exact Nat.choose_pos hkA
      | cons a digits =>
          have haA : a < A := hall a List.mem_cons_self
          have htailcanon : IsCanonical k digits := hcanon.2.2
          have htailall : ∀ d ∈ digits, d < a := hcanon.2.1
          have htail : cascadeValue k digits < a.choose k :=
            ih ((Nat.le_succ k).trans hcanon.1) htailcanon htailall
          have hp : (a + 1).choose (k + 1) =
              a.choose k + a.choose (k + 1) := by
            simpa only [Nat.succ_eq_add_one] using Nat.choose_succ_succ a k
          have hmono : (a + 1).choose (k + 1) ≤ A.choose (k + 1) :=
            Nat.choose_le_choose (k + 1) (by omega)
          simp only [cascadeValue_cons, Nat.add_sub_cancel]
          omega

/-- A number bracketed by two consecutive binomials has that greedy head. -/
theorem greedyHead_eq_of_bounds
    {m k a : ℕ} (hk : 1 ≤ k) (ha : k ≤ a)
    (hle : a.choose k ≤ m) (hlt : m < (a + 1).choose k) :
    greedyHead m k = a := by
  have hm : 0 < m :=
    lt_of_lt_of_le (Nat.choose_pos ha) hle
  have habound : a ≤ m + k := by
    by_contra hnot
    have hmono : (m + k).choose k ≤ a.choose k :=
      Nat.choose_le_choose k (by omega)
    exact (Nat.not_lt_of_ge (hmono.trans hle)) (lt_choose_add m k hk)
  unfold greedyHead
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨habound, fun _ => hle, ?_⟩
  intro b hab hbbound hb
  have hmono : (a + 1).choose k ≤ b.choose k :=
    Nat.choose_le_choose k (by omega)
  omega

/-- Canonical binomial cascades are unique. -/
theorem canonicalDigits_unique
    {k m : ℕ} {digits : List ℕ}
    (hcanon : IsCanonical k digits)
    (hvalue : cascadeValue k digits = m) :
    digits = canonicalDigits k m := by
  induction k generalizing m digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at hcanon
  | succ k ih =>
      by_cases hm : m = 0
      · have hvalue0 : cascadeValue (k + 1) digits = 0 := hvalue.trans hm
        have hdigits : digits = [] := by
          cases digits with
          | nil => rfl
          | cons a tail =>
              have hpos : 0 < a.choose (k + 1) := Nat.choose_pos hcanon.1
              simp only [cascadeValue_cons, Nat.add_sub_cancel] at hvalue0
              omega
        simp [hdigits, hm]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        cases digits with
        | nil =>
            simp at hvalue
            omega
        | cons a tail =>
            have htailcanon : IsCanonical k tail := hcanon.2.2
            have htaillt : cascadeValue k tail < a.choose k :=
              cascadeValue_lt_choose_of_all_lt
                ((Nat.le_succ k).trans hcanon.1) htailcanon hcanon.2.1
            have hvalue' : a.choose (k + 1) + cascadeValue k tail = m := by
              simpa only [cascadeValue_cons, Nat.add_sub_cancel] using hvalue
            have hle : a.choose (k + 1) ≤ m := by omega
            have hp : (a + 1).choose (k + 1) =
                a.choose k + a.choose (k + 1) := by
              simpa only [Nat.succ_eq_add_one] using Nat.choose_succ_succ a k
            have hlt : m < (a + 1).choose (k + 1) := by omega
            have hhead : greedyHead m (k + 1) = a :=
              greedyHead_eq_of_bounds (by omega) hcanon.1 hle hlt
            have htailvalue : cascadeValue k tail = m - a.choose (k + 1) := by
              omega
            have htail : tail = canonicalDigits k (m - a.choose (k + 1)) :=
              ih htailcanon htailvalue
            rw [canonicalDigits_succ_of_pos hmpos, hhead]
            exact congrArg (List.cons a) htail

end Erdos776.KruskalKatona
