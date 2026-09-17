import Erdos776.Combinatorics.CascadeNormalForm
import Erdos776.Combinatorics.NumericShadow

/-!
# The ground-independent numerical cascade shadow

The greedy normal form turns the finite minimum `kkShadow n k m` into a
numerical function of `k,m` alone whenever `m ≤ choose n k`.
-/

namespace Erdos776.KruskalKatona

open Finset

/-- Lower every index in the unique canonical cascade of `m`. -/
def canonicalShadow (k m : ℕ) : ℕ :=
  cascadeShadowValue k (canonicalDigits k m)

/-- Evaluate the canonical shadow through any proved canonical representation. -/
theorem canonicalShadow_eq_cascadeShadowValue
    {k m : ℕ} {digits : List ℕ}
    (hcanon : IsCanonical k digits)
    (hvalue : cascadeValue k digits = m) :
    canonicalShadow k m = cascadeShadowValue k digits := by
  unfold canonicalShadow
  rw [← canonicalDigits_unique hcanon hvalue]

/-- Closed form for the shadow of a diagonal representation of `len`. -/
theorem canonicalShadow_diagonal {a len : ℕ} (hlen : len ≤ a) :
    canonicalShadow a len =
      (a + 1).choose 2 - (a + 1 - len).choose 2 := by
  rw [canonicalShadow_eq_cascadeShadowValue
      (isCanonical_diagonalDigits hlen)
      (cascadeValue_diagonalDigits hlen),
    cascadeShadowValue_diagonalDigits hlen]

@[simp] theorem canonicalShadow_zero (k : ℕ) : canonicalShadow k 0 = 0 := by
  cases k with
  | zero => simp [canonicalShadow, cascadeShadowValue]
  | succ k => simp [canonicalShadow, cascadeShadowValue]

theorem bounded_cascadeFamily_canonicalDigits_of_lt
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m < n.choose k) :
    BoundedFamily n (cascadeFamily k (canonicalDigits k m)) := by
  intro s hs
  exact mem_cascadeFamily_lt_of_digits_lt
    (canonicalDigits_all_lt hk hm) hs

theorem bounded_cascadeFamily_singleton_digit
    {n k : ℕ} (hk : 1 ≤ k) :
    BoundedFamily n (cascadeFamily k [n]) := by
  cases k with
  | zero => omega
  | succ k =>
      intro s hs x hx
      simp only [cascadeFamily_succ_cons, cascadeFamily_nil, image_empty,
        union_empty, mem_powersetCard] at hs
      exact mem_range.mp (hs.1 hx)

theorem canonicalDigits_eq_singleton_choose
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    canonicalDigits k (n.choose k) = [n] := by
  symm
  apply canonicalDigits_unique
  · cases k with
    | zero => omega
    | succ k => simp [IsCanonical, hkn]
  · simp [cascadeValue]

/-- The shadow of a complete numerical level is the complete lower level. -/
theorem canonicalShadow_choose {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    canonicalShadow k (n.choose k) = n.choose (k - 1) := by
  rw [canonicalShadow, canonicalDigits_eq_singleton_choose hk hkn,
    cascadeShadowValue_cons, cascadeValue_nil, Nat.add_zero]

theorem bounded_cascadeFamily_canonicalDigits
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    BoundedFamily n (cascadeFamily k (canonicalDigits k m)) := by
  by_cases hm0 : m = 0
  · subst m
    have hdigits : canonicalDigits k 0 = [] := by
      cases k with
      | zero => omega
      | succ k => simp
    rw [hdigits, cascadeFamily_nil]
    intro s hs
    simp at hs
  · rcases lt_or_eq_of_le hm with hlt | heq
    · exact bounded_cascadeFamily_canonicalDigits_of_lt hk hlt
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hkn : k ≤ n := by
        by_contra hnot
        rw [heq, Nat.choose_eq_zero_of_lt (by omega)] at hmpos
        omega
      rw [heq, canonicalDigits_eq_singleton_choose hk hkn]
      exact bounded_cascadeFamily_singleton_digit hk

/--
For every feasible cardinality, the finite minimum shadow equals the cascade
shadow of the unique numerical normal form.
-/
theorem kkShadow_eq_canonicalShadow
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    kkShadow n k m = canonicalShadow k m := by
  have hcanon : IsCanonical k (canonicalDigits k m) :=
    isCanonical_canonicalDigits hk
  by_cases hm0 : m = 0
  · subst m
    have hdigits : canonicalDigits k 0 = [] := by
      cases k with
      | zero => omega
      | succ k => simp
    have heval := kkShadow_eq_cascadeShadowValue hcanon
      (show BoundedFamily n (cascadeFamily k (canonicalDigits k 0)) by
        rw [hdigits, cascadeFamily_nil]
        intro s hs
        simp at hs)
    rw [cascadeValue_canonicalDigits hk] at heval
    simpa [canonicalShadow] using heval
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    rcases lt_or_eq_of_le hm with hlt | heq
    · have heval := kkShadow_eq_cascadeShadowValue hcanon
        (bounded_cascadeFamily_canonicalDigits hk hlt.le)
      rw [cascadeValue_canonicalDigits hk] at heval
      exact heval
    · have hkn : k ≤ n := by
        by_contra hnot
        have hzero : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [heq, hzero] at hmpos
        omega
      have hsingle : IsCanonical k [n] := by
        cases k with
        | zero => omega
        | succ k => simp [IsCanonical, hkn]
      have hnormal : canonicalDigits k m = [n] := by
        symm
        apply canonicalDigits_unique hsingle
        simp [cascadeValue, heq]
      rw [heq] at hnormal ⊢
      have heval := kkShadow_eq_cascadeShadowValue hsingle
        (bounded_cascadeFamily_singleton_digit (n := n) hk)
      rw [cascadeValue_cons, cascadeValue_nil, Nat.add_zero] at heval
      simpa [canonicalShadow, hnormal] using heval

theorem canonicalShadow_eq_kkShadow
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    canonicalShadow k m = kkShadow n k m :=
  (kkShadow_eq_canonicalShadow hk hm).symm

/-- The canonical numerical shadow is monotone in the represented value. -/
theorem canonicalShadow_mono (k : ℕ) (hk : 1 ≤ k) :
    Monotone (canonicalShadow k) := by
  intro x y hxy
  let n := y + k
  have hycap : y ≤ n.choose k := by
    exact (lt_choose_add y k hk).le
  have hxcap : x ≤ n.choose k := hxy.trans hycap
  rw [canonicalShadow_eq_kkShadow hk hxcap,
    canonicalShadow_eq_kkShadow hk hycap]
  exact kkShadow_mono n k hxy

@[simp] theorem canonicalShadow_one (k : ℕ) (hk : 1 ≤ k) :
    canonicalShadow k 1 = k := by
  have hdigits : canonicalDigits k 1 = [k] := by
    simpa using canonicalDigits_eq_singleton_choose hk le_rfl
  cases k with
  | zero => omega
  | succ k =>
      simp [canonicalShadow, hdigits, cascadeShadowValue,
        Nat.choose_succ_self_right]

theorem canonicalShadow_pos {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    0 < canonicalShadow k m := by
  have hmono := canonicalShadow_mono k hk hm
  rw [canonicalShadow_one k hk] at hmono
  omega

/-- The finite sentinel extension never exceeds the true numerical shadow. -/
theorem kkShadow_le_canonicalShadow (n k m : ℕ) (hk : 1 ≤ k) :
    kkShadow n k m ≤ canonicalShadow k m := by
  by_cases hm : m ≤ n.choose k
  · rw [kkShadow_eq_canonicalShadow hk hm]
  · have hcap : n.choose k < m := by omega
    by_cases hkn : k ≤ n
    · have hmono := canonicalShadow_mono k hk hcap.le
      have hcapShadow : canonicalShadow k (n.choose k) = n.choose (k - 1) := by
        rw [canonicalShadow,
          canonicalDigits_eq_singleton_choose hk hkn,
          cascadeShadowValue_cons, cascadeValue_nil, Nat.add_zero]
      rw [hcapShadow] at hmono
      exact (kkShadow_le_sentinel n k m).trans hmono
    · by_cases hpred : k - 1 ≤ n
      · have hsucc : k = n + 1 := by omega
        have hsentinel : n.choose (k - 1) = 1 := by
          rw [hsucc]
          simp
        have hkk : kkShadow n k m ≤ 1 := by
          simpa [hsentinel] using kkShadow_le_sentinel n k m
        exact hkk.trans (canonicalShadow_pos hk (by omega))
      · have hsentinel : n.choose (k - 1) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        have hkk : kkShadow n k m ≤ 0 := by
          simpa [hsentinel] using kkShadow_le_sentinel n k m
        exact hkk.trans (Nat.zero_le _)

/-- Feasible ground sets give the same numerical shadow value. -/
theorem kkShadow_eq_kkShadow_of_feasible
    {n₁ n₂ k m : ℕ} (hk : 1 ≤ k)
    (h₁ : m ≤ n₁.choose k) (h₂ : m ≤ n₂.choose k) :
    kkShadow n₁ k m = kkShadow n₂ k m := by
  rw [kkShadow_eq_canonicalShadow hk h₁,
    kkShadow_eq_canonicalShadow hk h₂]

end Erdos776.KruskalKatona
