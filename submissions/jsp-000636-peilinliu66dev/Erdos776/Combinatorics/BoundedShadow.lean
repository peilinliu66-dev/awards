import Erdos776.Combinatorics.NormalShadow

/-!
# Ground-bounded evaluation of the canonical shadow

`canonicalDigits` uses the universally valid search bound `m+k`.  That is
convenient for proofs but unsuitable for finite certificates when `m` is a
large binomial-scale integer.  The evaluator below searches only below the
largest possible cascade digit and lowers that bound after each digit.
-/

namespace Erdos776.KruskalKatona

/-- Multiplicative evaluation of `choose n k`, keeping intermediate values small. -/
def linearChoose (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => linearChoose n k * (n - k) / (k + 1)

@[simp] theorem linearChoose_eq_choose (n k : ℕ) :
    linearChoose n k = n.choose k := by
  induction k with
  | zero => simp [linearChoose]
  | succ k ih =>
      rw [linearChoose, ih]
      have hmul : (k + 1) * n.choose (k + 1) =
          n.choose k * (n - k) := by
        rw [Nat.mul_comm]
        exact Nat.choose_succ_right_eq n k
      exact (Nat.eq_div_of_mul_eq_right (by omega) hmul).symm

/--
An executable binomial coefficient which first uses symmetry to minimize the
multiplicative loop length.
-/
def fastBinom (n k : ℕ) : ℕ :=
  if k ≤ n then linearChoose n (min k (n - k)) else 0

@[simp] theorem fastBinom_eq_choose (n k : ℕ) :
    fastBinom n k = n.choose k := by
  unfold fastBinom
  by_cases hk : k ≤ n
  · rw [if_pos hk, linearChoose_eq_choose]
    by_cases hhalf : k ≤ n - k
    · rw [min_eq_left hhalf]
    · rw [min_eq_right (by omega), Nat.choose_symm hk]
  · rw [if_neg hk, Nat.choose_eq_zero_of_lt (by omega)]

/-- Descend through candidate digits while updating `choose a k` in constant space. -/
def descendingGreedyHead (m k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | a + 1, value =>
      if value ≤ m then a + 1
      else descendingGreedyHead m k a (value * (a + 1 - k) / (a + 1))

theorem descendingGreedyHead_eq_findGreatest (m k n : ℕ) :
    descendingGreedyHead m k n (n.choose k) =
      Nat.findGreatest (fun a => a.choose k ≤ m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [descendingGreedyHead]
      by_cases hvalue : (n + 1).choose k ≤ m
      · rw [if_pos hvalue]
        exact (Nat.findGreatest_eq (P := fun a => a.choose k ≤ m) hvalue).symm
      · rw [if_neg hvalue,
          Nat.findGreatest_of_not (P := fun a => a.choose k ≤ m) hvalue]
        have hmul : (n + 1) * n.choose k =
            (n + 1).choose k * (n + 1 - k) := by
          rw [Nat.mul_comm]
          exact Nat.choose_mul_succ_eq n k
        have hupdate : (n + 1).choose k * (n + 1 - k) / (n + 1) =
            n.choose k := by
          exact (Nat.eq_div_of_mul_eq_right (by omega) hmul).symm
        rw [hupdate, ih]

/-- The largest feasible head digit, searched only up to `n`. -/
def boundedGreedyHead (n m k : ℕ) : ℕ :=
  descendingGreedyHead m k n (fastBinom n k)

theorem boundedGreedyHead_eq_greedyHead
    {n m k : ℕ} (hm : 0 < m) (hk : 1 ≤ k)
    (hbound : m < (n + 1).choose k) :
    boundedGreedyHead n m k = greedyHead m k := by
  have hheadLe : greedyHead m k ≤ n := by
    by_contra hnot
    have hn : n + 1 ≤ greedyHead m k := by omega
    have hmono := Nat.choose_le_choose k hn
    have hspec := greedyHead_spec (k := k) hm
    omega
  unfold boundedGreedyHead
  rw [fastBinom_eq_choose, descendingGreedyHead_eq_findGreatest]
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨hheadLe, fun _ => greedyHead_spec (k := k) hm, ?_⟩
  intro b hab hbn hb
  have hnext := greedyHead_next_gt hm hk
  have hmono := Nat.choose_le_choose k (show greedyHead m k + 1 ≤ b by omega)
  omega

/--
Evaluate the shadow while bounding every head search by the preceding digit.
The first argument is the largest digit currently allowed.
-/
def boundedShadow : ℕ → ℕ → ℕ → ℕ
  | _, 0, _ => 0
  | n, k + 1, m =>
      if m = 0 then 0
      else
        let a := boundedGreedyHead n m (k + 1)
        fastBinom a k +
          boundedShadow (a - 1) k (m - fastBinom a (k + 1))

@[simp] theorem boundedShadow_zero_index (n m : ℕ) :
    boundedShadow n 0 m = 0 := rfl

@[simp] theorem boundedShadow_zero_value (n k : ℕ) :
    boundedShadow n k 0 = 0 := by
  cases k <;> simp [boundedShadow]

theorem boundedShadow_eq_canonicalShadow_of_lt
    {n k m : ℕ} (hbound : m < (n + 1).choose k) :
    boundedShadow n k m = canonicalShadow k m := by
  induction k generalizing n m with
  | zero => simp [boundedShadow, canonicalShadow, cascadeShadowValue]
  | succ k ih =>
      by_cases hm0 : m = 0
      · subst m
        simp
      · have hm : 0 < m := Nat.pos_of_ne_zero hm0
        have hhead := boundedGreedyHead_eq_greedyHead hm (by omega) hbound
        let a := greedyHead m (k + 1)
        let rem := m - a.choose (k + 1)
        have ha : k + 1 ≤ a := by
          dsimp [a]
          exact le_greedyHead hm
        have hrem : rem < ((a - 1) + 1).choose k := by
          have h := greedyRemainder_lt hm (show 1 ≤ k + 1 by omega)
          dsimp [rem, a]
          simpa only [Nat.add_sub_cancel, show greedyHead m (k + 1) - 1 + 1 =
            greedyHead m (k + 1) by omega] using h
        have hi := ih hrem
        rw [boundedShadow]
        simp only [hm0, if_false, hhead, fastBinom_eq_choose]
        change a.choose k + boundedShadow (a - 1) k rem = _
        rw [canonicalShadow, canonicalDigits_succ_of_pos hm]
        change a.choose k + boundedShadow (a - 1) k rem =
          a.choose k + canonicalShadow k rem
        rw [hi]

/-- A feasible state may be evaluated with searches bounded by its ground size. -/
theorem boundedShadow_eq_canonicalShadow
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    boundedShadow n k m = canonicalShadow k m := by
  by_cases hm0 : m = 0
  · subst m
    simp
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hkn : k ≤ n := by
    by_contra hnot
    rw [Nat.choose_eq_zero_of_lt (by omega)] at hm
    omega
  have hpos : 0 < n.choose (k - 1) := Nat.choose_pos (by omega)
  have hp : (n + 1).choose k = n.choose (k - 1) + n.choose k := by
    simpa only [Nat.succ_eq_add_one, show k - 1 + 1 = k by omega] using
      Nat.choose_succ_succ n (k - 1)
  apply boundedShadow_eq_canonicalShadow_of_lt
  rw [hp]
  omega

end Erdos776.KruskalKatona
