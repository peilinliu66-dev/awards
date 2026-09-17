import Erdos776.Uniform.LowerWindow.Supersolution

/-!
# Parameters of the lower-window anchor ladder

This file formalizes the threshold sequence and the maximal anchor index from
Sections 3--5.  These are pure arithmetic facts, independent of the later
cascade manipulations.
-/

namespace Erdos776.Uniform

/-- `T_q` from (3.1). -/
def anchorThreshold : ℕ → ℕ
  | 0 => 28
  | q + 1 => (anchorThreshold q - 2 * q).choose 2

/-- `B_q = T_q - 2q`. -/
def anchorBase (q : ℕ) : ℕ := anchorThreshold q - 2 * q

@[simp] theorem anchorThreshold_zero : anchorThreshold 0 = 28 := rfl

@[simp] theorem anchorThreshold_succ (q : ℕ) :
    anchorThreshold (q + 1) = (anchorThreshold q - 2 * q).choose 2 := rfl

@[simp] theorem anchorThreshold_one : anchorThreshold 1 = 378 := by
  norm_num [anchorThreshold, Nat.choose_two_right]

@[simp] theorem anchorThreshold_two : anchorThreshold 2 = 70500 := by
  norm_num [anchorThreshold, Nat.choose_two_right]

@[simp] theorem anchorThreshold_three : anchorThreshold 3 = 2484807760 := by
  norm_num [anchorThreshold, Nat.choose_two_right]

/-- A coarse estimate used to prove that the anchor ladder is unbounded. -/
theorem two_mul_le_choose_two :
    ∀ x : ℕ, 5 ≤ x → 2 * x ≤ x.choose 2 := by
  intro x hx
  induction x with
  | zero => omega
  | succ x ih =>
      by_cases hx5 : 5 ≤ x
      · have hprev := ih hx5
        rw [show (x + 1).choose 2 = x.choose 1 + x.choose 2 by
          simpa using Nat.choose_succ_succ x 1]
        simp only [Nat.choose_one_right]
        omega
      · have hx4 : x = 4 := by omega
        subst x
        norm_num [Nat.choose_two_right]

/-- The elementary growth estimate (3.5). -/
theorem anchorThreshold_lower (t : ℕ) (ht : 1 ≤ t) :
    128 * t + 250 ≤ anchorThreshold t := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases ht0 : t = 0
      · subst t
        norm_num [Nat.choose_two_right]
      · have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
        have hprev := ih ht1
        let x := anchorThreshold t - 2 * t
        have hx : 126 * t + 250 ≤ x := by
          dsimp [x]
          omega
        have hx5 : 5 ≤ x := by omega
        have hchoose := two_mul_le_choose_two x hx5
        rw [anchorThreshold_succ]
        change (128 * (t + 1) + 250 ≤ x.choose 2)
        exact (show 128 * (t + 1) + 250 ≤ 2 * x by omega).trans hchoose

theorem anchorThreshold_mono (q : ℕ) :
    anchorThreshold q ≤ anchorThreshold (q + 1) := by
  by_cases hq0 : q = 0
  · subst q
    norm_num [Nat.choose_two_right]
  · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    have hlower := anchorThreshold_lower q hq1
    let x := anchorThreshold q - 2 * q
    have hx : 5 ≤ x := by
      dsimp [x]
      omega
    have hchoose := two_mul_le_choose_two x hx
    rw [anchorThreshold_succ]
    change anchorThreshold q ≤ x.choose 2
    exact (show anchorThreshold q ≤ 2 * x by
      dsimp [x]
      omega).trans hchoose

theorem monotone_anchorThreshold : Monotone anchorThreshold :=
  monotone_nat_of_le_succ anchorThreshold_mono

theorem anchorThreshold_eventually_gt (r : ℕ) :
    ∃ q, r < anchorThreshold q := by
  refine ⟨r + 1, ?_⟩
  have hlower := anchorThreshold_lower (r + 1) (by omega)
  omega

/-- The first anchor threshold strictly above `r`. -/
noncomputable def firstExceedingAnchor (r : ℕ) : ℕ :=
  Nat.find (anchorThreshold_eventually_gt r)

/-- The maximal `t` satisfying `T_t ≤ r`. -/
noncomputable def maximalAnchorIndex (r : ℕ) : ℕ :=
  firstExceedingAnchor r - 1

/-- The three properties in (3.3), including positivity. -/
def IsMaximalAnchorIndex (r t : ℕ) : Prop :=
  1 ≤ t ∧ anchorThreshold t ≤ r ∧ r < anchorThreshold (t + 1)

theorem firstExceedingAnchor_spec (r : ℕ) :
    r < anchorThreshold (firstExceedingAnchor r) := by
  exact Nat.find_spec (anchorThreshold_eventually_gt r)

theorem maximalAnchorIndex_spec (r : ℕ) (hr : 378 ≤ r) :
    IsMaximalAnchorIndex r (maximalAnchorIndex r) := by
  let q := firstExceedingAnchor r
  have hqspec : r < anchorThreshold q := firstExceedingAnchor_spec r
  have hq2 : 2 ≤ q := by
    by_contra hnot
    have hcases : q = 0 ∨ q = 1 := by omega
    rcases hcases with hq0 | hq1
    · rw [hq0, anchorThreshold_zero] at hqspec
      omega
    · rw [hq1, anchorThreshold_one] at hqspec
      omega
  have hpredlt : q - 1 < q := by omega
  have hpredNot : ¬ r < anchorThreshold (q - 1) := by
    exact Nat.find_min (anchorThreshold_eventually_gt r) hpredlt
  have hsucc : q - 1 + 1 = q := by omega
  dsimp [maximalAnchorIndex, firstExceedingAnchor]
  change IsMaximalAnchorIndex r (q - 1)
  exact ⟨by omega, by omega, by simpa [hsucc] using hqspec⟩

/-- `N = r-2t` from (3.4). -/
def anchorN (r t : ℕ) : ℕ := r - 2 * t

/-- `c = 2t+3` from (3.4). -/
def phaseWidth (t : ℕ) : ℕ := 2 * t + 3

/-- `h = t+2` from (3.4). -/
def phaseSlot (t : ℕ) : ℕ := t + 2

/-- `s_j` from (4.4), with the formula extended harmlessly to `j=0`. -/
def towerStone (r t j : ℕ) : ℕ :=
  r + 1 - phaseWidth t * 2 ^ (j - 1)

/-- The consequence `r ≥ 64c` recorded as (3.6). -/
theorem sixtyFour_mul_phaseWidth_le
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    64 * phaseWidth t ≤ r := by
  have hlower := anchorThreshold_lower t ht.1
  have hTr := ht.2.1
  simp only [phaseWidth]
  omega

theorem first_towerStone_eq (r t : ℕ) :
    towerStone r t 1 = anchorN r t - 2 := by
  simp [towerStone, phaseWidth, anchorN]
  omega

theorem towerStone_succ
    {r t j : ℕ} (hj : 1 ≤ j)
    (hpow : phaseWidth t * 2 ^ j ≤ r + 1) :
    towerStone r t (j + 1) = 2 * towerStone r t j - r - 1 := by
  have hpowEq : 2 ^ j = 2 * 2 ^ (j - 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
    omega
  let a := phaseWidth t * 2 ^ (j - 1)
  have hmul : phaseWidth t * 2 ^ j = 2 * a := by
    dsimp [a]
    rw [hpowEq]
    simp [Nat.mul_assoc, Nat.mul_comm]
  have htwoa : 2 * a ≤ r + 1 := by
    rw [← hmul]
    exact hpow
  simp only [towerStone, show j + 1 - 1 = j by omega, hmul]
  change r + 1 - 2 * a = 2 * (r + 1 - a) - r - 1
  omega

end Erdos776.Uniform
