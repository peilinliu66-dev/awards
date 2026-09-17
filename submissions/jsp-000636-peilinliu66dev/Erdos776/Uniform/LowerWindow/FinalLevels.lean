import Erdos776.Uniform.LowerWindow.ScalarCollapse

/-!
# The final two lower-window levels

This is Section 11.  It turns the three possible terminal scalar residuals
into the exact level-three and level-two supersolution states.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- `F₀(z)` at level four. -/
def finalFourState (r z : ℕ) : ℕ :=
  (r + 2).choose 4 + (r + 1).choose 3 + z

/-- The general level-four to level-three identity (11.1). -/
theorem finalFourState_step
    {r z : ℕ} (hr : 6 ≤ r) (hz : z ≤ 6) (hzpos : 1 ≤ z) :
    r + canonicalShadow 4 (finalFourState r z) =
      (r + 3).choose 3 + (canonicalShadow 2 z - 1) := by
  have hzCap : z < (r + 1).choose 2 := by
    have hcap : 10 ≤ (r + 1).choose 2 := by
      have hmono := Nat.choose_le_choose 2 (show 5 ≤ r + 1 by omega)
      norm_num at hmono
      exact hmono
    omega
  have hinnerCap : (r + 1).choose 3 + z < (r + 2).choose 3 := by
    have hp : (r + 2).choose 3 =
        (r + 1).choose 2 + (r + 1).choose 3 := by
      simpa only [Nat.succ_eq_add_one, show r + 1 + 1 = r + 2 by omega] using
        Nat.choose_succ_succ (r + 1) 2
    omega
  have hshell4 := canonicalShadow_add_shell
    (B := r + 2) (k := 4) (x := (r + 1).choose 3 + z)
    (by omega) (by omega) hinnerCap
  have hshell3 := canonicalShadow_add_shell
    (B := r + 1) (k := 3) (x := z)
    (by omega) (by omega) hzCap
  have hshell4' : canonicalShadow 4
      ((r + 2).choose 4 + ((r + 1).choose 3 + z)) =
      (r + 2).choose 3 + canonicalShadow 3 ((r + 1).choose 3 + z) := by
    simpa using hshell4
  have hshell3' : canonicalShadow 3 ((r + 1).choose 3 + z) =
      (r + 1).choose 2 + canonicalShadow 2 z := by
    simpa using hshell3
  unfold finalFourState
  rw [show (r + 2).choose 4 + (r + 1).choose 3 + z =
      (r + 2).choose 4 + ((r + 1).choose 3 + z) by omega,
    hshell4', hshell3']
  have hp1 : (r + 2).choose 2 = r + 1 + (r + 1).choose 2 := by
    simpa only [Nat.succ_eq_add_one, Nat.choose_one_right,
      show r + 1 + 1 = r + 2 by omega] using
        Nat.choose_succ_succ (r + 1) 1
  have hp2 : (r + 3).choose 3 =
      (r + 2).choose 2 + (r + 2).choose 3 := by
    simpa only [Nat.succ_eq_add_one,
      show r + 2 + 1 = r + 3 by omega] using
        Nat.choose_succ_succ (r + 2) 2
  have hshadowPos := canonicalShadow_pos (k := 2) (m := z) (by omega) hzpos
  have hshadowSub : canonicalShadow 2 z - 1 + 1 = canonicalShadow 2 z :=
    Nat.sub_add_cancel hshadowPos
  omega

theorem finalFourState_scalar_step
    {r t : ℕ} (hr : 6 ≤ r) (ht : 1 ≤ t) :
    r + canonicalShadow 4 (finalFourState r (scalarResidual t 0)) =
      if t = 1 then (r + 3).choose 3 + 1
      else (r + 3).choose 3 + 3 := by
  have hz := scalarResidual_zero t ht
  by_cases ht1 : t = 1
  · subst t
    have hz1 : scalarResidual 1 0 = 1 := by simpa using hz
    rw [hz1, finalFourState_step hr (by omega) (by omega)]
    simp [canonicalShadow_one]
  · simp only [if_neg ht1] at hz ⊢
    by_cases ht2 : t = 2
    · subst t
      have hz2 : scalarResidual 2 0 = 4 := by simpa using hz
      rw [hz2, finalFourState_step hr (by omega) (by omega),
        canonicalShadow_two_four]
    · have hz6 : scalarResidual t 0 = 6 := by simpa [ht2] using hz
      rw [hz6, finalFourState_step hr (by omega) (by omega),
        canonicalShadow_two_six]

/-- The last shadow is one below capacity for `t=1`, and tight thereafter. -/
theorem finalThreeState_step
    {r d : ℕ} (hr : 6 ≤ r) (hd : d = 1 ∨ d = 3) :
    r + canonicalShadow 3 ((r + 3).choose 3 + d) =
      if d = 1 then (r + 4).choose 2 - 1 else (r + 4).choose 2 := by
  have hdCap : d < (r + 3).choose 2 := by
    have hcap : 6 ≤ (r + 3).choose 2 := by
      have hmono := Nat.choose_le_choose 2 (show 4 ≤ r + 3 by omega)
      norm_num at hmono
      exact hmono
    rcases hd with rfl | rfl <;> omega
  have hp : (r + 4).choose 2 = r + 3 + (r + 3).choose 2 := by
    simpa only [Nat.succ_eq_add_one, Nat.choose_one_right,
      show r + 3 + 1 = r + 4 by omega] using
        Nat.choose_succ_succ (r + 3) 1
  rcases hd with rfl | rfl
  · change r + canonicalShadow 3 ((r + 3).choose 3 + 1) =
      (r + 4).choose 2 - 1
    have hshell := canonicalShadow_add_shell
      (B := r + 3) (k := 3) (x := 1)
      (by omega) (by omega) hdCap
    have hshell' : canonicalShadow 3 ((r + 3).choose 3 + 1) =
        (r + 3).choose 2 + canonicalShadow 2 1 := by
      simpa using hshell
    rw [hshell', canonicalShadow_one 2 (by omega)]
    have hpSub : (r + 4).choose 2 - 1 =
        r + 2 + (r + 3).choose 2 := by omega
    rw [hpSub]
    omega
  · change r + canonicalShadow 3 ((r + 3).choose 3 + 3) =
      (r + 4).choose 2
    have hshell := canonicalShadow_add_shell
      (B := r + 3) (k := 3) (x := 3)
      (by omega) (by omega) hdCap
    have hshell' : canonicalShadow 3 ((r + 3).choose 3 + 3) =
        (r + 3).choose 2 + canonicalShadow 2 3 := by
      simpa using hshell
    rw [hshell', canonicalShadow_two_three]
    rw [hp]
    omega

theorem finalScalar_bottom
    {r t : ℕ} (hr : 6 ≤ r) (_ht : 1 ≤ t) :
    let E3 := if t = 1 then (r + 3).choose 3 + 1
      else (r + 3).choose 3 + 3
    r + canonicalShadow 3 E3 =
      if t = 1 then (r + 4).choose 2 - 1 else (r + 4).choose 2 := by
  dsimp only
  by_cases ht1 : t = 1
  · simp only [ht1, if_pos]
    exact finalThreeState_step hr (Or.inl rfl)
  · simp only [ht1, if_false]
    exact finalThreeState_step hr (Or.inr rfl)

end Erdos776.Uniform
