import Erdos776.Uniform.LowerWindow.PhaseBounds

/-!
# Ordinary phase harvests

At a harvest the old diagonal run is completed to `s_j`, while the first
term of phase `j+1` pays the incoming load.  The theorem below identifies
both sides with the explicit phase cascades, including the exceptional
length of phase one.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

theorem phaseFixedDigits_succ
    {r t j : ℕ} (hj : 1 ≤ j) :
    phaseFixedDigits r t (j + 1) =
      phaseFixedDigits r t j ++ [towerStone r t j] := by
  unfold phaseFixedDigits
  rw [show j + 1 - 1 = (j - 1) + 1 by omega,
    towerDigits_succ, show j - 1 + 1 = j by omega]
  simp [List.append_assoc]

theorem phaseRunDigits_next_zero
    {r t j : ℕ} (hj : 1 ≤ j) :
    phaseRunDigits r t (j + 1) 0 = [towerStone r t (j + 1) - 1] := by
  unfold phaseRunDigits phaseRunLength
  simp only [if_neg (show j + 1 ≠ 1 by omega)]
  rfl

theorem phaseDigits_next_zero
    {r t j : ℕ} (hj : 1 ≤ j) :
    phaseDigits r t (j + 1) 0 =
      phaseFixedDigits r t j ++
        [towerStone r t j, towerStone r t (j + 1) - 1] := by
  unfold phaseDigits
  rw [phaseFixedDigits_succ hj, phaseRunDigits_next_zero hj]
  simp [List.append_assoc]

theorem phase_harvest_active_index
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseBirth r t j - phaseExtensionCount r t j -
        (phaseFixedDigits r t j).length =
      phaseTop r t j - phaseExtensionCount r t j := by
  rw [length_phaseFixedDigits]
  unfold phaseBirth
  have hu := four_le_phaseTop_at_phase ht hj hjK
  omega

theorem phaseRunLength_le_active_at_harvest
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseRunLength j (phaseExtensionCount r t j) ≤
      phaseTop r t j - phaseExtensionCount r t j := by
  have hu := four_le_phaseTop_at_phase ht hj hjK
  unfold phaseRunLength phaseExtensionCount
  by_cases hj1 : j = 1
  · simp only [hj1, if_pos]
    have hu5 := five_le_phaseTop_one ht
    simpa only [hj1] using (show
      (phaseTop r t 1 - 5) / 2 + 2 ≤
        phaseTop r t 1 - (phaseTop r t 1 - 5) / 2 by omega)
  · simp only [if_neg hj1]
    omega

theorem phase_harvest_active_lt_stone
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseTop r t j - phaseExtensionCount r t j < towerStone r t j := by
  by_cases hj1 : j = 1
  · subst j
    have hu := five_le_phaseTop_one ht
    have hstone : towerStone r t 1 = phaseTop r t 1 + 2 := by
      rw [first_towerStone_eq]
      simp only [phaseTop_one]
      rw [phaseTop_one] at hu
      omega
    rw [hstone]
    omega
  · have hj2 : 2 ≤ j := by omega
    have hu := phaseTop_le_half_add_one_of_two_le ht hj2
    have hs := towerStone_phase_lower ht hj hjK
    omega

/-- The newborn active term at an ordinary harvest pays `r` by itself. -/
theorem newborn_binomial_pays
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 2 ≤ j) (hjK : j ≤ phaseCount r t) :
    r ≤ (towerStone r t j - 1).choose (phaseTop r t j) := by
  apply binomial_pays_of_quarter_digit hr
  · have hs := towerStone_phase_lower ht (by omega) hjK
    omega
  · have hu := four_le_phaseTop_at_phase ht (by omega) hjK
    omega
  · have hu := phaseTop_le_half_add_one_of_two_le ht hj
    have hs := towerStone_phase_lower ht (by omega) hjK
    omega

theorem phase_harvest_newborn_index
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseBirth r t j - phaseExtensionCount r t j -
        (phaseFixedDigits r t j).length - 2 =
      phaseTop r t (j + 1) := by
  rw [phase_harvest_active_index ht hj hjK,
    phaseTop_succ_eq_sub hj (four_le_phaseTop_at_phase ht hj hjK)]

/--
The ordinary harvest transition, with both the hockey-stick completion and
the newborn payment discharged.  It is used for `j+1 ≤ K`; the manuscript
replaces the last such ordinary birth by the one-digit final zone.
-/
theorem phase_harvest_valid
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j + 1 ≤ phaseCount r t)
    (hcanon : IsCanonical
      (phaseBirth r t j - phaseExtensionCount r t j)
      (phaseDigits r t j (phaseExtensionCount r t j))) :
    r + canonicalShadow
        (phaseBirth r t j - phaseExtensionCount r t j)
        (phaseState r t j (phaseExtensionCount r t j)) ≤
      phaseState r t (j + 1) 0 := by
  let ell := phaseExtensionCount r t j
  let k := phaseBirth r t j - ell
  let fixed := phaseFixedDigits r t j
  let s := towerStone r t j
  let a := towerStone r t (j + 1) - 1
  have hjK' : j ≤ phaseCount r t := by omega
  have hactive := phase_harvest_active_index ht hj hjK'
  have hrun := phaseRunLength_le_active_at_harvest ht hj hjK'
  have hactiveLt := phase_harvest_active_lt_stone hr ht hj hjK'
  have hindex := phase_harvest_newborn_index ht hj hjK'
  have hpay := newborn_binomial_pays hr ht (show 2 ≤ j + 1 by omega) hjK
  have hfixed : fixed.length + 2 ≤ k := by
    dsimp [fixed, k, ell]
    have hu := four_le_phaseTop_at_phase ht hj hjK'
    rw [length_phaseFixedDigits]
    unfold phaseBirth phaseExtensionCount
    by_cases hj1 : j = 1
    · simp only [hj1, if_pos]
      have hu5 := five_le_phaseTop_one ht
      omega
    · simp only [if_neg hj1]
      omega
  have hgeneric : r + canonicalShadow k
      (cascadeValue k (fixed ++ diagonalDigits (s - 1)
        (phaseRunLength j ell))) ≤
      cascadeValue (k - 1) (fixed ++ [s, a]) := by
    apply cascade_harvest_pays hcanon hfixed
    · rw [hactive]
      exact hrun
    · rw [hactive]
      exact hactiveLt
    · change r ≤ (towerStone r t (j + 1) - 1).choose
        (phaseBirth r t j - phaseExtensionCount r t j -
          (phaseFixedDigits r t j).length - 2)
      rw [hindex]
      exact hpay
  have hbirth : phaseBirth r t (j + 1) = k - 1 := by
    dsimp [k, ell]
    exact phaseBirth_succ ht hj hjK'
  unfold phaseState
  rw [phaseDigits_next_zero hj]
  unfold phaseDigits phaseRunDigits
  change r + canonicalShadow k
      (cascadeValue k (fixed ++ diagonalDigits (s - 1)
        (phaseRunLength j ell))) ≤
    cascadeValue (phaseBirth r t (j + 1)) (fixed ++ [s, a])
  rw [hbirth]
  exact hgeneric

end Erdos776.Uniform
