import Erdos776.Uniform.LowerWindow.PhaseStart

/-!
# Capacity of the ordinary phase states

Every displayed phase cascade has all digits below `r+3`.  Together with
canonicity, this puts its value below the `(r+3)`-ground-set level and hence
below the required `(r+4)` capacity.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

theorem towerStone_le_r (r t j : ℕ) : towerStone r t j ≤ r := by
  have hc : 0 < phaseWidth t := by simp [phaseWidth]
  have hp : 0 < 2 ^ (j - 1) := pow_pos (by omega) _
  have hprod : 0 < phaseWidth t * 2 ^ (j - 1) := Nat.mul_pos hc hp
  unfold towerStone
  omega

theorem phaseDigits_all_lt_r3
    {r t j L d : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hd : d ∈ phaseDigits r t j L) :
    d < r + 3 := by
  rcases List.mem_append.mp hd with hd | hd
  · rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨q, hq, rfl⟩ := mem_anchorHeadDigits
        (q := t + 1) (by
          have h64 := sixtyFour_mul_phaseWidth_le ht
          simp [phaseWidth] at h64
          omega) hd
      omega
    · obtain ⟨q, hq1, hqCount, rfl⟩ := mem_towerDigits hd
      exact (towerStone_le_r r t q).trans_lt (by omega)
  · have hdLe := mem_diagonalDigits_le hd
    exact hdLe.trans_lt (by
      have hs := towerStone_le_r r t j
      omega)

theorem phaseBirth_le_phaseBirth_one
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseBirth r t j ≤ phaseBirth r t 1 := by
  induction j, hj using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih =>
      have hjK' : j ≤ phaseCount r t := by omega
      rw [phaseBirth_succ ht hj hjK']
      exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (ih hjK'))

theorem phaseLevel_le_r
    {r t j L : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseBirth r t j - L ≤ r := by
  exact (Nat.sub_le _ _).trans
    ((phaseBirth_le_phaseBirth_one ht hj hjK).trans (by
      rw [phaseBirth_one ht]
      omega))

/-- Every state in every ordinary phase fits the required level capacity. -/
theorem phaseState_lt_capacity
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L ≤ phaseExtensionCount r t j) :
    phaseState r t j L < (r + 4).choose (phaseBirth r t j - L) := by
  have hcanon := isCanonical_phase_state hr ht hj hjK hL
  have hlevel := phaseLevel_le_r (L := L) ht hj hjK
  have hsmall : phaseState r t j L <
      (r + 3).choose (phaseBirth r t j - L) := by
    unfold phaseState
    exact cascadeValue_lt_choose_of_all_lt (by omega) hcanon
      (fun d hd => phaseDigits_all_lt_r3 ht hd)
  exact hsmall.trans_le (Nat.choose_le_choose _ (by omega))

end Erdos776.Uniform
