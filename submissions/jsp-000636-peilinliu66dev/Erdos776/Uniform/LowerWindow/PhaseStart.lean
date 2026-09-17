import Erdos776.Uniform.LowerWindow.PhaseCanonical

/-!
# Entry into the ordinary phase block

This is the transition (4.1)--(4.3): after shadowing the completed anchor,
the two-term run `(N-3,N-4)` pays the incoming load and becomes phase one.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

theorem phase_one_digits_at_birth (r t : ℕ) :
    phaseDigits r t 1 0 =
      anchorHeadDigits r (t + 1) ++
        diagonalDigits (towerStone r t 1 - 1) 2 := by
  unfold phaseDigits phaseFixedDigits phaseRunDigits phaseRunLength
  simp [towerDigits]

/-- The two newborn phase-one terms have total value `2N-7 ≥ r`. -/
theorem phase_one_run_pays
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    r ≤ cascadeValue (phaseTop r t 1)
      (diagonalDigits (towerStone r t 1 - 1) 2) := by
  have hu := five_le_phaseTop_one ht
  have hstone : towerStone r t 1 = phaseTop r t 1 + 2 := by
    rw [first_towerStone_eq]
    simp only [phaseTop_one]
    rw [phaseTop_one] at hu
    omega
  rw [hstone]
  simp only [diagonalDigits_succ, cascadeValue_cons]
  have hchoose1 : (phaseTop r t 1 + 2 - 1).choose (phaseTop r t 1) =
      phaseTop r t 1 + 1 := by
    rw [show phaseTop r t 1 + 2 - 1 = phaseTop r t 1 + 1 by omega]
    exact Nat.choose_succ_self_right _
  have hchoose2 : (phaseTop r t 1 + 2 - 1 - 1).choose
      (phaseTop r t 1 - 1) = phaseTop r t 1 := by
    rw [show phaseTop r t 1 + 2 - 1 - 1 = phaseTop r t 1 by omega]
    rw [Nat.choose_symm (n := phaseTop r t 1) (k := 1) (by omega),
      Nat.choose_one_right]
  rw [hchoose1, hchoose2]
  simp only [diagonalDigits_zero, cascadeValue_nil, Nat.add_zero]
  rw [phaseTop_one_eq_width ht]
  have h64 := sixtyFour_mul_phaseWidth_le ht
  omega

/-- The completed anchor feeds the first phase birth. -/
theorem completedAnchor_to_phase_one
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    r + canonicalShadow (r - t - 1) (completedAnchorValue r t) ≤
      phaseState r t 1 0 := by
  have hcanon0 := isCanonical_anchorHeadDigits
    (r := r) (q := t + 1) (show 2 * (t + 1) + 2 ≤ r by
      have h64 := sixtyFour_mul_phaseWidth_le ht
      simp [phaseWidth] at h64
      omega)
  have hcanon : IsCanonical (r - t - 1) (anchorHeadDigits r (t + 1)) := by
    simpa only [show r - (t + 1) = r - t - 1 by omega] using hcanon0
  rw [canonicalShadow_eq_cascadeShadowValue hcanon]
  · unfold phaseState
    rw [phase_one_digits_at_birth, phaseBirth_one ht, cascadeValue_append]
    unfold cascadeShadowValue
    have hindex : r - t - 2 - (anchorHeadDigits r (t + 1)).length =
        phaseTop r t 1 := by
      rw [length_anchorHeadDigits]
      have h64 := sixtyFour_mul_phaseWidth_le ht
      simp only [phaseTop_one, anchorN, phaseWidth] at h64 ⊢
      omega
    simp only [Nat.sub_zero,
      show r - t - 1 - 1 = r - t - 2 by omega]
    rw [hindex]
    simpa [Nat.add_comm] using Nat.add_le_add_left (phase_one_run_pays ht)
      (cascadeValue (r - t - 2) (anchorHeadDigits r (t + 1)))
  · rfl

end Erdos776.Uniform
