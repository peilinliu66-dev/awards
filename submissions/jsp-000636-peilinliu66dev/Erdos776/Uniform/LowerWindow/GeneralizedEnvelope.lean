import Erdos776.Uniform.LowerWindow.RisingTail

/-!
# The exact generalized envelope

This is Section 8.  At level `i`, `envelopeCount t i = i-t-4` tower stones
have been completed, and the terminal position-two digit is the next stone
plus two.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

def envelopeCount (t i : ℕ) : ℕ := i - t - 4

def generalizedEnvelopeDigits (r t i : ℕ) : List ℕ :=
  anchorHeadDigits r (t + 1) ++ towerDigits r t (envelopeCount t i) ++
    [towerStone r t (envelopeCount t i + 1) + 2]

def generalizedEnvelopeState (r t i : ℕ) : ℕ :=
  cascadeValue i (generalizedEnvelopeDigits r t i)

theorem envelope_level_eq
    {t i : ℕ} (hi : t + 4 ≤ i) :
    i = t + envelopeCount t i + 4 := by
  unfold envelopeCount
  omega

theorem envelopeCount_pos
    {t i : ℕ} (hi : t + 5 ≤ i) : 1 ≤ envelopeCount t i := by
  unfold envelopeCount
  omega

theorem envelopeCount_le_phaseCount
    {r t i : ℕ} (hi : i ≤ t + phaseCount r t + 4) :
    envelopeCount t i ≤ phaseCount r t := by
  unfold envelopeCount
  omega

theorem generalizedEnvelopeDigits_eq_phaseFixed
    {r t i : ℕ} (hi : t + 5 ≤ i) :
    generalizedEnvelopeDigits r t i =
      phaseFixedDigits r t (envelopeCount t i) ++
        [towerStone r t (envelopeCount t i),
          towerStone r t (envelopeCount t i + 1) + 2] := by
  let m := envelopeCount t i
  have hm : 1 ≤ m := envelopeCount_pos hi
  unfold generalizedEnvelopeDigits phaseFixedDigits
  rw [show envelopeCount t i = (envelopeCount t i - 1) + 1 by omega,
    towerDigits_succ, show envelopeCount t i - 1 + 1 = envelopeCount t i by omega]
  simp [List.append_assoc]

theorem towerStone_succ_add_two_lt
    {r t m : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hm : 1 ≤ m) (hmK : m ≤ phaseCount r t) :
    towerStone r t (m + 1) + 2 < towerStone r t m := by
  have hK : 1 ≤ phaseCount r t := (phaseCount_spec ht).1
  have hpowK : 2 ^ phaseCount r t =
      2 * 2 ^ (phaseCount r t - 1) := by
    conv_lhs => rw [show phaseCount r t = phaseCount r t - 1 + 1 by omega,
      pow_succ]
    omega
  have hpow : 2 ^ m ≤ 2 ^ phaseCount r t :=
    pow_le_pow_right' (by omega) hmK
  have hdistK : phaseWidth t * 2 ^ phaseCount r t ≤ r / 2 := by
    rw [hpowK]
    calc
      phaseWidth t * (2 * 2 ^ (phaseCount r t - 1)) =
          2 * (phaseWidth t * 2 ^ (phaseCount r t - 1)) := by
        simp [Nat.mul_assoc, Nat.mul_comm]
      _ ≤ 2 * (r / 4) :=
        Nat.mul_le_mul_left 2 (phaseCount_spec ht).2.1
      _ ≤ r / 2 := by omega
  have hdist : phaseWidth t * 2 ^ m ≤ r / 2 :=
    (Nat.mul_le_mul_left _ hpow).trans hdistK
  have hrec := towerStone_succ (r := r) (t := t) (j := m) hm
    (hdist.trans (by omega))
  have hgap : 3 ≤ phaseWidth t * 2 ^ (m - 1) := by
    have hc : 3 ≤ phaseWidth t := by simp [phaseWidth]
    have hp : 0 < 2 ^ (m - 1) := pow_pos (by omega) _
    exact Nat.mul_le_mul hc hp
  have hs : towerStone r t m ≤ r - 2 := by
    unfold towerStone
    omega
  have hsLower := towerStone_phase_lower ht hm hmK
  omega

/-- Every generalized-envelope display is canonical in its stated range. -/
theorem isCanonical_generalizedEnvelope
    {r t i : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hiLower : t + 5 ≤ i) (hiUpper : i ≤ t + phaseCount r t + 4) :
    IsCanonical i (generalizedEnvelopeDigits r t i) := by
  let m := envelopeCount t i
  let fixed := phaseFixedDigits r t m
  let s := towerStone r t m
  let d := towerStone r t (m + 1) + 2
  have hm : 1 ≤ m := envelopeCount_pos hiLower
  have hmK : m ≤ phaseCount r t := envelopeCount_le_phaseCount hiUpper
  have hbirth := isCanonical_phase_birth hr ht hm hmK
  have hfixedBirth : IsCanonical (phaseBirth r t m) fixed := by
    apply isCanonical_append_left
    simpa [m, fixed, phaseDigits] using hbirth
  have hiEq : i = t + m + 4 := by
    dsimp [m]
    exact envelope_level_eq (by omega)
  have hiBirth : i ≤ phaseBirth r t m := by
    rw [hiEq]
    unfold phaseBirth
    have hu := four_le_phaseTop_at_phase ht hm hmK
    omega
  have hfixedLen : fixed.length ≤ i := by
    dsimp [fixed]
    rw [length_phaseFixedDigits, hiEq]
    omega
  have hfixed : IsCanonical i fixed :=
    hfixedBirth.lowerIndex hiBirth hfixedLen
  have htailIndex : i - fixed.length = 3 := by
    dsimp [fixed]
    rw [length_phaseFixedDigits, hiEq]
    omega
  have hsd : d < s := by
    dsimp [d, s, m]
    exact towerStone_succ_add_two_lt ht hm hmK
  have hsLower := towerStone_phase_lower ht hm hmK
  have htail : IsCanonical (i - fixed.length) [s, d] := by
    rw [htailIndex]
    norm_num [IsCanonical]
    omega
  have hcross : ∀ a ∈ fixed, ∀ b ∈ [s, d], b < a := by
    intro a ha b hb
    have hsa := phaseFixed_digit_gt_stone ht hm hmK ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hsa
    · exact hsd.trans hsa
  have hfull := isCanonical_append hfixed htail hcross
  rw [generalizedEnvelopeDigits_eq_phaseFixed hiLower]
  simpa [m, fixed, s, d] using hfull

theorem generalizedEnvelope_top_eq_rising
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    generalizedEnvelopeState r t (t + phaseCount r t + 4) =
      risingState r t 2 := by
  unfold generalizedEnvelopeState risingState
  have hcount : envelopeCount t (t + phaseCount r t + 4) =
      phaseCount r t := by
    unfold envelopeCount
    omega
  have hlevel : risingLevel r t 2 = t + phaseCount r t + 4 := by
    unfold risingLevel
    omega
  rw [hlevel]
  have hK := five_le_phaseCount ht
  rw [generalizedEnvelopeDigits_eq_phaseFixed (show
    t + 5 ≤ t + phaseCount r t + 4 by omega)]
  rw [hcount]
  unfold risingDigits risingFixedDigits risingTailDigit finalTailCeiling
  simp [List.append_assoc]

theorem envelope_stone_recurrence
    {r t m : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hm : 1 ≤ m) (hmK : m ≤ phaseCount r t) :
    towerStone r t (m + 1) = 2 * towerStone r t m - r - 1 := by
  have hpow : phaseWidth t * 2 ^ m ≤ r / 2 := by
    have hKm : 2 ^ m ≤ 2 ^ phaseCount r t :=
      pow_le_pow_right' (a := 2) (by omega) hmK
    have hpowK : 2 ^ phaseCount r t =
        2 * 2 ^ (phaseCount r t - 1) := by
      conv_lhs => rw [show phaseCount r t = phaseCount r t - 1 + 1 by
        have := (phaseCount_spec ht).1
        omega, pow_succ]
      omega
    calc
      phaseWidth t * 2 ^ m ≤ phaseWidth t * 2 ^ phaseCount r t :=
        Nat.mul_le_mul_left _ hKm
      _ = 2 * (phaseWidth t * 2 ^ (phaseCount r t - 1)) := by
        rw [hpowK]
        simp [Nat.mul_assoc, Nat.mul_comm]
      _ ≤ 2 * (r / 4) :=
        Nat.mul_le_mul_left 2 (phaseCount_spec ht).2.1
      _ ≤ r / 2 := by omega
  exact towerStone_succ hm (hpow.trans (by omega))

theorem envelope_bottom_gain
    {r t m : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hm : 1 ≤ m) (hmK : m ≤ phaseCount r t) :
    r + (towerStone r t m).choose 2 +
        (towerStone r t (m + 1) + 2) =
      (towerStone r t m + 2).choose 2 := by
  let s := towerStone r t m
  let sn := towerStone r t (m + 1)
  have hrec : sn = 2 * s - r - 1 := by
    dsimp [sn, s]
    exact envelope_stone_recurrence ht hm hmK
  have hs := towerStone_phase_lower ht hm hmK
  have hp1 : (s + 1).choose 2 = s + s.choose 2 := by
    simpa [Nat.choose_one_right] using Nat.choose_succ_succ s 1
  have hp2 : (s + 2).choose 2 = s + 1 + (s + 1).choose 2 := by
    simpa [Nat.choose_one_right] using Nat.choose_succ_succ (s + 1) 1
  change r + s.choose 2 + (sn + 2) = (s + 2).choose 2
  rw [hp2, hp1]
  omega

/-- The exact envelope recurrence (8.2). -/
theorem generalizedEnvelope_step
    {r t i : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hiLower : t + 6 ≤ i) (hiUpper : i ≤ t + phaseCount r t + 4) :
    generalizedEnvelopeState r t (i - 1) =
      r + canonicalShadow i (generalizedEnvelopeState r t i) := by
  let m := envelopeCount t i
  let fixed := phaseFixedDigits r t m
  let s := towerStone r t m
  let d := towerStone r t (m + 1) + 2
  have hm : 2 ≤ m := by
    dsimp [m]
    unfold envelopeCount
    omega
  have hmK : m ≤ phaseCount r t := envelopeCount_le_phaseCount hiUpper
  have hiEq : i = t + m + 4 := by
    dsimp [m]
    exact envelope_level_eq (by omega)
  have holdDigits : generalizedEnvelopeDigits r t i = fixed ++ [s, d] := by
    dsimp [fixed, s, d, m]
    exact generalizedEnvelopeDigits_eq_phaseFixed (by omega)
  have hnewCount : envelopeCount t (i - 1) = m - 1 := by
    dsimp [m]
    unfold envelopeCount
    omega
  have hnewDigits : generalizedEnvelopeDigits r t (i - 1) =
      fixed ++ [s + 2] := by
    unfold generalizedEnvelopeDigits
    rw [hnewCount]
    dsimp [fixed, s, m]
    unfold phaseFixedDigits
    rw [show envelopeCount t i - 1 + 1 = envelopeCount t i by omega]
  have hcanon := isCanonical_generalizedEnvelope hr ht (by omega) hiUpper
  rw [holdDigits] at hcanon
  unfold generalizedEnvelopeState
  rw [holdDigits, hnewDigits,
    canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold cascadeShadowValue
  rw [cascadeValue_append, cascadeValue_append]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  have hindex : i - 1 - fixed.length = 2 := by
    dsimp [fixed]
    rw [length_phaseFixedDigits, hiEq]
    omega
  rw [hindex]
  have hgain := envelope_bottom_gain ht (by omega) hmK
  norm_num [Nat.choose_one_right]
  dsimp [s, d] at hgain ⊢
  omega

theorem generalizedEnvelopeState_lt_capacity
    {r t i : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hiLower : t + 5 ≤ i) (hiUpper : i ≤ t + phaseCount r t + 4) :
    generalizedEnvelopeState r t i < (r + 4).choose i := by
  have hcanon := isCanonical_generalizedEnvelope hr ht hiLower hiUpper
  have hall : ∀ d ∈ generalizedEnvelopeDigits r t i, d < r + 3 := by
    intro d hd
    rw [generalizedEnvelopeDigits_eq_phaseFixed hiLower] at hd
    rcases List.mem_append.mp hd with hd | hd
    · unfold phaseFixedDigits at hd
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨q, hq, rfl⟩ := mem_anchorHeadDigits
          (q := t + 1) (by
            have h64 := sixtyFour_mul_phaseWidth_le ht
            simp [phaseWidth] at h64
            omega) hd
        omega
      · obtain ⟨q, hq1, hqCount, rfl⟩ := mem_towerDigits hd
        exact (towerStone_le_r r t q).trans_lt (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact (towerStone_le_r r t (envelopeCount t i)).trans_lt (by omega)
      · have hs := towerStone_le_r r t (envelopeCount t i + 1)
        omega
  have hlevel : i ≤ r + 3 := by
    let m := envelopeCount t i
    have hm1 : 1 ≤ m := envelopeCount_pos hiLower
    have hmK : m ≤ phaseCount r t := envelopeCount_le_phaseCount hiUpper
    have hb := phaseLevel_le_r (L := 0) ht hm1 hmK
    have hiEq : i = t + m + 4 := by
      dsimp [m]
      exact envelope_level_eq (by omega)
    have hu := four_le_phaseTop_at_phase ht hm1 hmK
    have hiBirth : i ≤ phaseBirth r t m := by
      rw [hiEq]
      unfold phaseBirth
      omega
    exact hiBirth.trans (hb.trans (by omega))
  have hsmall : generalizedEnvelopeState r t i < (r + 3).choose i := by
    unfold generalizedEnvelopeState
    exact cascadeValue_lt_choose_of_all_lt hlevel hcanon hall
  exact hsmall.trans_le (Nat.choose_le_choose _ (by omega))

end Erdos776.Uniform
