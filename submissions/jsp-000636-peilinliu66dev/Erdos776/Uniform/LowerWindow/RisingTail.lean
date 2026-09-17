import Erdos776.Uniform.LowerWindow.PhaseCapacity

/-!
# The one-digit final zone

This file formalizes Section 7.  The completed stones remain fixed while one
tail digit rises as its lower index descends from `u_K-1` to `2`.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- `D=s_{K+1}+2` from (7.1). -/
noncomputable def finalTailCeiling (r t : ℕ) : ℕ :=
  towerStone r t (phaseCount r t + 1) + 2

/-- The digit `d_p` from (7.3). -/
noncomputable def risingTailDigit (r t p : ℕ) : ℕ :=
  if p = 2 then finalTailCeiling r t
  else finalTailCeiling r t - p + 1

/-- The anchors and all completed stones `s₁,...,s_K`. -/
noncomputable def risingFixedDigits (r t : ℕ) : List ℕ :=
  phaseFixedDigits r t (phaseCount r t) ++ [towerStone r t (phaseCount r t)]

theorem length_risingFixedDigits (r t : ℕ) (hK : 1 ≤ phaseCount r t) :
    (risingFixedDigits r t).length = t + 2 + phaseCount r t := by
  simp [risingFixedDigits]
  omega

/-- At tail position `p`, the common level is `t+K+p+2`. -/
noncomputable def risingLevel (r t p : ℕ) : ℕ := t + phaseCount r t + p + 2

noncomputable def risingDigits (r t p : ℕ) : List ℕ :=
  risingFixedDigits r t ++ [risingTailDigit r t p]

noncomputable def risingState (r t p : ℕ) : ℕ :=
  cascadeValue (risingLevel r t p) (risingDigits r t p)

theorem finalTop_le_eighth_add_two
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    phaseTop r t (phaseCount r t) ≤ r / 8 + 2 := by
  have hu := finalTop_le_eight_mul_phaseWidth_add_two ht
  have h64 := sixtyFour_mul_phaseWidth_le ht
  have hwidth : 8 * phaseWidth t ≤ r / 8 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 8)).2
    omega
  omega

theorem finalTailCeiling_lower
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    r / 2 + 3 ≤ finalTailCeiling r t := by
  unfold finalTailCeiling
  have hs := towerStone_after_phases_lower ht
  omega

theorem finalTailCeiling_lt_finalStone
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    finalTailCeiling r t < towerStone r t (phaseCount r t) := by
  let K := phaseCount r t
  let c := phaseWidth t
  let p := 2 ^ (K - 1)
  have hK : 5 ≤ K := five_le_phaseCount ht
  have hpow : 2 ^ K = 2 * p := by
    dsimp [p]
    conv_lhs => rw [show K = K - 1 + 1 by omega, pow_succ]
    omega
  have hdist : c * 2 ^ K ≤ r / 2 := by
    have hlower := (phaseCount_spec ht).2.1
    dsimp [K, c, p] at hpow ⊢
    rw [hpow]
    calc
      phaseWidth t * (2 * 2 ^ (phaseCount r t - 1)) =
          2 * (phaseWidth t * 2 ^ (phaseCount r t - 1)) := by
        simp [Nat.mul_assoc, Nat.mul_comm]
      _ ≤ 2 * (r / 4) := Nat.mul_le_mul_left 2 hlower
      _ ≤ r / 2 := by omega
  have hgap : 3 ≤ c * p := by
    have hc : 3 ≤ c := by simp [c, phaseWidth]
    have hp : 0 < p := pow_pos (by omega) _
    exact (show 3 * 1 ≤ c * p from Nat.mul_le_mul hc hp)
  have hrec : towerStone r t (K + 1) =
      2 * towerStone r t K - r - 1 := by
    apply towerStone_succ (j := K) (by omega)
    exact hdist.trans (by omega)
  have hsK : towerStone r t K ≤ r - 2 := by
    unfold towerStone
    dsimp [c, p] at hgap ⊢
    omega
  unfold finalTailCeiling
  dsimp [K] at hrec hsK ⊢
  rw [hrec]
  have hsLower := towerStone_phase_lower ht (phaseCount_spec ht).1 le_rfl
  omega

theorem risingTailDigit_le_ceiling {r t p : ℕ}
    (ht : IsMaximalAnchorIndex r t) (hp : 1 ≤ p) :
    risingTailDigit r t p ≤ finalTailCeiling r t := by
  have hD := finalTailCeiling_lower ht
  unfold risingTailDigit
  by_cases h : p = 2
  · simp [h]
  · simp only [if_neg h]
    omega

theorem risingTailDigit_lt_finalStone
    {r t p : ℕ} (ht : IsMaximalAnchorIndex r t) (hp : 1 ≤ p) :
    risingTailDigit r t p < towerStone r t (phaseCount r t) :=
  (risingTailDigit_le_ceiling ht hp).trans_lt
    (finalTailCeiling_lt_finalStone ht)

theorem risingTailDigit_valid
    {r t p : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hp2 : 2 ≤ p) (hpu : p < phaseTop r t (phaseCount r t)) :
    p ≤ risingTailDigit r t p := by
  have hD := finalTailCeiling_lower ht
  have hu := finalTop_le_eighth_add_two ht
  unfold risingTailDigit
  by_cases hp : p = 2
  · simp only [hp, if_pos]
    omega
  · simp only [if_neg hp]
    omega

theorem risingLevel_sub_fixedLength (r t p : ℕ)
    (hK : 1 ≤ phaseCount r t) :
    risingLevel r t p - (risingFixedDigits r t).length = p := by
  rw [length_risingFixedDigits r t hK]
  unfold risingLevel
  omega

theorem risingLevel_le_birth
    {r t p : ℕ} (hp : p < phaseTop r t (phaseCount r t)) :
    risingLevel r t p ≤ phaseBirth r t (phaseCount r t) := by
  unfold risingLevel phaseBirth
  omega

/-- Every displayed rising-tail state is a canonical cascade. -/
theorem isCanonical_risingState
    {r t p : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hp2 : 2 ≤ p) (hpu : p < phaseTop r t (phaseCount r t)) :
    IsCanonical (risingLevel r t p) (risingDigits r t p) := by
  let K := phaseCount r t
  let fixed := phaseFixedDigits r t K
  let s := towerStone r t K
  let d := risingTailDigit r t p
  have hK : 1 ≤ K := (phaseCount_spec ht).1
  have hbirth := isCanonical_phase_birth hr ht hK le_rfl
  have hfixedBirth : IsCanonical (phaseBirth r t K) fixed := by
    apply isCanonical_append_left
    simpa [K, fixed, phaseDigits, phaseRunDigits, phaseRunLength] using hbirth
  have hlevel := risingLevel_le_birth hpu
  have hfixedLen : fixed.length ≤ risingLevel r t p := by
    rw [length_phaseFixedDigits]
    unfold risingLevel
    omega
  have hfixed : IsCanonical (risingLevel r t p) fixed :=
    hfixedBirth.lowerIndex hlevel hfixedLen
  have htailIndex : risingLevel r t p - fixed.length = p + 1 := by
    dsimp [fixed, K]
    rw [length_phaseFixedDigits]
    unfold risingLevel
    omega
  have hdValid := risingTailDigit_valid hr ht hp2 hpu
  have hsValid : p + 1 ≤ s := by
    have hs := towerStone_phase_lower ht hK le_rfl
    have hu := finalTop_le_eighth_add_two ht
    dsimp [K] at hs
    dsimp [s, K]
    omega
  have htail : IsCanonical (risingLevel r t p - fixed.length) [s, d] := by
    rw [htailIndex]
    simp only [isCanonical_succ_cons]
    refine ⟨?_, ?_, isCanonical_singleton (by omega) hdValid⟩
    · exact hsValid
    · intro b hb
      simp only [List.mem_singleton] at hb
      subst b
      dsimp [d, s, K]
      exact risingTailDigit_lt_finalStone ht (by omega)
  have hcross : ∀ a ∈ fixed, ∀ b ∈ [s, d], b < a := by
    intro a ha b hb
    have hsa := phaseFixed_digit_gt_stone ht hK le_rfl ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hsa
    · exact (risingTailDigit_lt_finalStone ht (by omega)).trans hsa
  have hfull := isCanonical_append hfixed htail hcross
  unfold risingDigits risingFixedDigits
  dsimp [fixed, s, d, K] at hfull ⊢
  simpa [List.append_assoc] using hfull

theorem risingTailDigit_step
    {r t p : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hp4 : 4 ≤ p) (hpu : p < phaseTop r t (phaseCount r t)) :
    risingTailDigit r t (p - 1) = risingTailDigit r t p + 1 := by
  have hvalid := risingTailDigit_valid hr ht (by omega) hpu
  unfold risingTailDigit at hvalid ⊢
  simp only [if_neg (show p ≠ 2 by omega),
    if_neg (show p - 1 ≠ 2 by omega)] at hvalid ⊢
  omega

theorem risingTail_gain_pays
    {r t p : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hp4 : 4 ≤ p) (hpu : p < phaseTop r t (phaseCount r t)) :
    r + (risingTailDigit r t p).choose (p - 1) ≤
      (risingTailDigit r t (p - 1)).choose (p - 1) := by
  have hstep := risingTailDigit_step hr ht hp4 hpu
  have hdValid := risingTailDigit_valid hr ht (by omega) hpu
  have hD := finalTailCeiling_lower ht
  have hu := finalTop_le_eighth_add_two ht
  have hdQuarter : r / 4 - 1 ≤ risingTailDigit r t p := by
    unfold risingTailDigit
    simp only [if_neg (show p ≠ 2 by omega)]
    omega
  have hpay : r ≤ (risingTailDigit r t p).choose (p - 2) := by
    apply binomial_pays_of_quarter_digit hr hdQuarter (by omega)
    omega
  have hpascal := Nat.choose_succ_succ (risingTailDigit r t p) (p - 2)
  have hpascal' : (risingTailDigit r t p + 1).choose (p - 1) =
      (risingTailDigit r t p).choose (p - 2) +
        (risingTailDigit r t p).choose (p - 1) := by
    simpa only [Nat.succ_eq_add_one, show p - 2 + 1 = p - 1 by omega] using hpascal
  rw [hstep, hpascal']
  simpa [Nat.add_comm, Nat.add_left_comm] using
    Nat.add_le_add_right hpay ((risingTailDigit r t p).choose (p - 1))

/-- Every ordinary `p → p-1` rise (`p ≥ 4`) is a valid supersolution step. -/
theorem risingState_step
    {r t p : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hp4 : 4 ≤ p) (hpu : p < phaseTop r t (phaseCount r t)) :
    r + canonicalShadow (risingLevel r t p) (risingState r t p) ≤
      risingState r t (p - 1) := by
  have hcanon := isCanonical_risingState hr ht (by omega) hpu
  unfold risingState
  rw [show risingLevel r t (p - 1) = risingLevel r t p - 1 by
    unfold risingLevel
    omega]
  unfold risingDigits
  unfold risingDigits at hcanon
  rw [canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold cascadeShadowValue
  rw [cascadeValue_append, cascadeValue_append]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  rw [show risingLevel r t p - 1 - (risingFixedDigits r t).length = p - 1 by
      rw [length_risingFixedDigits r t (phaseCount_spec ht).1]
      unfold risingLevel
      omega]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    Nat.add_le_add_left (risingTail_gain_pays hr ht hp4 hpu)
      (cascadeValue (risingLevel r t p - 1) (risingFixedDigits r t))

/-! ### Entry, final jump, and capacity -/

theorem risingEntryPosition_two_le
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    2 ≤ phaseTop r t (phaseCount r t) - 1 := by
  have hu := three_mul_phaseWidth_le_finalTop ht
  have hc : 3 ≤ phaseWidth t := by simp [phaseWidth]
  omega

theorem risingEntryLevel
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    risingLevel r t (phaseTop r t (phaseCount r t) - 1) =
      phaseBirth r t (phaseCount r t) := by
  unfold risingLevel phaseBirth
  have hu := risingEntryPosition_two_le ht
  omega

theorem phaseK_state_le_rising_entry
    {r t : ℕ} (_hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    phaseState r t (phaseCount r t) 0 ≤
      risingState r t (phaseTop r t (phaseCount r t) - 1) := by
  let K := phaseCount r t
  let u := phaseTop r t K
  let fixed := phaseFixedDigits r t K
  let s := towerStone r t K
  let p := u - 1
  have hK : 1 ≤ K := (phaseCount_spec ht).1
  have hK5 : 5 ≤ K := by
    dsimp [K]
    exact five_le_phaseCount ht
  have hp2 : 2 ≤ p := by
    dsimp [p, u, K]
    exact risingEntryPosition_two_le ht
  have hlevel : risingLevel r t p = phaseBirth r t K := by
    dsimp [p, u, K]
    exact risingEntryLevel ht
  have hphaseDigits : phaseDigits r t K 0 = fixed ++ [s - 1] := by
    have hK1 : K ≠ 1 := by omega
    unfold phaseDigits phaseRunDigits phaseRunLength
    simp [fixed, s, hK1]
  unfold phaseState risingState
  rw [hlevel, hphaseDigits]
  unfold risingDigits risingFixedDigits
  dsimp [fixed, s, p, u, K]
  rw [cascadeValue_append, cascadeValue_append, cascadeValue_append]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  have hindex : phaseBirth r t (phaseCount r t) -
      (phaseFixedDigits r t (phaseCount r t)).length =
      phaseTop r t (phaseCount r t) := by
    rw [length_phaseFixedDigits]
    unfold phaseBirth
    omega
  rw [hindex]
  have hmono : (towerStone r t (phaseCount r t) - 1).choose
      (phaseTop r t (phaseCount r t)) ≤
      (towerStone r t (phaseCount r t)).choose
        (phaseTop r t (phaseCount r t)) :=
    Nat.choose_le_choose _ (Nat.sub_le _ _)
  omega

/-- The special final gain `choose D 2 - choose (D-2) 2 = 2D-3`. -/
theorem risingTail_final_gain
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    r + (risingTailDigit r t 3).choose 2 ≤
      (risingTailDigit r t 2).choose 2 := by
  let D := finalTailCeiling r t
  have hD : r / 2 + 3 ≤ D := by
    dsimp [D]
    exact finalTailCeiling_lower ht
  have hD2 : 2 ≤ D := by omega
  have hd3 : risingTailDigit r t 3 = D - 2 := by
    unfold risingTailDigit
    simp only [if_neg (by omega : (3 : ℕ) ≠ 2)]
    dsimp [D] at hD ⊢
    omega
  have hd2 : risingTailDigit r t 2 = D := by
    simp [risingTailDigit, D]
  rw [hd3, hd2]
  have hp1 : D.choose 2 = (D - 1).choose 1 + (D - 1).choose 2 := by
    have h := Nat.choose_succ_succ (D - 1) 1
    simpa only [Nat.succ_eq_add_one, show D - 1 + 1 = D by omega] using h
  have hp2 : (D - 1).choose 2 =
      (D - 2).choose 1 + (D - 2).choose 2 := by
    have h := Nat.choose_succ_succ (D - 2) 1
    simpa only [Nat.succ_eq_add_one,
      show D - 2 + 1 = D - 1 by omega] using h
  rw [hp1, hp2, Nat.choose_one_right, Nat.choose_one_right]
  omega

theorem risingState_final_step
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    r + canonicalShadow (risingLevel r t 3) (risingState r t 3) ≤
      risingState r t 2 := by
  have hu := three_mul_phaseWidth_le_finalTop ht
  have hc : 3 ≤ phaseWidth t := by simp [phaseWidth]
  have hcanon := isCanonical_risingState (p := 3) hr ht (by omega) (by omega)
  unfold risingState
  rw [show risingLevel r t 2 = risingLevel r t 3 - 1 by
    unfold risingLevel
    omega]
  unfold risingDigits
  unfold risingDigits at hcanon
  rw [canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold cascadeShadowValue
  rw [cascadeValue_append, cascadeValue_append]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  have hK := (phaseCount_spec ht).1
  rw [show risingLevel r t 3 - 1 - (risingFixedDigits r t).length = 2 by
    rw [length_risingFixedDigits r t hK]
    unfold risingLevel
    omega]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    Nat.add_le_add_left (risingTail_final_gain ht)
      (cascadeValue (risingLevel r t 3 - 1) (risingFixedDigits r t))

/-- The last ordinary harvest enters the one-digit final zone. -/
theorem final_phase_harvest_to_rising
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    let K := phaseCount r t
    let j := K - 1
    r + canonicalShadow
        (phaseBirth r t j - phaseExtensionCount r t j)
        (phaseState r t j (phaseExtensionCount r t j)) ≤
      risingState r t (phaseTop r t K - 1) := by
  dsimp only
  have hK : 5 ≤ phaseCount r t := five_le_phaseCount ht
  have hharvest := phase_harvest_valid_auto hr ht
    (j := phaseCount r t - 1) (by omega)
    (show phaseCount r t - 1 + 1 ≤ phaseCount r t by omega)
  rw [show phaseCount r t - 1 + 1 = phaseCount r t by omega] at hharvest
  exact hharvest.trans (phaseK_state_le_rising_entry hr ht)

theorem risingDigits_all_lt_r3
    {r t p d : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hp : 1 ≤ p) (hd : d ∈ risingDigits r t p) :
    d < r + 3 := by
  rcases List.mem_append.mp hd with hd | hd
  · rcases List.mem_append.mp hd with hd | hd
    · rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨q, hq, rfl⟩ := mem_anchorHeadDigits
          (q := t + 1) (by
            have h64 := sixtyFour_mul_phaseWidth_le ht
            simp [phaseWidth] at h64
            omega) hd
        omega
      · obtain ⟨q, hq1, hqCount, rfl⟩ := mem_towerDigits hd
        exact (towerStone_le_r r t q).trans_lt (by omega)
    · simp only [List.mem_singleton] at hd
      subst d
      exact (towerStone_le_r r t (phaseCount r t)).trans_lt (by omega)
  · simp only [List.mem_singleton] at hd
    subst d
    exact (risingTailDigit_lt_finalStone ht hp).trans
      ((towerStone_le_r r t (phaseCount r t)).trans_lt (by omega))

theorem risingState_lt_capacity
    {r t p : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hp2 : 2 ≤ p) (hpu : p < phaseTop r t (phaseCount r t)) :
    risingState r t p < (r + 4).choose (risingLevel r t p) := by
  have hcanon := isCanonical_risingState hr ht hp2 hpu
  have hlevel : risingLevel r t p ≤ r := by
    exact (risingLevel_le_birth hpu).trans
      (phaseLevel_le_r (L := 0) ht (phaseCount_spec ht).1 le_rfl)
  have hsmall : risingState r t p < (r + 3).choose (risingLevel r t p) := by
    unfold risingState
    exact cascadeValue_lt_choose_of_all_lt (by omega) hcanon
      (fun d hd => risingDigits_all_lt_r3 ht (by omega) hd)
  exact hsmall.trans_le (Nat.choose_le_choose _ (by omega))

end Erdos776.Uniform
