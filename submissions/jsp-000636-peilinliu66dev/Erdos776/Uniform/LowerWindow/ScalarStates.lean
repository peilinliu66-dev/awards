import Erdos776.Uniform.LowerWindow.GeneralizedEnvelope
import Erdos776.Uniform.LowerWindow.FinalLevels

/-!
# Semantic scalar-collapse states

The scalar recurrence was proved in `ScalarCollapse.lean`.  Here `F_q(z)` is
represented by its actual canonical-cascade digit list, the envelope collision
is checked, and one scalar recurrence step is evaluated through
`canonicalShadow`.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- The digit list representing `F_q(z)` from (9.1). -/
def scalarDigits (r q z : ℕ) : List ℕ :=
  anchorHeadDigits r q ++ [r - 2 * q + 1] ++ canonicalDigits 2 z

def scalarState (r q z : ℕ) : ℕ :=
  cascadeValue (q + 4) (scalarDigits r q z)

theorem scalarState_value (r q z : ℕ) :
    scalarState r q z =
      cascadeValue (q + 4) (anchorHeadDigits r q) +
        (r - 2 * q + 1).choose 3 + z := by
  unfold scalarState scalarDigits
  rw [cascadeValue_append, cascadeValue_append]
  rw [length_anchorHeadDigits]
  have hidx3 : q + 4 - (q + 1) = 3 := by omega
  rw [hidx3]
  simp only [cascadeValue_cons, cascadeValue_nil,
    Nat.add_zero]
  rw [List.length_append, length_anchorHeadDigits, List.length_singleton]
  have hidx2 : q + 4 - (q + 1 + 1) = 2 := by omega
  rw [hidx2, cascadeValue_canonicalDigits (by omega)]

@[simp] theorem scalarState_zero_residual (r q : ℕ) :
    scalarState r q 0 =
      cascadeValue (q + 4) (anchorHeadDigits r q) +
        (r - 2 * q + 1).choose 3 := by
  rw [scalarState_value]
  omega

theorem scalarState_bottom_eq_finalFour (r z : ℕ) :
    scalarState r 0 z = finalFourState r z := by
  rw [scalarState_value]
  unfold finalFourState
  simp [anchorHeadDigits, cascadeValue]

theorem envelope_bottom_digits
    {r t : ℕ} :
    generalizedEnvelopeDigits r t (t + 5) =
      anchorHeadDigits r t ++
        [anchorN r t, towerStone r t 1, towerStone r t 2 + 2] := by
  have hcount : envelopeCount t (t + 5) = 1 := by
    unfold envelopeCount
    omega
  rw [generalizedEnvelopeDigits_eq_phaseFixed (r := r) (by omega), hcount]
  simp [phaseFixedDigits, towerDigits, anchorHeadDigits, anchorN,
    List.append_assoc]

/-- Section 9: the extra anchors collide exactly to `F_t(0)`. -/
theorem generalizedEnvelope_collision
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    scalarState r t 0 =
      r + canonicalShadow (t + 5) (generalizedEnvelopeState r t (t + 5)) := by
  have hK := five_le_phaseCount ht
  have hcanon := isCanonical_generalizedEnvelope hr ht (by omega)
    (show t + 5 ≤ t + phaseCount r t + 4 by omega)
  have hdigits := envelope_bottom_digits (r := r) (t := t)
  rw [hdigits] at hcanon
  unfold generalizedEnvelopeState
  rw [hdigits, canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold cascadeShadowValue scalarState scalarDigits
  have hanchor : anchorHeadDigits r (t + 1) =
      anchorHeadDigits r t ++ [anchorN r t] := by
    rw [anchorHeadDigits]
    rfl
  have hscalarZero : canonicalDigits 2 0 = [] := by simp
  rw [hscalarZero]
  simp only [List.append_nil]
  rw [show t + 5 - 1 = t + 4 by omega]
  rw [cascadeValue_append, cascadeValue_append]
  have hlen : (anchorHeadDigits r t).length = t + 1 :=
    length_anchorHeadDigits r t
  rw [hlen]
  have hidxNew : t + 4 - (t + 1) = 3 := by omega
  rw [hidxNew]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  have hN : towerStone r t 1 + 2 = anchorN r t := by
    rw [first_towerStone_eq]
    have hu := five_le_phaseTop_one ht
    rw [phaseTop_one] at hu
    omega
  have hgain := envelope_bottom_gain ht (m := 1) (by omega)
    (show 1 ≤ phaseCount r t from (phaseCount_spec ht).1)
  rw [hN] at hgain
  norm_num at hgain
  have hpascal : (anchorN r t + 1).choose 3 =
      (anchorN r t).choose 2 + (anchorN r t).choose 3 := by
    simpa using Nat.choose_succ_succ (anchorN r t) 2
  have hspecial : r - 2 * t + 1 = anchorN r t + 1 := by
    unfold anchorN
    have h64 := sixtyFour_mul_phaseWidth_le ht
    simp [phaseWidth] at h64
    omega
  rw [hspecial, hpascal]
  norm_num [Nat.choose_one_right]
  omega

theorem anchorHeadDigits_pred_append
    {r q : ℕ} (hq : 1 ≤ q) :
    anchorHeadDigits r q =
      anchorHeadDigits r (q - 1) ++ [r - 2 * (q - 1)] := by
  conv_lhs => rw [show q = (q - 1) + 1 by omega, anchorHeadDigits]

/-- One semantic scalar transition, assuming the displayed old state is canonical. -/
theorem scalarState_step
    {r t q : ℕ} (hq : 1 ≤ q) (hqt : q ≤ t) (hqr : 2 * q ≤ r)
    (hcanon : IsCanonical (q + 4)
      (scalarDigits r q (scalarResidual t q))) :
    scalarState r (q - 1) (scalarResidual t (q - 1)) =
      r + canonicalShadow (q + 4) (scalarState r q (scalarResidual t q)) := by
  let a := r - 2 * q + 2
  let z := scalarResidual t q
  let z' := scalarResidual t (q - 1)
  let fixed := anchorHeadDigits r (q - 1)
  have hanchor := anchorHeadDigits_pred_append (r := r) hq
  have ha : r - 2 * (q - 1) = a := by
    dsimp [a]
    omega
  have hspecialOld : r - 2 * q + 1 = a - 1 := by
    dsimp [a]
  have hspecialNew : r - 2 * (q - 1) + 1 = a + 1 := by
    dsimp [a]
    omega
  have hzstep : z' = 2 * q - 1 + canonicalShadow 2 z := by
    dsimp [z', z]
    exact scalarResidual_step hq hqt
  have hcanon' : IsCanonical (q + 4)
      (fixed ++ [a, a - 1] ++ canonicalDigits 2 z) := by
    dsimp only [fixed, z]
    unfold scalarDigits at hcanon
    rw [hanchor, ha, hspecialOld] at hcanon
    simpa [List.append_assoc] using hcanon
  unfold scalarState scalarDigits
  rw [hanchor, ha, hspecialOld]
  simp only [List.append_assoc]
  have hcanon'' : IsCanonical (q + 4)
      (fixed ++ ([a] ++ ([a - 1] ++ canonicalDigits 2 z))) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hcanon'
  change cascadeValue (q - 1 + 4)
      (fixed ++ ([a + 1] ++ canonicalDigits 2 z')) =
    r + canonicalShadow (q + 4)
      (cascadeValue (q + 4)
        (fixed ++ ([a] ++ ([a - 1] ++ canonicalDigits 2 z))))
  rw [canonicalShadow_eq_cascadeShadowValue hcanon'' rfl]
  unfold cascadeShadowValue
  rw [cascadeValue_append (q - 1 + 4) fixed
      ([a + 1] ++ canonicalDigits 2 z')]
  rw [cascadeValue_append (q + 4 - 1) fixed
      ([a] ++ ([a - 1] ++ canonicalDigits 2 z))]
  have hlen : fixed.length = q := by
    dsimp [fixed]
    rw [length_anchorHeadDigits]
    omega
  rw [hlen]
  have hidx : q + 4 - 1 - q = 3 := by omega
  have hidxNew : q - 1 + 4 - q = 3 := by omega
  rw [hidx, hidxNew]
  change cascadeValue (q - 1 + 4) fixed +
      ((a + 1).choose 3 + cascadeValue 2 (canonicalDigits 2 z')) =
    r + (cascadeValue (q + 4 - 1) fixed +
      (a.choose 3 + ((a - 1).choose 2 +
        cascadeValue 1 (canonicalDigits 2 z))))
  rw [cascadeValue_canonicalDigits (by omega)]
  have hzshadow : cascadeValue 1 (canonicalDigits 2 z) = canonicalShadow 2 z := rfl
  rw [hzshadow, hzstep]
  have hp1 : (a + 1).choose 3 = a.choose 2 + a.choose 3 := by
    simpa using Nat.choose_succ_succ a 2
  have hp2 : a.choose 2 = (a - 1) + (a - 1).choose 2 := by
    have haPos : 1 ≤ a := by
      dsimp [a]
      omega
    have h := Nat.choose_succ_succ (a - 1) 1
    have hasucc : (a - 1).succ = a := by omega
    rw [hasucc] at h
    simpa [Nat.choose_one_right] using h
  have hfixedIndex : q - 1 + 4 = q + 4 - 1 := by omega
  have har : a - 1 + (2 * q - 1) = r := by
    dsimp [a]
    omega
  rw [hp1, hp2]
  rw [hfixedIndex]
  omega

/-! ### Canonicity and capacity of the scalar states -/

theorem scalarResidual_five_four_three_bounds
    {t : ℕ} (ht : 6 ≤ t) :
    scalarResidual t 5 ≤ 20 ∧
      scalarResidual t 4 ≤ 16 ∧ scalarResidual t 3 ≤ 14 := by
  have hz6 := scalarResidual_le_sq (t := t) (q := 6) (by omega) ht
  have hs6 := canonicalShadow_mono 2 (by omega) hz6
  rw [show (6 : ℕ) ^ 2 = 36 by norm_num,
    canonicalShadow_two_thirtySix] at hs6
  have hz5 : scalarResidual t 5 ≤ 20 := by
    rw [show 5 = 6 - 1 by omega,
      scalarResidual_step (q := 6) (by omega) ht]
    omega
  have hs5 := canonicalShadow_mono 2 (by omega) hz5
  rw [canonicalShadow_two_twenty] at hs5
  have hz4 : scalarResidual t 4 ≤ 16 := by
    rw [show 4 = 5 - 1 by omega,
      scalarResidual_step (q := 5) (by omega) (by omega)]
    omega
  have hs4 := canonicalShadow_mono 2 (by omega) hz4
  rw [canonicalShadow_two_sixteen] at hs4
  have hz3 : scalarResidual t 3 ≤ 14 := by
    rw [show 3 = 4 - 1 by omega,
      scalarResidual_step (q := 4) (by omega) (by omega)]
    omega
  exact ⟨hz5, hz4, hz3⟩

theorem scalarResidual_le_thirtySix
    {t q : ℕ} (ht : 1 ≤ t) (hqt : q ≤ t) (hq : q ≤ 5) :
    scalarResidual t q ≤ 36 := by
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [scalarResidual_zero t ht]
    by_cases ht1 : t = 1
    · simp [ht1]
    by_cases ht2 : t = 2
    · simp [ht2]
    · simp [ht1, ht2]
  · by_cases ht1 : t = 1
    · subst t
      simp
    have ht2 : 2 ≤ t := by omega
    by_cases ht2' : t = 2
    · subst t
      rw [show 1 = 2 - 1 by omega,
        scalarResidual_step (q := 2) (by omega) (by omega),
        scalarResidual_top]
      simp
    have ht3 : 3 ≤ t := by omega
    have hz2 := (scalarResidual_two_bounds ht3).2
    have hs2 := canonicalShadow_mono 2 (by omega) hz2
    rw [canonicalShadow_two_eleven] at hs2
    rw [show 1 = 2 - 1 by omega,
      scalarResidual_step (q := 2) (by omega) (by omega)]
    omega
  · by_cases ht2 : t = 2
    · subst t
      simp
    exact (scalarResidual_two_bounds (by omega)).2.trans (by omega)
  · by_cases ht3 : t = 3
    · subst t
      simp
    by_cases ht4 : t = 4
    · subst t
      rw [show 3 = 4 - 1 by omega,
        scalarResidual_step (q := 4) (by omega) (by omega),
        scalarResidual_top]
      simp
    by_cases ht5 : t = 5
    · subst t
      have hz4 : scalarResidual 5 4 = 9 := by
        rw [show 4 = 5 - 1 by omega,
          scalarResidual_step (q := 5) (by omega) (by omega),
          scalarResidual_top]
        simp
      rw [show 3 = 4 - 1 by omega,
        scalarResidual_step (q := 4) (by omega) (by omega), hz4,
        canonicalShadow_two_nine]
      omega
    exact (scalarResidual_five_four_three_bounds (by omega)).2.2.trans
      (by omega)
  · by_cases ht4 : t = 4
    · subst t
      simp
    by_cases ht5 : t = 5
    · subst t
      rw [show 4 = 5 - 1 by omega,
        scalarResidual_step (q := 5) (by omega) (by omega),
        scalarResidual_top]
      simp
    exact (scalarResidual_five_four_three_bounds (by omega)).2.1.trans
      (by omega)
  · by_cases ht5 : t = 5
    · subst t
      simp
    exact (scalarResidual_five_four_three_bounds (by omega)).1.trans
      (by omega)

theorem scalarResidual_lt_special_choose_two
    {r t q : ℕ} (ht : IsMaximalAnchorIndex r t) (hqt : q ≤ t) :
    scalarResidual t q < (r - 2 * q + 1).choose 2 := by
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp [phaseWidth] at h64
  by_cases hq6 : 6 ≤ q
  · have hz := scalarResidual_le_sq hq6 hqt
    have hquad := choose_two_mul_gt_sq (show 2 ≤ q by omega)
    have hspecial : 2 * q ≤ r - 2 * q + 1 := by omega
    exact hz.trans_lt (hquad.trans_le (Nat.choose_le_choose 2 hspecial))
  · have hz := scalarResidual_le_thirtySix ht.1 hqt (by omega)
    have hspecial : 10 ≤ r - 2 * q + 1 := by omega
    have hchoose := Nat.choose_le_choose 2 hspecial
    have hbase : 36 < (10 : ℕ).choose 2 := by norm_num [Nat.choose]
    exact hz.trans_lt (hbase.trans_le hchoose)

theorem isCanonical_scalarDigits
    {r t q : ℕ} (ht : IsMaximalAnchorIndex r t) (hqt : q ≤ t) :
    IsCanonical (q + 4) (scalarDigits r q (scalarResidual t q)) := by
  let s := r - 2 * q + 1
  let tail := canonicalDigits 2 (scalarResidual t q)
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp [phaseWidth] at h64
  have hrq : 2 * q + 4 ≤ r := by omega
  have hheadHigh := isCanonical_anchorHeadDigits
    (r := r) (q := q) (show 2 * q + 2 ≤ r by omega)
  have hhead : IsCanonical (q + 4) (anchorHeadDigits r q) := by
    apply hheadHigh.lowerIndex (by omega)
    rw [length_anchorHeadDigits]
    omega
  have hresLt : scalarResidual t q < s.choose 2 := by
    dsimp [s]
    exact scalarResidual_lt_special_choose_two ht hqt
  have htailDigits : IsCanonical 2 tail := by
    dsimp [tail]
    exact isCanonical_canonicalDigits (by omega)
  have htailLt : ∀ d ∈ tail, d < s := by
    dsimp [tail]
    exact canonicalDigits_all_lt (by omega) hresLt
  have hs3 : 3 ≤ s := by
    dsimp [s]
    omega
  have htail : IsCanonical 3 (s :: tail) := by
    rw [isCanonical_succ_cons]
    exact ⟨hs3, htailLt, htailDigits⟩
  have hcross : ∀ a ∈ anchorHeadDigits r q, ∀ b ∈ s :: tail, b < a := by
    intro a ha b hb
    obtain ⟨j, hj, rfl⟩ := mem_anchorHeadDigits
      (q := q) (show 2 * q ≤ r by omega) ha
    have hba : b < s + 1 := by
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · exact (htailLt b hb).trans_le (by omega)
    dsimp [s] at hba ⊢
    omega
  unfold scalarDigits
  simp only [List.append_assoc]
  change IsCanonical (q + 4)
    (anchorHeadDigits r q ++ (s :: tail))
  apply isCanonical_append hhead
  · simpa [length_anchorHeadDigits] using htail
  · exact hcross

theorem scalarState_lt_capacity
    {r t q : ℕ} (ht : IsMaximalAnchorIndex r t) (hqt : q ≤ t) :
    scalarState r q (scalarResidual t q) < (r + 4).choose (q + 4) := by
  have hcanon := isCanonical_scalarDigits ht hqt
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp [phaseWidth] at h64
  have hlevel : q + 4 ≤ r + 3 := by omega
  have hall : ∀ d ∈ scalarDigits r q (scalarResidual t q), d < r + 3 := by
    intro d hd
    unfold scalarDigits at hd
    simp only [List.append_assoc] at hd
    change d ∈ anchorHeadDigits r q ++
      ((r - 2 * q + 1) :: canonicalDigits 2 (scalarResidual t q)) at hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨j, hj, rfl⟩ := mem_anchorHeadDigits
        (q := q) (by omega) hd
      omega
    · rcases List.mem_cons.mp hd with rfl | hd
      · omega
      · have hlt := canonicalDigits_all_lt (k := 2)
          (m := scalarResidual t q) (A := r - 2 * q + 1)
          (by omega) (scalarResidual_lt_special_choose_two ht hqt) d hd
        omega
  have hsmall : scalarState r q (scalarResidual t q) <
      (r + 3).choose (q + 4) := by
    unfold scalarState
    exact cascadeValue_lt_choose_of_all_lt hlevel hcanon hall
  exact hsmall.trans_le (Nat.choose_le_choose _ (by omega))

/-- The scalar recurrence with all semantic side conditions discharged. -/
theorem scalarState_step_auto
    {r t q : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hq : 1 ≤ q) (hqt : q ≤ t) :
    scalarState r (q - 1) (scalarResidual t (q - 1)) =
      r + canonicalShadow (q + 4)
        (scalarState r q (scalarResidual t q)) := by
  apply scalarState_step hq hqt
  · have h64 := sixtyFour_mul_phaseWidth_le ht
    simp [phaseWidth] at h64
    omega
  · exact isCanonical_scalarDigits ht hqt

end Erdos776.Uniform
