import Erdos776.Uniform.LowerWindow.Anchors

/-!
# The scalar bottom collapse

This file isolates Section 10.  It proves the small residual recurrence and
its terminal value independently of the phase construction that feeds it.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

theorem choose_two_mul_gt_sq {q : ℕ} (hq : 2 ≤ q) :
    q ^ 2 < (2 * q).choose 2 := by
  have hchoose : (2 * q).choose 2 = q * (2 * q - 1) := by
    rw [Nat.choose_two_right]
    calc
      2 * q * (2 * q - 1) / 2 =
          2 * (q * (2 * q - 1)) / 2 := by
            apply congrArg (fun n : ℕ => n / 2)
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = q * (2 * q - 1) := Nat.mul_div_cancel_left _ (by omega)
  rw [hchoose, pow_two]
  have hsplit : 2 * q - 1 = q + (q - 1) := by omega
  rw [hsplit, Nat.mul_add]
  have hpositive : 0 < q * (q - 1) := Nat.mul_pos (by omega) (by omega)
  omega

theorem cascadeShadowValue_two_le
    {q : ℕ} {digits : List ℕ}
    (hlen : digits.length ≤ 2)
    (hall : ∀ d ∈ digits, d < 2 * q) :
    cascadeShadowValue 2 digits ≤ 2 * q := by
  cases digits with
  | nil => simp
  | cons a tail =>
      cases tail with
      | nil =>
          have ha := hall a List.mem_cons_self
          simp [cascadeShadowValue, cascadeValue, Nat.choose_one_right]
          omega
      | cons b tail =>
          cases tail with
          | nil =>
              have ha := hall a List.mem_cons_self
              simp [cascadeShadowValue, cascadeValue, Nat.choose_one_right]
              omega
          | cons c tail => simp at hlen

/-- The estimate on `∂₂` used in the invariant `z_q ≤ q²`. -/
theorem canonicalShadow_two_le_two_mul
    {q m : ℕ} (hq : 2 ≤ q) (hm : m ≤ q ^ 2) :
    canonicalShadow 2 m ≤ 2 * q := by
  have hmLt : m < (2 * q).choose 2 :=
    hm.trans_lt (choose_two_mul_gt_sq hq)
  unfold canonicalShadow
  apply cascadeShadowValue_two_le
  · exact (isCanonical_canonicalDigits (k := 2) (m := m) (by omega)).length_le
  · exact canonicalDigits_all_lt (k := 2) (m := m) (A := 2 * q)
      (by omega) hmLt

/-! Fixed two-shadow values used at the bottom of the induction. -/

theorem canonicalShadow_two_five : canonicalShadow 2 5 = 4 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [3, 2]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_three : canonicalShadow 2 3 = 3 := by
  rw [show 3 = (3 : ℕ).choose 2 by norm_num [Nat.choose],
    canonicalShadow_choose (by omega) (by omega)]
  norm_num

theorem canonicalShadow_two_four : canonicalShadow 2 4 = 4 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [3, 1]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_six : canonicalShadow 2 6 = 4 := by
  rw [show 6 = (4 : ℕ).choose 2 by norm_num [Nat.choose],
    canonicalShadow_choose (by omega) (by omega)]
  norm_num

theorem canonicalShadow_two_seven : canonicalShadow 2 7 = 5 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [4, 1]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_eight : canonicalShadow 2 8 = 5 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [4, 2]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_nine : canonicalShadow 2 9 = 5 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [4, 3]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_eleven : canonicalShadow 2 11 = 6 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [5, 1]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_twelve : canonicalShadow 2 12 = 6 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [5, 2]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_fourteen : canonicalShadow 2 14 = 6 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [5, 4]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_sixteen : canonicalShadow 2 16 = 7 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [6, 1]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_twenty : canonicalShadow 2 20 = 7 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [6, 5]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_thirtySix : canonicalShadow 2 36 = 9 := by
  rw [show 36 = (9 : ℕ).choose 2 by norm_num [Nat.choose],
    canonicalShadow_choose (by omega) (by omega)]
  norm_num

/-- Run the recurrence downward for a prescribed number of steps. -/
def scalarDescent (t : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 =>
      let q := t - d
      2 * q - 1 + canonicalShadow 2 (scalarDescent t d)

/-- `z_q`, with `z_t=0`. -/
def scalarResidual (t q : ℕ) : ℕ := scalarDescent t (t - q)

@[simp] theorem scalarResidual_top (t : ℕ) : scalarResidual t t = 0 := by
  simp [scalarResidual, scalarDescent]

theorem scalarResidual_step
    {t q : ℕ} (hq : 1 ≤ q) (hqt : q ≤ t) :
    scalarResidual t (q - 1) =
      2 * q - 1 + canonicalShadow 2 (scalarResidual t q) := by
  unfold scalarResidual
  rw [show t - (q - 1) = (t - q) + 1 by omega]
  simp only [scalarDescent]
  rw [show t - (t - q) = q by omega]

/-- The quadratic invariant from Lemma 10.2. -/
theorem scalarResidual_le_sq
    {t q : ℕ} (hq : 6 ≤ q) (hqt : q ≤ t) :
    scalarResidual t q ≤ q ^ 2 := by
  apply Nat.decreasingInduction'
      (P := fun k => scalarResidual t k ≤ k ^ 2)
      (m := q) (n := t) ?_ hqt
  · simp
  · intro k hkt hqk ih
    have hk6 : 6 ≤ k := hq.trans hqk
    have hk1t : k + 1 ≤ t := by omega
    rw [show k = (k + 1) - 1 by omega,
      scalarResidual_step (show 1 ≤ k + 1 by omega) hk1t]
    have hshadow := canonicalShadow_two_le_two_mul
      (q := k + 1) (m := scalarResidual t (k + 1)) (by omega) ih
    have hmul : 6 * k ≤ k ^ 2 := by
      rw [pow_two]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left k hk6
    have hsquare : 2 * (k + 1) - 1 + 2 * (k + 1) ≤ k ^ 2 := by
      omega
    exact (Nat.add_le_add_left hshadow (2 * (k + 1) - 1)).trans hsquare

theorem scalarResidual_two_bounds
    {t : ℕ} (ht : 3 ≤ t) :
    5 ≤ scalarResidual t 2 ∧ scalarResidual t 2 ≤ 11 := by
  constructor
  · rw [show 2 = 3 - 1 by omega, scalarResidual_step (q := 3) (by omega) ht]
    omega
  · by_cases ht3 : t = 3
    · subst t
      norm_num [scalarResidual, scalarDescent, canonicalShadow_two_five,
        canonicalShadow_two_three]
    by_cases ht4 : t = 4
    · subst t
      norm_num [scalarResidual, scalarDescent, canonicalShadow_two_seven,
        canonicalShadow_two_three]
    by_cases ht5 : t = 5
    · subst t
      norm_num [scalarResidual, scalarDescent, canonicalShadow_two_nine,
        canonicalShadow_two_twelve, canonicalShadow_two_five,
        canonicalShadow_two_three]
    have ht6 : 6 ≤ t := by omega
    have hz6 := scalarResidual_le_sq (t := t) (q := 6) (by omega) ht6
    have hs6 := canonicalShadow_mono 2 (by omega) hz6
    rw [show (6 : ℕ) ^ 2 = 36 by norm_num,
      canonicalShadow_two_thirtySix] at hs6
    have hz5 : scalarResidual t 5 ≤ 20 := by
      rw [show 5 = 6 - 1 by omega,
        scalarResidual_step (q := 6) (by omega) ht6]
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
    have hs3 := canonicalShadow_mono 2 (by omega) hz3
    rw [canonicalShadow_two_fourteen] at hs3
    rw [show 2 = 3 - 1 by omega,
      scalarResidual_step (q := 3) (by omega) (by omega)]
    omega

theorem canonicalShadow_two_eq_five_of_range
    {m : ℕ} (hlower : 7 ≤ m) (hupper : m ≤ 9) :
    canonicalShadow 2 m = 5 := by
  have hm : m = 7 ∨ m = 8 ∨ m = 9 := by omega
  rcases hm with rfl | rfl | rfl
  · exact canonicalShadow_two_seven
  · exact canonicalShadow_two_eight
  · exact canonicalShadow_two_nine

/-- Lemma 10.2, including the exceptional first two anchor indices. -/
theorem scalarResidual_zero (t : ℕ) (ht : 1 ≤ t) :
    scalarResidual t 0 = if t = 1 then 1 else if t = 2 then 4 else 6 := by
  by_cases ht1 : t = 1
  · subst t
    simp [scalarResidual, scalarDescent]
  by_cases ht2 : t = 2
  · subst t
    simp [scalarResidual, scalarDescent, canonicalShadow_two_three]
  have ht3 : 3 ≤ t := by omega
  have hz2 := scalarResidual_two_bounds ht3
  have hshadowLower := canonicalShadow_mono 2 (by omega) hz2.1
  have hshadowUpper := canonicalShadow_mono 2 (by omega) hz2.2
  rw [canonicalShadow_two_five] at hshadowLower
  rw [canonicalShadow_two_eleven] at hshadowUpper
  have hz1 : 7 ≤ scalarResidual t 1 ∧ scalarResidual t 1 ≤ 9 := by
    rw [show 1 = 2 - 1 by omega,
      scalarResidual_step (q := 2) (by omega) (by omega)]
    exact ⟨by omega, by omega⟩
  have hs1 := canonicalShadow_two_eq_five_of_range hz1.1 hz1.2
  rw [show 0 = 1 - 1 by omega,
    scalarResidual_step (q := 1) (by omega) (by omega), hs1]
  simp [ht1, ht2]

end Erdos776.Uniform
