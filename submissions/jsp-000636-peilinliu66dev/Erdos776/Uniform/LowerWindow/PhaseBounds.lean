import Erdos776.Uniform.LowerWindow.PhaseTransitions

/-!
# Quantitative bounds for ordinary phase terms

This file supplies the binomial estimates from Lemma 5.1 and Section 6.  The
proof is uniform in `r`; no finite numerical scan is imported.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- Binomial coefficients increase in the lower index up to the midpoint. -/
theorem choose_mono_right_of_le_half
    {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n / 2) :
    n.choose a ≤ n.choose b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      exact (ih (by omega)).trans
        (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- Away from both endpoints, `choose d k` is at least `choose d 2`. -/
theorem choose_two_le_choose_of_interior
    {d k : ℕ} (hk : 2 ≤ k) (hcomp : k + 2 ≤ d) :
    d.choose 2 ≤ d.choose k := by
  have hkd : k ≤ d := by omega
  by_cases hkhalf : k ≤ d / 2
  · exact choose_mono_right_of_le_half hk hkhalf
  · have hcompHalf : d - k ≤ d / 2 := by omega
    have hcompTwo : 2 ≤ d - k := by omega
    rw [← Nat.choose_symm hkd]
    exact choose_mono_right_of_le_half hcompTwo hcompHalf

/-- A convenient linear lower bound for triangular numbers. -/
theorem five_mul_le_choose_two :
    ∀ d : ℕ, 11 ≤ d → 5 * d ≤ d.choose 2 := by
  intro d hd
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hd11 : 11 ≤ d
      · have hprev := ih hd11
        rw [show (d + 1).choose 2 = d.choose 1 + d.choose 2 by
          simpa using Nat.choose_succ_succ d 1]
        simp only [Nat.choose_one_right]
        omega
      · have hd10 : d = 10 := by omega
        subst d
        norm_num [Nat.choose_two_right]

/-- For `r ≥ 378`, even the quarter-scale endpoint binomial exceeds `r`. -/
theorem r_lt_choose_quarter_sub_one
    {r : ℕ} (hr : 378 ≤ r) :
    r < (r / 4 - 1).choose 2 := by
  let d := r / 4 - 1
  have hd : 11 ≤ d := by
    dsimp [d]
    omega
  have hfive := five_mul_le_choose_two d hd
  have hrfive : r < 5 * d := by
    dsimp [d]
    omega
  exact hrfive.trans_le hfive

/-- A term with both indices at least two and a quarter-scale digit pays `r`. -/
theorem binomial_pays_of_quarter_digit
    {r d k : ℕ} (hr : 378 ≤ r)
    (hd : r / 4 - 1 ≤ d) (hk : 2 ≤ k) (hcomp : k + 2 ≤ d) :
    r ≤ d.choose k := by
  have hquarter := r_lt_choose_quarter_sub_one hr
  have hfirst : (r / 4 - 1).choose 2 ≤ d.choose 2 :=
    Nat.choose_le_choose 2 hd
  have hsecond := choose_two_le_choose_of_interior hk hcomp
  exact hquarter.le.trans (hfirst.trans hsecond)

theorem phaseExtensionDigit_quarter_lower
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j) :
    r / 4 - 1 ≤ phaseExtensionDigit r t j L := by
  unfold phaseExtensionDigit
  unfold phaseExtensionCount at hL
  by_cases hj1 : j = 1
  · subst j
    simp only [if_pos] at hL ⊢
    have hu := five_le_phaseTop_one ht
    have hstone : towerStone r t 1 = phaseTop r t 1 + 2 := by
      rw [first_towerStone_eq]
      simp only [phaseTop_one]
      have hu := five_le_phaseTop_one ht
      rw [phaseTop_one] at hu
      omega
    rw [hstone]
    have hueq := phaseTop_one_eq_width ht
    have h64 := sixtyFour_mul_phaseWidth_le ht
    omega
  · simp only [if_neg hj1] at hL ⊢
    have hj2 : 2 ≤ j := by omega
    have hu := phaseTop_le_half_add_one_of_two_le ht hj2
    have hs := towerStone_phase_lower ht hj hjK
    omega

theorem phaseExtensionIndex_add_two_le_digit
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j) :
    phaseExtensionIndex r t j L + 2 ≤ phaseExtensionDigit r t j L := by
  unfold phaseExtensionDigit phaseExtensionIndex
  unfold phaseExtensionCount at hL
  by_cases hj1 : j = 1
  · subst j
    simp only [if_pos] at hL ⊢
    have hu := five_le_phaseTop_one ht
    have hstone : towerStone r t 1 = phaseTop r t 1 + 2 := by
      rw [first_towerStone_eq]
      simp only [phaseTop_one]
      rw [phaseTop_one] at hu
      omega
    rw [hstone]
    omega
  · simp only [if_neg hj1] at hL ⊢
    have hj2 : 2 ≤ j := by omega
    have hu := phaseTop_le_half_add_one_of_two_le ht hj2
    have hs := towerStone_phase_lower ht hj hjK
    omega

/-- Every displayed in-phase extension term pays the full incoming load. -/
theorem phaseExtension_binomial_pays
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j) :
    r ≤ (phaseExtensionDigit r t j L).choose
      (phaseExtensionIndex r t j L) := by
  apply binomial_pays_of_quarter_digit hr
  · exact phaseExtensionDigit_quarter_lower hr ht hj hjK hL
  · exact (phaseExtensionIndex_four_le ht hj hjK hL).trans' (by omega)
  · exact phaseExtensionIndex_add_two_le_digit hr ht hj hjK hL

/-- The in-phase transition with its quantitative payment discharged. -/
theorem phase_extension_valid
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j)
    (hcanon : IsCanonical (phaseBirth r t j - L) (phaseDigits r t j L)) :
    r + canonicalShadow (phaseBirth r t j - L) (phaseState r t j L) ≤
      phaseState r t j (L + 1) :=
  phase_extension_pays ht hj hjK hL hcanon
    (phaseExtension_binomial_pays hr ht hj hjK hL)

end Erdos776.Uniform
