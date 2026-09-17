import Erdos776.Uniform.LowerWindow.Anchors
import Erdos776.Uniform.LowerWindow.PhasePositions

/-!
# Cascade states and ordinary in-phase transitions

The lists in this file are the active runs (6.0a)--(6.0b), not merely their
cardinalities.  The main transition lemma evaluates the actual canonical
Kruskal--Katona shadow through such a list and appends the new paying term.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-! ### Generic cascade transition lemmas -/

theorem length_diagonalDigits_of_le
    {a len : ℕ} (hlen : len ≤ a) :
    (diagonalDigits a len).length = len := by
  induction len generalizing a with
  | zero => rfl
  | succ len ih =>
      cases a with
      | zero => omega
      | succ a =>
          simp only [diagonalDigits_succ, List.length_cons]
          rw [ih (by omega)]

/-- Appending one term that has value at least `r` gives a supersolution step. -/
theorem cascade_append_pays
    {r k a : ℕ} {digits : List ℕ}
    (hcanon : IsCanonical k digits)
    (hpay : r ≤ a.choose (k - 1 - digits.length)) :
    r + canonicalShadow k (cascadeValue k digits) ≤
      cascadeValue (k - 1) (digits ++ [a]) := by
  rw [canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold cascadeShadowValue
  rw [cascadeValue_append]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  omega

/-- A descending partial run is dominated, after shadowing, by its completion. -/
theorem diagonalRun_shadow_le_completion
    {s p len : ℕ} (hp : 1 ≤ p) (hlen : len ≤ p) (hps : p < s) :
    cascadeShadowValue p (diagonalDigits (s - 1) len) ≤
      s.choose (p - 1) := by
  have hspos : 1 ≤ s := by omega
  have hcanonTop : IsCanonical (s - 1)
      (diagonalDigits (s - 1) len) :=
    isCanonical_diagonalDigits (by omega)
  have hcanon : IsCanonical p (diagonalDigits (s - 1) len) :=
    hcanonTop.lowerIndex (by omega) (by
      rw [length_diagonalDigits_of_le (by omega)]
      exact hlen)
  have hall : ∀ d ∈ diagonalDigits (s - 1) len, d < s := by
    intro d hd
    exact (mem_diagonalDigits_le hd).trans_lt (by omega)
  have hvalue : cascadeValue p (diagonalDigits (s - 1) len) <
      s.choose p :=
    cascadeValue_lt_choose_of_all_lt (by omega) hcanon hall
  have hmono := canonicalShadow_mono p hp hvalue.le
  rw [canonicalShadow_eq_cascadeShadowValue hcanon rfl,
    canonicalShadow_choose hp (by omega)] at hmono
  exact hmono

/--
Complete an old descending run to the digit `s`; a newborn term `a` then
pays the incoming load.  This is the abstract hockey-stick harvest argument.
-/
theorem cascade_harvest_pays
    {r k s a len : ℕ} {fixed : List ℕ}
    (hcanon : IsCanonical k (fixed ++ diagonalDigits (s - 1) len))
    (hfixed : fixed.length + 2 ≤ k)
    (hlen : len ≤ k - fixed.length)
    (hstone : k - fixed.length < s)
    (hpay : r ≤ a.choose (k - fixed.length - 2)) :
    r + canonicalShadow k
        (cascadeValue k (fixed ++ diagonalDigits (s - 1) len)) ≤
      cascadeValue (k - 1) (fixed ++ [s, a]) := by
  rw [canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold cascadeShadowValue
  rw [cascadeValue_append, cascadeValue_append]
  have hp : 1 ≤ k - fixed.length := by omega
  have hcomplete := diagonalRun_shadow_le_completion
    hp hlen hstone
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  have hidx1 : k - 1 - fixed.length = k - fixed.length - 1 := by omega
  have hidx2 : k - fixed.length - 1 - 1 =
      k - fixed.length - 2 := by omega
  rw [hidx1, hidx2]
  change cascadeValue (k - fixed.length - 1)
      (diagonalDigits (s - 1) len) ≤ s.choose (k - fixed.length - 1)
    at hcomplete
  omega

/-! ### The displayed phase states -/

/-- The already-completed tower stones `s₁,...,s_count`. -/
def towerDigits (r t : ℕ) : ℕ → List ℕ
  | 0 => []
  | count + 1 => towerDigits r t count ++ [towerStone r t (count + 1)]

@[simp] theorem length_towerDigits (r t count : ℕ) :
    (towerDigits r t count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [towerDigits, ih]

theorem towerDigits_succ (r t count : ℕ) :
    towerDigits r t (count + 1) =
      towerDigits r t count ++ [towerStone r t (count + 1)] := rfl

/-- A useful list form of extending a descending digit run by one place. -/
theorem diagonalDigits_add_one (a len : ℕ) :
    diagonalDigits a (len + 1) =
      diagonalDigits a len ++ [a - len] := by
  induction len generalizing a with
  | zero => simp
  | succ len ih =>
      change a :: diagonalDigits (a - 1) (len + 1) =
        (a :: diagonalDigits (a - 1) len) ++ [a - (len + 1)]
      rw [List.cons_append, ih]
      congr 2
      simp [Nat.sub_sub, Nat.add_comm]

/-- Number of active terms after `L` extensions in phase `j`. -/
def phaseRunLength (j L : ℕ) : ℕ :=
  if j = 1 then L + 2 else L + 1

/-- The active run `R_{j,L}` from (6.0a)--(6.0b), represented by its digits. -/
def phaseRunDigits (r t j L : ℕ) : List ℕ :=
  diagonalDigits (towerStone r t j - 1) (phaseRunLength j L)

@[simp] theorem length_phaseRunDigits
    {r t j L : ℕ} (hlen : phaseRunLength j L ≤ towerStone r t j - 1) :
    (phaseRunDigits r t j L).length = phaseRunLength j L := by
  unfold phaseRunDigits
  exact length_diagonalDigits_of_le hlen

/-- The new digit appended by the next in-phase extension. -/
def phaseExtensionDigit (r t j L : ℕ) : ℕ :=
  if j = 1 then towerStone r t j - 3 - L
  else towerStone r t j - 2 - L

/-- Its lower binomial index, as displayed in (6.1) and (6.3). -/
def phaseExtensionIndex (r t j L : ℕ) : ℕ :=
  if j = 1 then phaseTop r t j - 3 - 2 * L
  else phaseTop r t j - 2 - 2 * L

theorem phaseRunDigits_succ (r t j L : ℕ) :
    phaseRunDigits r t j (L + 1) =
      phaseRunDigits r t j L ++ [phaseExtensionDigit r t j L] := by
  by_cases hj1 : j = 1
  · subst j
    simp only [phaseRunDigits, phaseRunLength, if_pos, phaseExtensionDigit]
    rw [show L + 1 + 2 = (L + 2) + 1 by omega,
      diagonalDigits_add_one]
    congr 2
    simp [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm]
  · simp only [phaseRunDigits, phaseRunLength, if_neg hj1,
      phaseExtensionDigit]
    rw [show L + 1 + 1 = (L + 1) + 1 by omega,
      diagonalDigits_add_one]
    congr 2
    simp [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm]

/-- Digits that remain fixed during phase `j`. -/
def phaseFixedDigits (r t j : ℕ) : List ℕ :=
  anchorHeadDigits r (t + 1) ++ towerDigits r t (j - 1)

@[simp] theorem length_phaseFixedDigits (r t j : ℕ) :
    (phaseFixedDigits r t j).length = t + 2 + (j - 1) := by
  simp [phaseFixedDigits]

/-- The complete digit list at level `b_j-L`. -/
def phaseDigits (r t j L : ℕ) : List ℕ :=
  phaseFixedDigits r t j ++ phaseRunDigits r t j L

/-- The numerical state represented by the displayed phase cascade. -/
def phaseState (r t j L : ℕ) : ℕ :=
  cascadeValue (phaseBirth r t j - L) (phaseDigits r t j L)

theorem phaseDigits_succ (r t j L : ℕ) :
    phaseDigits r t j (L + 1) =
      phaseDigits r t j L ++ [phaseExtensionDigit r t j L] := by
  unfold phaseDigits
  rw [phaseRunDigits_succ]
  simp [List.append_assoc]

theorem phaseExtensionIndex_four_le
    {r t j L : ℕ} (_ht : IsMaximalAnchorIndex r t)
    (_hj : 1 ≤ j) (_hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j) :
    4 ≤ phaseExtensionIndex r t j L := by
  unfold phaseExtensionIndex
  unfold phaseExtensionCount at hL
  by_cases hj1 : j = 1
  · simp only [hj1, if_pos] at hL ⊢
    omega
  · simp only [if_neg hj1] at hL ⊢
    omega

theorem phaseRunLength_le_stone
    {r t j L : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L ≤ phaseExtensionCount r t j) :
    phaseRunLength j L ≤ towerStone r t j - 1 := by
  have hu := (phaseTop_between_at_phase ht hj hjK).2
  have hs := towerStone_phase_lower ht hj hjK
  unfold phaseRunLength
  unfold phaseExtensionCount at hL
  by_cases hj1 : j = 1
  · subst j
    simp at hL
    simp only [if_pos]
    have hu1 := five_le_phaseTop_one ht
    have hstone : towerStone r t 1 = phaseTop r t 1 + 2 := by
      rw [first_towerStone_eq]
      simp only [phaseTop_one]
      rw [phaseTop_one] at hu1
      omega
    rw [hstone]
    rw [phaseTop_one]
    rw [phaseTop_one] at hu1
    omega
  · simp only [if_neg hj1] at hL ⊢
    have hj2 : 2 ≤ j := by omega
    have huHalf := phaseTop_le_half_add_one_of_two_le ht hj2
    have h64 := sixtyFour_mul_phaseWidth_le ht
    have hc : 3 ≤ phaseWidth t := by simp [phaseWidth]
    omega

theorem phaseExtension_actual_index
    {r t j L : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j) :
    phaseBirth r t j - L - 1 - (phaseDigits r t j L).length =
      phaseExtensionIndex r t j L := by
  have hrun := phaseRunLength_le_stone ht hj hjK hL.le
  unfold phaseDigits
  rw [List.length_append, length_phaseFixedDigits,
    length_phaseRunDigits hrun]
  unfold phaseBirth phaseRunLength phaseExtensionIndex
  by_cases hj1 : j = 1
  · subst j
    simp only [if_pos]
    omega
  · simp only [if_neg hj1]
    omega

/-- One actual in-phase cascade transition from Section 6. -/
theorem phase_extension_pays
    {r t j L : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j)
    (hcanon : IsCanonical (phaseBirth r t j - L) (phaseDigits r t j L))
    (hpay : r ≤ (phaseExtensionDigit r t j L).choose
      (phaseExtensionIndex r t j L)) :
    r + canonicalShadow (phaseBirth r t j - L) (phaseState r t j L) ≤
      phaseState r t j (L + 1) := by
  have hindex := phaseExtension_actual_index ht hj hjK hL
  have hidx4 := phaseExtensionIndex_four_le ht hj hjK hL
  have hlevel : phaseBirth r t j - (L + 1) =
      phaseBirth r t j - L - 1 := by
    have : L + 1 ≤ phaseBirth r t j := by
      have hnonneg : 4 ≤ phaseBirth r t j - L - 1 := by
        have hsub : phaseBirth r t j - L - 1 -
            (phaseDigits r t j L).length ≤ phaseBirth r t j - L - 1 :=
          Nat.sub_le _ _
        rw [hindex] at hsub
        exact hidx4.trans hsub
      omega
    omega
  unfold phaseState
  rw [phaseDigits_succ, hlevel]
  apply cascade_append_pays hcanon
  rw [hindex]
  exact hpay

end Erdos776.Uniform
