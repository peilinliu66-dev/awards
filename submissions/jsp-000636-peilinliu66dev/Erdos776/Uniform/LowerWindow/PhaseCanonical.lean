import Erdos776.Uniform.LowerWindow.PhaseHarvest

/-!
# Canonicity of the displayed phase cascades

The transition lemmas evaluate `canonicalShadow` through the displayed digit
lists.  This file proves that the first phase is canonical and that every
in-phase extension preserves canonicity.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

theorem isCanonical_pairwise_gt
    {k : ℕ} {digits : List ℕ} (h : IsCanonical k digits) :
    digits.Pairwise (· > ·) := by
  induction digits generalizing k with
  | nil => simp
  | cons a digits ih =>
      cases k with
      | zero => simp at h
      | succ k =>
          simp only [isCanonical_succ_cons] at h
          simp only [List.pairwise_cons]
          exact ⟨h.2.1, ih h.2.2⟩

/-- Lower a canonical list one level and append a digit below its old last digit. -/
theorem isCanonical_lower_append_after_last
    {k last a : ℕ} {init : List ℕ}
    (hcanon : IsCanonical k (init ++ [last]))
    (hlen : (init ++ [last]).length ≤ k - 1)
    (hindex : 1 ≤ k - 1 - (init ++ [last]).length)
    (hvalid : k - 1 - (init ++ [last]).length ≤ a)
    (ha : a < last) :
    IsCanonical (k - 1) ((init ++ [last]) ++ [a]) := by
  have hlower : IsCanonical (k - 1) (init ++ [last]) :=
    hcanon.lowerIndex (by omega) hlen
  have hsingle : IsCanonical (k - 1 - (init ++ [last]).length) [a] :=
    isCanonical_singleton hindex hvalid
  apply isCanonical_append hlower hsingle
  intro d hd b hb
  simp only [List.mem_singleton] at hb
  subst b
  rcases List.mem_append.mp hd with hd | hd
  · have hp := isCanonical_pairwise_gt hcanon
    simp only [List.pairwise_append, List.pairwise_singleton,
      List.mem_singleton, forall_eq] at hp
    exact ha.trans (hp.2.2 d hd)
  · simp only [List.mem_singleton] at hd
    subst d
    exact ha

/-- The part of the current run before its last digit. -/
def phaseRunInitLength (j L : ℕ) : ℕ :=
  if j = 1 then L + 1 else L

def phasePreviousDigit (r t j L : ℕ) : ℕ :=
  towerStone r t j - 1 - phaseRunInitLength j L

theorem phaseRunLength_eq_init_add_one (j L : ℕ) :
    phaseRunLength j L = phaseRunInitLength j L + 1 := by
  unfold phaseRunLength phaseRunInitLength
  split <;> omega

theorem phaseDigits_eq_append_previous (r t j L : ℕ) :
    phaseDigits r t j L =
      (phaseFixedDigits r t j ++
        diagonalDigits (towerStone r t j - 1)
          (phaseRunInitLength j L)) ++
        [phasePreviousDigit r t j L] := by
  unfold phaseDigits phaseRunDigits phasePreviousDigit
  rw [phaseRunLength_eq_init_add_one, diagonalDigits_add_one]
  simp [List.append_assoc]

theorem phaseExtensionDigit_lt_previous
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j) :
    phaseExtensionDigit r t j L < phasePreviousDigit r t j L := by
  have hpos := phaseExtensionDigit_quarter_lower hr ht hj hjK hL
  unfold phaseExtensionDigit at hpos
  unfold phaseExtensionDigit phasePreviousDigit phaseRunInitLength
  by_cases hj1 : j = 1
  · simp only [hj1, if_pos] at hpos ⊢
    omega
  · simp only [if_neg hj1] at hpos ⊢
    omega

theorem phase_one_birth_index_after_anchors
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    phaseBirth r t 1 - (anchorHeadDigits r (t + 1)).length =
      phaseTop r t 1 := by
  rw [length_anchorHeadDigits, phaseBirth_one ht]
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp only [phaseWidth] at h64
  simp only [phaseTop_one, anchorN]
  omega

/-- The two-term state (4.2), i.e. phase one at birth, is canonical. -/
theorem isCanonical_phase_one_birth
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    IsCanonical (phaseBirth r t 1) (phaseDigits r t 1 0) := by
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp only [phaseWidth] at h64
  have hanchorTop := isCanonical_anchorHeadDigits
    (r := r) (q := t + 1) (show 2 * (t + 1) + 2 ≤ r by
      have hc : 3 ≤ phaseWidth t := by simp [phaseWidth]
      omega)
  have hbirth : phaseBirth r t 1 = r - t - 2 := phaseBirth_one ht
  have hanchorLen : (anchorHeadDigits r (t + 1)).length ≤
      phaseBirth r t 1 := by
    rw [length_anchorHeadDigits, hbirth]
    omega
  have hanchor : IsCanonical (phaseBirth r t 1)
      (anchorHeadDigits r (t + 1)) := by
    apply hanchorTop.lowerIndex
    · rw [hbirth]
      omega
    · exact hanchorLen
  have hu := five_le_phaseTop_one ht
  have hstone : towerStone r t 1 = phaseTop r t 1 + 2 := by
    rw [first_towerStone_eq]
    simp only [phaseTop_one]
    rw [phaseTop_one] at hu
    omega
  have hrunTop : IsCanonical (towerStone r t 1 - 1)
      (diagonalDigits (towerStone r t 1 - 1) 2) :=
    isCanonical_diagonalDigits (by omega)
  have hrun : IsCanonical (phaseBirth r t 1 -
      (anchorHeadDigits r (t + 1)).length)
      (diagonalDigits (towerStone r t 1 - 1) 2) := by
    rw [phase_one_birth_index_after_anchors ht]
    apply hrunTop.lowerIndex
    · rw [hstone]
      omega
    · rw [length_diagonalDigits_of_le (by omega)]
      omega
  have hcross : ∀ a ∈ anchorHeadDigits r (t + 1),
      ∀ b ∈ diagonalDigits (towerStone r t 1 - 1) 2, b < a := by
    intro a ha b hb
    obtain ⟨q, hq, rfl⟩ := mem_anchorHeadDigits
      (q := t + 1) (by omega) ha
    have hbLe := mem_diagonalDigits_le hb
    have hbN : b < anchorN r t := by
      rw [first_towerStone_eq] at hbLe
      have hN : 5 ≤ anchorN r t := by
        have hu' := five_le_phaseTop_one ht
        rw [phaseTop_one] at hu'
        omega
      omega
    have hNa : anchorN r t ≤ r + 2 - 2 * q := by
      unfold anchorN
      omega
    exact hbN.trans_le hNa
  have hfull := isCanonical_append hanchor hrun hcross
  unfold phaseDigits phaseFixedDigits phaseRunDigits phaseRunLength
  simp [towerDigits]
  exact hfull

/-- Every legal in-phase extension preserves canonicity. -/
theorem isCanonical_phase_extension
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j)
    (hcanon : IsCanonical (phaseBirth r t j - L) (phaseDigits r t j L)) :
    IsCanonical (phaseBirth r t j - (L + 1))
      (phaseDigits r t j (L + 1)) := by
  let k := phaseBirth r t j - L
  let init := phaseFixedDigits r t j ++
    diagonalDigits (towerStone r t j - 1) (phaseRunInitLength j L)
  let last := phasePreviousDigit r t j L
  let a := phaseExtensionDigit r t j L
  have hdecomp := phaseDigits_eq_append_previous r t j L
  have hcanon' : IsCanonical k (init ++ [last]) := by
    dsimp [k, init, last]
    rw [← hdecomp]
    exact hcanon
  have hindexEq := phaseExtension_actual_index ht hj hjK hL
  have hindex4 := phaseExtensionIndex_four_le ht hj hjK hL
  have hlen : (init ++ [last]).length ≤ k - 1 := by
    have hpos : 0 < k - 1 - (phaseDigits r t j L).length := by
      rw [hindexEq]
      omega
    have hlenPhase : (phaseDigits r t j L).length ≤ k - 1 :=
      (Nat.sub_pos_iff_lt.mp hpos).le
    dsimp [init, last, k]
    rw [← hdecomp]
    exact hlenPhase
  have hactual : k - 1 - (init ++ [last]).length =
      phaseExtensionIndex r t j L := by
    dsimp [k, init, last]
    rw [← hdecomp]
    exact hindexEq
  have hvalid := phaseExtensionIndex_add_two_le_digit hr ht hj hjK hL
  have ha := phaseExtensionDigit_lt_previous hr ht hj hjK hL
  have hnext := isCanonical_lower_append_after_last hcanon' hlen
    (by rw [hactual]; omega) (by rw [hactual]; omega) ha
  have hlevel : phaseBirth r t j - (L + 1) = k - 1 := by
    have : L + 1 ≤ phaseBirth r t j := by
      have hnonneg : 4 ≤ k - 1 := by
        exact hindex4.trans (by
          rw [← hindexEq]
          exact Nat.sub_le _ _)
      dsimp [k] at hnonneg
      omega
    dsimp [k]
    omega
  rw [phaseDigits_succ, hlevel]
  dsimp [init, last, a] at hnext
  rw [← hdecomp] at hnext
  exact hnext

/-! ### Canonicity across a harvest -/

theorem isCanonical_append_left
    {k : ℕ} {xs ys : List ℕ} (h : IsCanonical k (xs ++ ys)) :
    IsCanonical k xs := by
  induction xs generalizing k with
  | nil => simp
  | cons a xs ih =>
      cases k with
      | zero => simp at h
      | succ k =>
          simp only [List.cons_append, isCanonical_succ_cons] at h ⊢
          refine ⟨h.1, ?_, ih h.2.2⟩
          intro b hb
          exact h.2.1 b (List.mem_append_left ys hb)

theorem mem_towerDigits
    {r t count d : ℕ} (hd : d ∈ towerDigits r t count) :
    ∃ q, 1 ≤ q ∧ q ≤ count ∧ d = towerStone r t q := by
  induction count with
  | zero => simp [towerDigits] at hd
  | succ count ih =>
      rw [towerDigits_succ] at hd
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨q, hq1, hqCount, rfl⟩ := ih hd
        exact ⟨q, hq1, by omega, rfl⟩
      · simp only [List.mem_singleton] at hd
        exact ⟨count + 1, by omega, le_rfl, hd⟩

theorem towerStone_anti_of_le
    {r t q j : ℕ} (hq : 1 ≤ q) (hqj : q ≤ j) :
    towerStone r t j ≤ towerStone r t q := by
  have hexp : q - 1 ≤ j - 1 := by omega
  have hpow : 2 ^ (q - 1) ≤ 2 ^ (j - 1) :=
    pow_le_pow_right' (by omega) hexp
  have hmul : phaseWidth t * 2 ^ (q - 1) ≤
      phaseWidth t * 2 ^ (j - 1) := Nat.mul_le_mul_left _ hpow
  unfold towerStone
  omega

theorem towerStone_strict_of_lt
    {r t q j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hq : 1 ≤ q) (hqj : q < j) (hjK : j ≤ phaseCount r t) :
    towerStone r t j < towerStone r t q := by
  have hexp : q - 1 < j - 1 := by omega
  have hpow : 2 ^ (q - 1) < 2 ^ (j - 1) :=
    Nat.pow_lt_pow_right (by omega) hexp
  have hc : 0 < phaseWidth t := by simp [phaseWidth]
  have hmul : phaseWidth t * 2 ^ (q - 1) <
      phaseWidth t * 2 ^ (j - 1) :=
    (Nat.mul_lt_mul_left hc).2 hpow
  have hjpos : 1 ≤ j := by omega
  have hexpK : j - 1 ≤ phaseCount r t - 1 := by omega
  have hpowK : 2 ^ (j - 1) ≤ 2 ^ (phaseCount r t - 1) :=
    pow_le_pow_right' (by omega) hexpK
  have hdist : phaseWidth t * 2 ^ (j - 1) ≤ r / 4 :=
    (Nat.mul_le_mul_left _ hpowK).trans (phaseCount_spec ht).2.1
  unfold towerStone
  omega

theorem phaseFixed_digit_gt_stone
    {r t j d : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hd : d ∈ phaseFixedDigits r t j) :
    towerStone r t j < d := by
  rcases List.mem_append.mp hd with hd | hd
  · obtain ⟨q, hq, rfl⟩ := mem_anchorHeadDigits
      (q := t + 1) (by
        have h64 := sixtyFour_mul_phaseWidth_le ht
        simp [phaseWidth] at h64
        omega) hd
    have hstoneFirst : towerStone r t j ≤ towerStone r t 1 :=
      towerStone_anti_of_le (by omega) hj
    rw [first_towerStone_eq] at hstoneFirst
    unfold anchorN at hstoneFirst
    have h64 := sixtyFour_mul_phaseWidth_le ht
    simp only [phaseWidth] at h64
    omega
  · obtain ⟨q, hq1, hqCount, rfl⟩ := mem_towerDigits hd
    exact towerStone_strict_of_lt ht hq1 (by omega) hjK

/-- An ordinary harvest produces a canonical birth state for the next phase. -/
theorem isCanonical_phase_harvest
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j + 1 ≤ phaseCount r t)
    (hcanon : IsCanonical
      (phaseBirth r t j - phaseExtensionCount r t j)
      (phaseDigits r t j (phaseExtensionCount r t j))) :
    IsCanonical (phaseBirth r t (j + 1)) (phaseDigits r t (j + 1) 0) := by
  let ell := phaseExtensionCount r t j
  let k := phaseBirth r t j - ell
  let fixed := phaseFixedDigits r t j
  let s := towerStone r t j
  let a := towerStone r t (j + 1) - 1
  have hjK' : j ≤ phaseCount r t := by omega
  have hfixedSize : fixed.length + 2 ≤ k := by
    dsimp [fixed, k, ell]
    rw [length_phaseFixedDigits]
    unfold phaseBirth phaseExtensionCount
    by_cases hj1 : j = 1
    · simp only [hj1, if_pos]
      have hu := five_le_phaseTop_one ht
      omega
    · simp only [if_neg hj1]
      have hu := four_le_phaseTop_at_phase ht hj hjK'
      omega
  have hfixedCanonK : IsCanonical k fixed := by
    apply isCanonical_append_left
    simpa [k, fixed, ell, phaseDigits] using hcanon
  have hfixedCanon : IsCanonical (k - 1) fixed :=
    hfixedCanonK.lowerIndex (by omega) (by omega)
  have hactive := phase_harvest_active_index ht hj hjK'
  have hnewIndex := phase_harvest_newborn_index ht hj hjK'
  have hnewIndex' : k - fixed.length - 2 = phaseTop r t (j + 1) := by
    simpa [k, fixed, ell] using hnewIndex
  have hp : k - 1 - fixed.length =
      phaseTop r t (j + 1) + 1 := by
    omega
  have hnewInterior : phaseTop r t (j + 1) + 2 ≤ a := by
    dsimp [a]
    have hu := phaseTop_le_half_add_one_of_two_le ht (show 2 ≤ j + 1 by omega)
    have hs := towerStone_phase_lower ht (show 1 ≤ j + 1 by omega) hjK
    omega
  have hstoneStep : towerStone r t (j + 1) < s := by
    dsimp [s]
    exact towerStone_strict_of_lt ht hj (by omega) hjK
  have htail : IsCanonical (k - 1 - fixed.length) [s, a] := by
    rw [hp]
    simp only [isCanonical_succ_cons]
    refine ⟨?_, ?_, ?_⟩
    · have huNext := four_le_phaseTop_at_phase ht (by omega) hjK
      have hsNext := towerStone_phase_lower ht (by omega) hjK
      dsimp [s]
      omega
    · intro b hb
      simp only [List.mem_singleton] at hb
      subst b
      have hstep := hstoneStep
      dsimp [a, s]
      dsimp [s] at hstep
      omega
    · have huNext := four_le_phaseTop_at_phase ht (by omega) hjK
      exact isCanonical_singleton (by omega) (by omega)
  have hcross : ∀ d ∈ fixed, ∀ b ∈ [s, a], b < d := by
    intro d hd b hb
    have hsd := phaseFixed_digit_gt_stone ht hj hjK' hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hsd
    · have has : a < s := by
        have hstep := hstoneStep
        dsimp [a, s]
        dsimp [s] at hstep
        omega
      exact has.trans hsd
  have hfull := isCanonical_append hfixedCanon htail hcross
  have hbirth : phaseBirth r t (j + 1) = k - 1 := by
    dsimp [k, ell]
    exact phaseBirth_succ ht hj hjK'
  rw [phaseDigits_next_zero hj, hbirth]
  exact hfull

/-! ### Chainable ordinary phases -/

theorem isCanonical_phase_within
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hbirth : IsCanonical (phaseBirth r t j) (phaseDigits r t j 0)) :
    ∀ L, L ≤ phaseExtensionCount r t j →
      IsCanonical (phaseBirth r t j - L) (phaseDigits r t j L) := by
  intro L hL
  induction L, Nat.zero_le L using Nat.le_induction with
  | base => simpa using hbirth
  | succ L _ ih =>
      exact isCanonical_phase_extension hr ht hj hjK (by omega) (ih (by omega))

/-- Every ordinary phase birth through `K` has the displayed canonical cascade. -/
theorem isCanonical_phase_birth
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    IsCanonical (phaseBirth r t j) (phaseDigits r t j 0) := by
  induction j, hj using Nat.le_induction with
  | base => exact isCanonical_phase_one_birth ht
  | succ j hj ih =>
      have hjK' : j ≤ phaseCount r t := by omega
      have hend := isCanonical_phase_within hr ht hj hjK' (ih hjK')
        (phaseExtensionCount r t j) le_rfl
      exact isCanonical_phase_harvest hr ht hj (by omega) hend

theorem isCanonical_phase_state
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L ≤ phaseExtensionCount r t j) :
    IsCanonical (phaseBirth r t j - L) (phaseDigits r t j L) :=
  isCanonical_phase_within hr ht hj hjK
    (isCanonical_phase_birth hr ht hj hjK) L hL

/-- Every in-phase transition in phases `1,...,K` is a valid supersolution step. -/
theorem phase_extension_valid_auto
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j) :
    r + canonicalShadow (phaseBirth r t j - L) (phaseState r t j L) ≤
      phaseState r t j (L + 1) :=
  phase_extension_valid hr ht hj hjK hL
    (isCanonical_phase_state hr ht hj hjK hL.le)

/-- Every ordinary harvest before the final phase is a valid supersolution step. -/
theorem phase_harvest_valid_auto
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j + 1 ≤ phaseCount r t) :
    r + canonicalShadow
        (phaseBirth r t j - phaseExtensionCount r t j)
        (phaseState r t j (phaseExtensionCount r t j)) ≤
      phaseState r t (j + 1) 0 :=
  phase_harvest_valid hr ht hj hjK
    (isCanonical_phase_state hr ht hj (by omega) le_rfl)

end Erdos776.Uniform
