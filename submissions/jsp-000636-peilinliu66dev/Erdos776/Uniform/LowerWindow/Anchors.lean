import Erdos776.Uniform.LowerWindow.Parameters

/-!
# Exact lower-window anchors

The lists below are the canonical cascades in (3.2): a finite ladder of
two-spaced anchor digits followed by the remaining diagonal (unary) block.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- The digits `r+2, r, ..., r+2-2q` in the anchor part of (3.2). -/
def anchorHeadDigits (r : ℕ) : ℕ → List ℕ
  | 0 => [r + 2]
  | q + 1 => anchorHeadDigits r q ++ [r - 2 * q]

@[simp] theorem length_anchorHeadDigits (r q : ℕ) :
    (anchorHeadDigits r q).length = q + 1 := by
  induction q with
  | zero => rfl
  | succ q ih => simp [anchorHeadDigits, ih]

theorem mem_anchorHeadDigits
    {r q d : ℕ} (hrq : 2 * q ≤ r) (hd : d ∈ anchorHeadDigits r q) :
    ∃ j ≤ q, d = r + 2 - 2 * j := by
  induction q with
  | zero =>
      simp [anchorHeadDigits] at hd
      exact ⟨0, le_rfl, by omega⟩
  | succ q ih =>
      simp only [anchorHeadDigits, List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl
      · obtain ⟨j, hj, rfl⟩ := ih (by omega) hd
        exact ⟨j, by omega, rfl⟩
      · exact ⟨q + 1, le_rfl, by omega⟩

theorem isCanonical_anchorHeadDigits
    {r q : ℕ} (hrq : 2 * q + 2 ≤ r) :
    IsCanonical (r - q) (anchorHeadDigits r q) := by
  induction q with
  | zero =>
      exact isCanonical_singleton (by omega) (by omega)
  | succ q ih =>
      have hprev : IsCanonical (r - q) (anchorHeadDigits r q) :=
        ih (by omega)
      have hlen : (anchorHeadDigits r q).length ≤ r - (q + 1) := by
        rw [length_anchorHeadDigits]
        omega
      have hlower : IsCanonical (r - (q + 1)) (anchorHeadDigits r q) :=
        hprev.lowerIndex (by omega) hlen
      have htail : IsCanonical
          (r - (q + 1) - (anchorHeadDigits r q).length) [r - 2 * q] := by
        rw [length_anchorHeadDigits]
        have hindex : r - (q + 1) - (q + 1) = r - 2 * q - 2 := by omega
        rw [hindex]
        exact isCanonical_singleton (by omega) (by omega)
      rw [anchorHeadDigits]
      apply isCanonical_append hlower htail
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      obtain ⟨j, hj, rfl⟩ :=
        mem_anchorHeadDigits (q := q) (by omega) ha
      omega

theorem anchorThreshold_position_bound (q : ℕ) :
    2 * q + 2 ≤ anchorThreshold q := by
  by_cases hq0 : q = 0
  · subst q
    norm_num
  · have hlower := anchorThreshold_lower q
      (Nat.one_le_iff_ne_zero.mpr hq0)
    omega

/-- The full canonical digit list in (3.2). -/
def anchorDigits (r q : ℕ) : List ℕ :=
  anchorHeadDigits r q ++
    diagonalDigits (r - 2 * q - 1) (r - anchorThreshold q)

/-- Numerical value of the exact `q`-th anchor. -/
def anchorValue (r q : ℕ) : ℕ :=
  cascadeValue (r - q) (anchorDigits r q)

theorem isCanonical_anchorDigits
    {r q : ℕ} (hT : anchorThreshold q ≤ r) :
    IsCanonical (r - q) (anchorDigits r q) := by
  have hpos := anchorThreshold_position_bound q
  have hhead := isCanonical_anchorHeadDigits
    (r := r) (q := q) (by omega)
  have htailLen : r - anchorThreshold q ≤ r - 2 * q - 1 := by omega
  have htail : IsCanonical (r - 2 * q - 1)
      (diagonalDigits (r - 2 * q - 1) (r - anchorThreshold q)) :=
    isCanonical_diagonalDigits htailLen
  unfold anchorDigits
  apply isCanonical_append hhead
  · convert htail using 1
    rw [length_anchorHeadDigits]
    omega
  · intro a ha b hb
    have hbLe := mem_diagonalDigits_le hb
    obtain ⟨j, hj, rfl⟩ :=
      mem_anchorHeadDigits (q := q) (by omega) ha
    omega

/-- The top state is the first exact anchor (`q=0`). -/
theorem lowerWindowChain_eq_anchorValue_zero
    {r : ℕ} (hr : 28 ≤ r) :
    lowerWindowChain r r = anchorValue r 0 := by
  rw [lowerWindowChain_step r r (by omega),
    lowerWindowProfile_eq_of_le le_rfl,
    lowerWindowChain_top_value,
    canonicalShadow_diagonal (show r - 6 ≤ r + 1 by omega)]
  have hidx : r + 1 + 1 - (r - 6) = 8 := by omega
  rw [hidx, show Nat.choose 8 2 = 28 by norm_num [Nat.choose_two_right]]
  unfold anchorValue anchorDigits
  simp only [anchorHeadDigits]
  rw [cascadeValue_append]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero,
    List.length_singleton, Nat.sub_zero]
  simp only [anchorThreshold_zero, Nat.mul_zero, Nat.sub_zero]
  rw [cascadeValue_diagonalDigits (show r - 28 ≤ r - 1 by omega)]
  have hsymm : (r + 2).choose r = (r + 2).choose 2 := by
    exact Nat.choose_symm_of_eq_add (by omega)
  rw [hsymm, show r + 1 + 1 = r + 2 by omega]
  have hchoose : 28 ≤ (r + 2).choose 2 := by
    have := Nat.choose_le_choose 2 (show 8 ≤ r + 2 by omega)
    norm_num [Nat.choose_two_right] at this ⊢
    exact this
  omega

/-- Shadowing the diagonal remainder produces the residual in Lemma 3.1. -/
theorem anchorTail_shadow
    {r q : ℕ} (hcurrent : anchorThreshold q ≤ r) :
    cascadeValue (r - q - 1 - (anchorHeadDigits r q).length)
        (diagonalDigits (r - 2 * q - 1) (r - anchorThreshold q)) =
      (r - 2 * q).choose 2 - anchorThreshold (q + 1) := by
  have hpos := anchorThreshold_position_bound q
  have hlen : r - anchorThreshold q ≤ r - 2 * q - 1 := by omega
  rw [length_anchorHeadDigits]
  have hindex : r - q - 1 - (q + 1) = (r - 2 * q - 1) - 1 := by omega
  rw [hindex]
  change cascadeShadowValue (r - 2 * q - 1)
      (diagonalDigits (r - 2 * q - 1) (r - anchorThreshold q)) = _
  rw [cascadeShadowValue_diagonalDigits hlen]
  have htop : r - 2 * q - 1 + 1 = r - 2 * q := by omega
  have hbottom : r - 2 * q - (r - anchorThreshold q) =
      anchorThreshold q - 2 * q := by omega
  rw [htop, hbottom, anchorThreshold_succ]

/-- Appending the next completed anchor contributes `choose (r-2q) 2`. -/
theorem anchorHeadDigits_succ_value
    {r q : ℕ} (hrq : 2 * q + 4 ≤ r) :
    cascadeValue (r - (q + 1)) (anchorHeadDigits r (q + 1)) =
      cascadeValue (r - q - 1) (anchorHeadDigits r q) +
        (r - 2 * q).choose 2 := by
  rw [anchorHeadDigits, cascadeValue_append, length_anchorHeadDigits]
  have hindex : r - (q + 1) - (q + 1) = r - 2 * q - 2 := by omega
  rw [hindex]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  have hsymm : (r - 2 * q).choose (r - 2 * q - 2) =
      (r - 2 * q).choose 2 := by
    exact Nat.choose_symm (by omega)
  rw [hsymm]
  congr 1

/-- The new diagonal remainder represents `r-T_(q+1)` exactly. -/
theorem anchorTail_succ_value
    {r q : ℕ} (hnext : anchorThreshold (q + 1) ≤ r) :
    cascadeValue (r - (q + 1) - (anchorHeadDigits r (q + 1)).length)
        (diagonalDigits (r - 2 * (q + 1) - 1)
          (r - anchorThreshold (q + 1))) =
      r - anchorThreshold (q + 1) := by
  have hpos := anchorThreshold_position_bound (q + 1)
  rw [length_anchorHeadDigits]
  have hindex : r - (q + 1) - (q + 1 + 1) =
      r - 2 * (q + 1) - 1 := by omega
  rw [hindex]
  exact cascadeValue_diagonalDigits (by omega)

/-- One exact anchor shadows to the next exact anchor. -/
theorem anchorValue_step
    {r q : ℕ} (hnext : anchorThreshold (q + 1) ≤ r) :
    r + canonicalShadow (r - q) (anchorValue r q) =
      anchorValue r (q + 1) := by
  have hcurrent : anchorThreshold q ≤ r :=
    (anchorThreshold_mono q).trans hnext
  have hcanon := isCanonical_anchorDigits hcurrent
  change r + canonicalShadow (r - q)
      (cascadeValue (r - q) (anchorDigits r q)) = anchorValue r (q + 1)
  rw [canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold anchorValue anchorDigits
  rw [cascadeShadowValue_append, cascadeValue_append]
  rw [anchorHeadDigits_succ_value (show 2 * q + 4 ≤ r by
      have := anchorThreshold_position_bound (q + 1)
      omega)]
  rw [anchorTail_shadow hcurrent, anchorTail_succ_value hnext]
  have hhead : cascadeShadowValue (r - q) (anchorHeadDigits r q) =
      cascadeValue (r - q - 1) (anchorHeadDigits r q) := by
    rfl
  rw [hhead]
  have hbase : anchorThreshold q - 2 * q ≤ r - 2 * q := by omega
  have hchoose : anchorThreshold (q + 1) ≤ (r - 2 * q).choose 2 := by
    rw [anchorThreshold_succ]
    exact Nat.choose_le_choose 2 hbase
  have hchooseSub : (r - 2 * q).choose 2 - anchorThreshold (q + 1) +
      anchorThreshold (q + 1) = (r - 2 * q).choose 2 :=
    Nat.sub_add_cancel hchoose
  have hrSub : r - anchorThreshold (q + 1) + anchorThreshold (q + 1) = r :=
    Nat.sub_add_cancel hnext
  omega

/-- Lemma 3.1: all anchor states are exact states of the recurrence. -/
theorem lowerWindowChain_eq_anchorValue
    {r q : ℕ} (hT : anchorThreshold q ≤ r) :
    lowerWindowChain r (r - q) = anchorValue r q := by
  induction q with
  | zero =>
      simpa using lowerWindowChain_eq_anchorValue_zero
        (show 28 ≤ r by simpa using hT)
  | succ q ih =>
      have hcurrent : anchorThreshold q ≤ r :=
        (anchorThreshold_mono q).trans hT
      have hi := ih hcurrent
      have hqr : q + 1 ≤ r := by
        have := anchorThreshold_position_bound (q + 1)
        omega
      rw [show r - (q + 1) = (r - q) - 1 by omega,
        lowerWindowChain_step r ((r - q) - 1) (by omega),
        lowerWindowProfile_eq_of_le (by omega),
        show (r - q - 1) + 1 = r - q by omega,
        hi]
      exact anchorValue_step hT

/-! ### Capacity on the exact anchor segment -/

theorem anchorDigits_all_lt
    {r q : ℕ} (hT : anchorThreshold q ≤ r) :
    ∀ d ∈ anchorDigits r q, d < r + 3 := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · obtain ⟨j, hj, rfl⟩ := mem_anchorHeadDigits
      (q := q) (by
        have := anchorThreshold_position_bound q
        omega) hd
    omega
  · have hdLe := mem_diagonalDigits_le hd
    omega

theorem anchorValue_lt_choose_r3
    {r q : ℕ} (hT : anchorThreshold q ≤ r) :
    anchorValue r q < (r + 3).choose (r - q) := by
  unfold anchorValue
  exact cascadeValue_lt_choose_of_all_lt
    (by omega) (isCanonical_anchorDigits hT) (anchorDigits_all_lt hT)

theorem anchorValue_lt_capacity
    {r q : ℕ} (hT : anchorThreshold q ≤ r) :
    anchorValue r q < (r + 4).choose (r - q) := by
  have hsmall := anchorValue_lt_choose_r3 hT
  have hposBound := anchorThreshold_position_bound q
  have hkpos : 1 ≤ r - q := by omega
  have hterm : 0 < (r + 3).choose (r - q - 1) :=
    Nat.choose_pos (by omega)
  have hp := Nat.choose_succ_succ (r + 3) (r - q - 1)
  have hindex : r - q - 1 + 1 = r - q := by omega
  simp only [Nat.succ_eq_add_one] at hp
  rw [hindex] at hp
  rw [show r + 3 + 1 = r + 4 by omega] at hp
  omega

/-- Every exact state from the top through the maximal anchor fits. -/
theorem lowerWindowChain_fit_anchor_segment
    {r t i : ℕ} (hT : anchorThreshold t ≤ r)
    (hiLower : r - t ≤ i) (hiUpper : i ≤ r + 1) :
    lowerWindowChain r i ≤ (r + 4).choose i := by
  by_cases hitop : i = r + 1
  · subst i
    rw [lowerWindowChain_top_value]
    have hbase : (r + 2).choose (r + 1) ≤ (r + 4).choose (r + 1) :=
      Nat.choose_le_choose (r + 1) (by omega)
    rw [show (r + 2).choose (r + 1) = r + 2 by
      exact Nat.choose_succ_self_right (r + 1)] at hbase
    omega
  · have hir : i ≤ r := by omega
    let q := r - i
    have hq : q ≤ t := by
      dsimp [q]
      omega
    have hTq : anchorThreshold q ≤ r :=
      (monotone_anchorThreshold hq).trans hT
    have hiq : r - q = i := by
      dsimp [q]
      omega
    rw [← hiq, lowerWindowChain_eq_anchorValue hTq]
    exact (anchorValue_lt_capacity hTq).le

/-! ### The additional completed anchor from Section 4 -/

/-- The rounded state (4.1), with the final old remainder completed. -/
def completedAnchorValue (r t : ℕ) : ℕ :=
  cascadeValue (r - t - 1) (anchorHeadDigits r (t + 1))

/-- Descending once past the maximal exact anchor is bounded by (4.1). -/
theorem lowerWindowChain_le_completedAnchor
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    lowerWindowChain r (r - t - 1) ≤ completedAnchorValue r t := by
  have hT := ht.2.1
  have hpos := anchorThreshold_position_bound t
  rw [lowerWindowChain_step r (r - t - 1) (by omega),
    lowerWindowProfile_eq_of_le (by omega),
    show r - t - 1 + 1 = r - t by omega,
    lowerWindowChain_eq_anchorValue hT]
  have hcanon := isCanonical_anchorDigits hT
  change r + canonicalShadow (r - t)
      (cascadeValue (r - t) (anchorDigits r t)) ≤ completedAnchorValue r t
  rw [canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold anchorDigits completedAnchorValue
  rw [cascadeShadowValue_append, anchorTail_shadow hT]
  have hheadSucc := anchorHeadDigits_succ_value
    (r := r) (q := t) (show 2 * t + 4 ≤ r by
      have hlower := anchorThreshold_lower t ht.1
      omega)
  rw [show r - (t + 1) = r - t - 1 by omega] at hheadSucc
  rw [hheadSucc]
  have hhead : cascadeShadowValue (r - t) (anchorHeadDigits r t) =
      cascadeValue (r - t - 1) (anchorHeadDigits r t) := by rfl
  rw [hhead]
  have hbase : anchorThreshold t - 2 * t ≤ r - 2 * t := by omega
  have hnextCap : anchorThreshold (t + 1) ≤ (r - 2 * t).choose 2 := by
    rw [anchorThreshold_succ]
    exact Nat.choose_le_choose 2 hbase
  have hsub : (r - 2 * t).choose 2 - anchorThreshold (t + 1) +
      anchorThreshold (t + 1) = (r - 2 * t).choose 2 :=
    Nat.sub_add_cancel hnextCap
  have hrt : 2 * t ≤ r := by omega
  have hrDecomp : r - 2 * t + 2 * t = r := Nat.sub_add_cancel hrt
  have hrNext : r < anchorThreshold (t + 1) := ht.2.2
  omega

theorem completedAnchorValue_lt_capacity
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    completedAnchorValue r t < (r + 4).choose (r - t - 1) := by
  have hlower := anchorThreshold_lower t ht.1
  have hTr := ht.2.1
  have hcanon0 := isCanonical_anchorHeadDigits
    (r := r) (q := t + 1) (show 2 * (t + 1) + 2 ≤ r by omega)
  have hcanon : IsCanonical (r - t - 1) (anchorHeadDigits r (t + 1)) := by
    simpa only [show r - (t + 1) = r - t - 1 by omega] using hcanon0
  have hall : ∀ d ∈ anchorHeadDigits r (t + 1), d < r + 3 := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := mem_anchorHeadDigits
      (q := t + 1) (by omega) hd
    omega
  have hsmall : completedAnchorValue r t <
      (r + 3).choose (r - t - 1) := by
    unfold completedAnchorValue
    exact cascadeValue_lt_choose_of_all_lt (by omega) hcanon hall
  have hkpos : 1 ≤ r - t - 1 := by omega
  have hterm : 0 < (r + 3).choose (r - t - 2) :=
    Nat.choose_pos (by omega)
  have hp := Nat.choose_succ_succ (r + 3) (r - t - 2)
  simp only [Nat.succ_eq_add_one] at hp
  rw [show r - t - 2 + 1 = r - t - 1 by omega,
    show r + 3 + 1 = r + 4 by omega] at hp
  omega

end Erdos776.Uniform
