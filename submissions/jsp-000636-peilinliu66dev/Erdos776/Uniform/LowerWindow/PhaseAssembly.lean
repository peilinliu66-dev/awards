import Erdos776.Uniform.LowerWindow.FullEnvelope

/-!
# Assembly interface for the phase/envelope segment

All top anchors and the scalar bottom collapse are already proved.  This file
checks that the remaining Section 4--9 phase construction has exactly the
right endpoints and inequalities to imply `LowerWindowFits` and hence the
global Erdős threshold.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- The level-three endpoint selected by the terminal scalar residual. -/
def finalThreeState (r t : ℕ) : ℕ :=
  if t = 1 then (r + 3).choose 3 + 1 else (r + 3).choose 3 + 3

/--
The assembly interface for Sections 4--10: a capacity-bounded supersolution
from the completed anchor down to `F₀(z₀)` at level four.
-/
def HasLowerWindowPhaseEnvelope (r t : ℕ) : Prop :=
  ∃ V : ℕ → ℕ,
    V (r - t - 1) = completedAnchorValue r t ∧
    V 4 = finalFourState r (scalarResidual t 0) ∧
    (∀ i, 4 ≤ i → i < r - t - 1 →
      r + canonicalShadow (i + 1) (V (i + 1)) ≤ V i) ∧
    ∀ i, 4 ≤ i → i ≤ r - t - 1 → V i ≤ (r + 4).choose i

/-- Sections 4--10, assembled into the exact lower-window obligation. -/
theorem hasLowerWindowPhaseEnvelope
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    HasLowerWindowPhaseEnvelope r t := by
  let K := phaseCount r t
  let j := K - 1
  let p := phaseTop r t K - 1
  let A := r - t - 1
  have hK : 5 ≤ K := by dsimp [K]; exact five_le_phaseCount ht
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hjLast : j ≤ phaseCount r t - 1 := by
    dsimp [j, K]
    exact le_rfl
  have hjCount : j ≤ phaseCount r t := by dsimp [j, K]; omega
  have hp2 : 2 ≤ p := by
    dsimp [p, K]
    exact risingEntryPosition_two_le ht
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp [phaseWidth] at h64
  have hbirthLt : phaseBirth r t j < A := by
    have hb := phaseBirth_le_phaseBirth_one ht hj hjCount
    rw [phaseBirth_one ht] at hb
    dsimp [A]
    omega
  have hendLt : phaseBirth r t j - phaseExtensionCount r t j < A :=
    lt_of_le_of_lt (Nat.sub_le _ _) hbirthLt
  have hfinalLevel : risingLevel r t p =
      phaseBirth r t j - phaseExtensionCount r t j - 1 := by
    have hentry := risingEntryLevel ht
    have hsucc := phaseBirth_succ ht (j := K - 1) (by omega) (by omega)
    dsimp [K, j, p] at hentry hsucc ⊢
    rw [show phaseCount r t - 1 + 1 = phaseCount r t by omega] at hsucc
    omega
  have hord := ordinary_birth_to_anchor_segment hr ht hj hjLast
  change HasEnvelopeSegment r (phaseBirth r t j) A
    (phaseState r t j 0) (completedAnchorValue r t) at hord
  have hphase := phase_extension_segment hr ht hj hjCount
  have hthroughPhase := hphase.stitch hord (Nat.sub_le _ _) hbirthLt
  have hfinal := final_harvest_segment hr ht
  change HasEnvelopeSegment r (risingLevel r t p)
    (phaseBirth r t j - phaseExtensionCount r t j)
    (risingState r t p)
    (phaseState r t j (phaseExtensionCount r t j)) at hfinal
  have hthroughFinal := hfinal.stitch hthroughPhase
    (by rw [hfinalLevel]; omega) hendLt
  have hrising := rising_tail_segment hr ht
  change HasEnvelopeSegment r (risingLevel r t 2) (risingLevel r t p)
    (risingState r t 2) (risingState r t p) at hrising
  have hrisingTopLt : risingLevel r t p < A := by
    rw [hfinalLevel]
    omega
  have hthroughRising := hrising.stitch hthroughFinal
    (by unfold risingLevel; omega) hrisingTopLt
  have henv0 := generalized_envelope_segment hr ht
  rw [generalizedEnvelope_top_eq_rising ht] at henv0
  have henv : HasEnvelopeSegment r (t + 5) (risingLevel r t 2)
      (generalizedEnvelopeState r t (t + 5)) (risingState r t 2) := by
    simpa [risingLevel, K] using henv0
  have henvTopLt : risingLevel r t 2 < A := by
    have : risingLevel r t 2 ≤ risingLevel r t p := by
      unfold risingLevel
      omega
    exact this.trans_lt hrisingTopLt
  have hthroughEnvelope := henv.stitch hthroughRising
    (by unfold risingLevel; omega) henvTopLt
  have hcollision := envelope_collision_segment hr ht
  have hcollisionTopLt : t + 5 < A := by
    have : t + 5 ≤ risingLevel r t 2 := by
      unfold risingLevel
      omega
    exact this.trans_lt henvTopLt
  have hthroughCollision := hcollision.stitch hthroughEnvelope
    (by omega) hcollisionTopLt
  have hscalar := scalar_collapse_segment ht
  have hscalarTopLt : t + 4 < A := by omega
  have hfull := hscalar.stitch hthroughCollision (by omega) hscalarTopLt
  rcases hfull with ⟨V, hV4, hVtop, hstep, hcap⟩
  exact ⟨V, hVtop, hV4, hstep, hcap⟩

theorem lowerWindowChain_le_phaseEnvelope
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hphase : HasLowerWindowPhaseEnvelope r t) :
    ∀ i, 4 ≤ i → i ≤ r - t - 1 →
      lowerWindowChain r i ≤ hphase.choose i := by
  intro i hi4 hii
  let V := hphase.choose
  have hVtop : V (r - t - 1) = completedAnchorValue r t :=
    hphase.choose_spec.1
  have hstart : lowerWindowChain r (r - t - 1) ≤ V (r - t - 1) := by
    rw [hVtop]
    exact lowerWindowChain_le_completedAnchor ht
  apply Nat.decreasingInduction'
      (P := fun k => lowerWindowChain r k ≤ V k)
      (m := i) (n := r - t - 1) ?_ hii
  · exact hstart
  · intro k hk hki ih
    have hk4 : 4 ≤ k := hi4.trans hki
    rw [lowerWindowChain_step r k (by omega),
      lowerWindowProfile_eq_of_le (by omega)]
    have hshadow := canonicalShadow_mono (k + 1) (by omega) ih
    exact (Nat.add_le_add_left hshadow r).trans
      (hphase.choose_spec.2.2.1 k hk4 (by omega))

theorem lowerWindowChain_three_le_final
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hphase : HasLowerWindowPhaseEnvelope r t) :
    lowerWindowChain r 3 ≤ finalThreeState r t := by
  let V := hphase.choose
  have hi4 : 4 ≤ r - t - 1 := by
    have hlower := anchorThreshold_lower t ht.1
    have hTr := ht.2.1
    have hsum : 4 + (t + 1) ≤ r := by omega
    rw [show r - t - 1 = r - (t + 1) by omega]
    exact Nat.le_sub_of_add_le hsum
  have hchain4 : lowerWindowChain r 4 ≤ V 4 :=
    lowerWindowChain_le_phaseEnvelope ht hphase 4 le_rfl hi4
  rw [lowerWindowChain_step r 3 (by omega),
    lowerWindowProfile_eq_of_le (by omega)]
  have hshadow := canonicalShadow_mono 4 (by omega) hchain4
  have hV4 : V 4 = finalFourState r (scalarResidual t 0) :=
    hphase.choose_spec.2.1
  rw [hV4] at hshadow
  exact (Nat.add_le_add_left hshadow r).trans_eq
    (by simpa [finalThreeState] using
      finalFourState_scalar_step (r := r) (t := t) (by omega) ht.1)

theorem finalThreeState_le_capacity
    {r t : ℕ} (hr : 6 ≤ r) :
    finalThreeState r t ≤ (r + 4).choose 3 := by
  have hp : (r + 4).choose 3 =
      (r + 3).choose 2 + (r + 3).choose 3 := by
    simpa only [Nat.succ_eq_add_one,
      show r + 3 + 1 = r + 4 by omega] using
        Nat.choose_succ_succ (r + 3) 2
  have hcap : 3 ≤ (r + 3).choose 2 := by
    have hmono := Nat.choose_le_choose 2 (show 3 ≤ r + 3 by omega)
    norm_num at hmono
    exact hmono
  unfold finalThreeState
  split <;> omega

theorem lowerWindowChain_two_le_capacity_of_phaseEnvelope
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hphase : HasLowerWindowPhaseEnvelope r t) :
    lowerWindowChain r 2 ≤ (r + 4).choose 2 := by
  have hthree := lowerWindowChain_three_le_final hr ht hphase
  rw [lowerWindowChain_step r 2 (by omega),
    lowerWindowProfile_eq_of_le (by omega)]
  have hshadow := canonicalShadow_mono 3 (by omega) hthree
  have hbottom := finalScalar_bottom (r := r) (t := t) (by omega) ht.1
  have hbottom' : r + canonicalShadow 3 (finalThreeState r t) =
      if t = 1 then (r + 4).choose 2 - 1 else (r + 4).choose 2 := by
    simpa [finalThreeState] using hbottom
  exact (Nat.add_le_add_left hshadow r).trans (by
    rw [hbottom']
    split <;> omega)

/-- The phase-envelope obligation implies the complete symbolic lower window. -/
theorem lowerWindowFits_of_phaseEnvelope
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hphase : HasLowerWindowPhaseEnvelope r t) :
    LowerWindowFits r := by
  intro i hi2 hir
  by_cases hitop : i = r + 2
  · subst i
    simp
  have hir' : i ≤ r + 1 := by omega
  by_cases hi2eq : i = 2
  · subst i
    exact lowerWindowChain_two_le_capacity_of_phaseEnvelope hr ht hphase
  by_cases hi3eq : i = 3
  · subst i
    exact (lowerWindowChain_three_le_final hr ht hphase).trans
      (finalThreeState_le_capacity (by omega))
  have hi4 : 4 ≤ i := by omega
  by_cases hiPhase : i ≤ r - t - 1
  · exact (lowerWindowChain_le_phaseEnvelope ht hphase i hi4 hiPhase).trans
      (hphase.choose_spec.2.2.2 i hi4 hiPhase)
  · have hiAnchor : r - t ≤ i := by omega
    exact lowerWindowChain_fit_anchor_segment ht.2.1 hiAnchor hir'

/-- A phase envelope implies the global threshold. -/
theorem isErdosThreshold_of_phaseEnvelope
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hphase : HasLowerWindowPhaseEnvelope r t) :
    IsErdosThreshold r (2 * r + 5) := by
  exact isErdosThreshold_of_lowerWindowFits r (by omega)
    (lowerWindowFits_of_phaseEnvelope hr ht hphase)

/-- The symbolic lower-window capacities hold uniformly from `r=378` onward. -/
theorem lowerWindowFits_of_ge_378 (r : ℕ) (hr : 378 ≤ r) :
    LowerWindowFits r := by
  let t := maximalAnchorIndex r
  have ht : IsMaximalAnchorIndex r t := maximalAnchorIndex_spec r hr
  exact lowerWindowFits_of_phaseEnvelope hr ht
    (hasLowerWindowPhaseEnvelope hr ht)

/-- The full middle-profile threshold in the non-computational uniform range. -/
theorem fullMiddleProfileThreshold_of_ge_378 (r : ℕ) (hr : 378 ≤ r) :
    FullMiddleProfileThreshold r := by
  exact fullMiddleProfileThreshold_of_lowerWindowFits r (by omega)
    (lowerWindowFits_of_ge_378 r hr)

/-- The global Erdős threshold in the non-computational uniform range. -/
theorem isErdosThreshold_of_ge_378 (r : ℕ) (hr : 378 ≤ r) :
    IsErdosThreshold r (2 * r + 5) := by
  exact isErdosThreshold_of_lowerWindowFits r (by omega)
    (lowerWindowFits_of_ge_378 r hr)

end Erdos776.Uniform
