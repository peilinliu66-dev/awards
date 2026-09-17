import Erdos776.Uniform.LowerWindow.EnvelopeSegments
import Erdos776.Uniform.LowerWindow.ScalarStates

/-!
# Assembly of the symbolic lower-window envelope

The individual phase, rising-tail, generalized-envelope, and scalar proofs
are stitched here into one capacity-bounded supersolution from the completed
anchor down to level four.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

theorem phase_extension_segment
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    HasEnvelopeSegment r
      (phaseBirth r t j - phaseExtensionCount r t j)
      (phaseBirth r t j)
      (phaseState r t j (phaseExtensionCount r t j))
      (phaseState r t j 0) := by
  apply hasEnvelopeSegment_of_descent
  · have hu := four_le_phaseTop_at_phase ht hj hjK
    unfold phaseBirth phaseExtensionCount
    split <;> omega
  · intro L hL
    exact phase_extension_valid_auto hr ht hj hjK hL
  · intro L hL
    exact (phaseState_lt_capacity hr ht hj hjK hL).le

theorem completed_anchor_entry_segment
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    HasEnvelopeSegment r (phaseBirth r t 1) (r - t - 1)
      (phaseState r t 1 0) (completedAnchorValue r t) := by
  let f : ℕ → ℕ := fun L =>
    if L = 0 then completedAnchorValue r t else phaseState r t 1 0
  have hseg : HasEnvelopeSegment r ((r - t - 1) - 1) (r - t - 1)
      (phaseState r t 1 0) (completedAnchorValue r t) := by
    apply hasEnvelopeSegment_of_descent (f := f)
    · have h64 := sixtyFour_mul_phaseWidth_le ht
      simp [phaseWidth] at h64
      omega
    · intro L hL
      have hL0 : L = 0 := by omega
      subst L
      simpa [f] using completedAnchor_to_phase_one ht
    · intro L hL
      have hcases : L = 0 ∨ L = 1 := by omega
      rcases hcases with rfl | rfl
      · simpa [f] using (completedAnchorValue_lt_capacity ht).le
      · have hcap := phaseState_lt_capacity hr ht
          (j := 1) (L := 0) (by omega)
          (show 1 ≤ phaseCount r t from (phaseCount_spec ht).1) (by omega)
        simpa [f, phaseBirth_one ht, show r - t - 1 - 1 = r - t - 2 by omega] using hcap.le
  simpa [phaseBirth_one ht, show r - t - 1 - 1 = r - t - 2 by omega] using hseg

theorem ordinary_harvest_segment
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j + 1 ≤ phaseCount r t) :
    HasEnvelopeSegment r (phaseBirth r t (j + 1))
      (phaseBirth r t j - phaseExtensionCount r t j)
      (phaseState r t (j + 1) 0)
      (phaseState r t j (phaseExtensionCount r t j)) := by
  let f : ℕ → ℕ := fun L => if L = 0 then
    phaseState r t j (phaseExtensionCount r t j)
    else phaseState r t (j + 1) 0
  have hjK' : j ≤ phaseCount r t := by omega
  have hseg := hasEnvelopeSegment_of_descent (r := r)
    (hi := phaseBirth r t j - phaseExtensionCount r t j)
    (len := 1) (f := f)
    (by
      have hu := four_le_phaseTop_at_phase ht hj hjK'
      unfold phaseBirth phaseExtensionCount
      split <;> omega)
    (by
      intro L hL
      have hL0 : L = 0 := by omega
      subst L
      simpa [f] using phase_harvest_valid_auto hr ht hj hjK)
    (by
      intro L hL
      have hcases : L = 0 ∨ L = 1 := by omega
      rcases hcases with rfl | rfl
      · simpa [f] using
          (phaseState_lt_capacity hr ht hj hjK' (L := phaseExtensionCount r t j)
            le_rfl).le
      · simpa [f, phaseBirth_succ ht hj hjK'] using
          (phaseState_lt_capacity hr ht (j := j + 1) (L := 0)
            (by omega) hjK (by omega)).le)
  simpa [f, phaseBirth_succ ht hj hjK'] using hseg

theorem ordinary_birth_to_anchor_segment
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t - 1) :
    HasEnvelopeSegment r (phaseBirth r t j) (r - t - 1)
      (phaseState r t j 0) (completedAnchorValue r t) := by
  induction j, hj using Nat.le_induction with
  | base => exact completed_anchor_entry_segment hr ht
  | succ j hj ih =>
      have hjK' : j ≤ phaseCount r t - 1 := by omega
      have hjCount : j ≤ phaseCount r t := by omega
      have hjNext : j + 1 ≤ phaseCount r t := by omega
      have hacc := ih hjK'
      have hphase := phase_extension_segment hr ht hj hjCount
      have hbirthLt : phaseBirth r t j < r - t - 1 := by
        have hb := phaseBirth_le_phaseBirth_one ht hj hjCount
        rw [phaseBirth_one ht] at hb
        have h64 := sixtyFour_mul_phaseWidth_le ht
        simp [phaseWidth] at h64
        omega
      have hext := hphase.stitch hacc (Nat.sub_le _ _) hbirthLt
      have hharvest := ordinary_harvest_segment hr ht hj hjNext
      exact hharvest.stitch hext
        (by rw [phaseBirth_succ ht hj hjCount]; omega)
        (lt_of_le_of_lt (Nat.sub_le _ _) hbirthLt)

theorem final_harvest_segment
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    let K := phaseCount r t
    let j := K - 1
    let p := phaseTop r t K - 1
    HasEnvelopeSegment r (risingLevel r t p)
      (phaseBirth r t j - phaseExtensionCount r t j)
      (risingState r t p)
      (phaseState r t j (phaseExtensionCount r t j)) := by
  dsimp only
  let K := phaseCount r t
  let j := K - 1
  let p := phaseTop r t K - 1
  have hK : 5 ≤ K := by dsimp [K]; exact five_le_phaseCount ht
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hjK : j ≤ K := by dsimp [j]; omega
  have hp2 : 2 ≤ p := by
    dsimp [p, K]
    exact risingEntryPosition_two_le ht
  have hpu : p < phaseTop r t K := by dsimp [p]; omega
  let f : ℕ → ℕ := fun L => if L = 0 then
    phaseState r t j (phaseExtensionCount r t j) else risingState r t p
  have hseg := hasEnvelopeSegment_of_descent (r := r)
    (hi := phaseBirth r t j - phaseExtensionCount r t j)
    (len := 1) (f := f)
    (by
      have hu := four_le_phaseTop_at_phase ht hj hjK
      unfold phaseBirth phaseExtensionCount
      split <;> omega)
    (by
      intro L hL
      have hL0 : L = 0 := by omega
      subst L
      simpa [f, K, j, p] using final_phase_harvest_to_rising hr ht)
    (by
      intro L hL
      have hcases : L = 0 ∨ L = 1 := by omega
      rcases hcases with rfl | rfl
      · simpa [f, K, j] using
          (phaseState_lt_capacity hr ht hj hjK
            (L := phaseExtensionCount r t j) le_rfl).le
      · have hcap := risingState_lt_capacity hr ht hp2 hpu
        have hlevel : risingLevel r t p =
            phaseBirth r t j - phaseExtensionCount r t j - 1 := by
          have hentry := risingEntryLevel ht
          have hsucc := phaseBirth_succ ht (j := K - 1) (by omega) (by omega)
          dsimp [K, j, p] at hentry hsucc ⊢
          rw [show phaseCount r t - 1 + 1 = phaseCount r t by omega] at hsucc
          omega
        simpa [f, hlevel] using hcap.le)
  have hlevel : risingLevel r t p =
      phaseBirth r t j - phaseExtensionCount r t j - 1 := by
    have hentry := risingEntryLevel ht
    have hsucc := phaseBirth_succ ht (j := K - 1) (by omega) (by omega)
    dsimp [K, j, p] at hentry hsucc ⊢
    rw [show phaseCount r t - 1 + 1 = phaseCount r t by omega] at hsucc
    omega
  change HasEnvelopeSegment r (risingLevel r t p)
    (phaseBirth r t j - phaseExtensionCount r t j)
    (risingState r t p)
    (phaseState r t j (phaseExtensionCount r t j))
  rw [hlevel]
  exact hseg

theorem rising_tail_segment
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    let p := phaseTop r t (phaseCount r t) - 1
    HasEnvelopeSegment r (risingLevel r t 2) (risingLevel r t p)
      (risingState r t 2) (risingState r t p) := by
  dsimp only
  let u := phaseTop r t (phaseCount r t)
  let p₀ := u - 1
  have hp2 : 2 ≤ p₀ := by
    dsimp [p₀, u]
    exact risingEntryPosition_two_le ht
  have hpU : p₀ < u := by dsimp [p₀]; omega
  have hseg := hasEnvelopeSegment_of_descent (r := r)
    (hi := risingLevel r t p₀) (len := p₀ - 2)
    (f := fun L => risingState r t (p₀ - L))
    (by unfold risingLevel; omega)
    (by
      intro L hL
      let p := p₀ - L
      have hp3 : 3 ≤ p := by dsimp [p]; omega
      have hpU' : p < u := by dsimp [p]; omega
      have hlevel : risingLevel r t p₀ - L = risingLevel r t p := by
        dsimp [p]
        unfold risingLevel
        omega
      have hnext : p₀ - (L + 1) = p - 1 := by
        dsimp [p]
        omega
      change r + canonicalShadow (risingLevel r t p₀ - L)
          (risingState r t (p₀ - L)) ≤
        risingState r t (p₀ - (L + 1))
      rw [hlevel, show p₀ - L = p by rfl, hnext]
      by_cases hp : p = 3
      · rw [hp]
        exact risingState_final_step hr ht
      · exact risingState_step hr ht (by omega) (by
          dsimp [u] at hpU' ⊢
          exact hpU'))
    (by
      intro L hL
      let p := p₀ - L
      have hp2' : 2 ≤ p := by dsimp [p]; omega
      have hpU' : p < u := by dsimp [p]; omega
      have hlevel : risingLevel r t p₀ - L = risingLevel r t p := by
        dsimp [p]
        unfold risingLevel
        omega
      change risingState r t (p₀ - L) ≤
        (r + 4).choose (risingLevel r t p₀ - L)
      rw [hlevel]
      exact (risingState_lt_capacity hr ht hp2' (by
        dsimp [u] at hpU' ⊢
        exact hpU')).le)
  change HasEnvelopeSegment r (risingLevel r t 2) (risingLevel r t p₀)
    (risingState r t 2) (risingState r t p₀)
  have hlo : risingLevel r t p₀ - (p₀ - 2) = risingLevel r t 2 := by
    unfold risingLevel
    omega
  have hpbot : p₀ - (p₀ - 2) = 2 := by omega
  change HasEnvelopeSegment r (risingLevel r t p₀ - (p₀ - 2))
    (risingLevel r t p₀)
    (risingState r t (p₀ - (p₀ - 2))) (risingState r t (p₀ - 0)) at hseg
  rw [hlo, hpbot, Nat.sub_zero] at hseg
  exact hseg

theorem generalized_envelope_segment
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    HasEnvelopeSegment r (t + 5) (t + phaseCount r t + 4)
      (generalizedEnvelopeState r t (t + 5))
      (generalizedEnvelopeState r t (t + phaseCount r t + 4)) := by
  let hi := t + phaseCount r t + 4
  let len := phaseCount r t - 1
  have hK : 5 ≤ phaseCount r t := five_le_phaseCount ht
  have hseg := hasEnvelopeSegment_of_descent (r := r) (hi := hi) (len := len)
    (f := fun L => generalizedEnvelopeState r t (hi - L))
    (by dsimp [hi, len]; omega)
    (by
      intro L hL
      let i := hi - L
      have hiLower : t + 6 ≤ i := by dsimp [i, hi, len] at *; omega
      have hiUpper : i ≤ t + phaseCount r t + 4 := by
        dsimp [i, hi]
        omega
      have hpred : hi - (L + 1) = i - 1 := by dsimp [i]; omega
      change r + canonicalShadow (hi - L)
          (generalizedEnvelopeState r t (hi - L)) ≤
        generalizedEnvelopeState r t (hi - (L + 1))
      rw [show hi - L = i by rfl, hpred]
      exact (generalizedEnvelope_step hr ht hiLower hiUpper).ge)
    (by
      intro L hL
      let i := hi - L
      have hiLower : t + 5 ≤ i := by dsimp [i, hi, len] at *; omega
      have hiUpper : i ≤ t + phaseCount r t + 4 := by
        dsimp [i, hi]
        omega
      change generalizedEnvelopeState r t i ≤ (r + 4).choose (hi - L)
      rw [show hi - L = i by rfl]
      exact (generalizedEnvelopeState_lt_capacity hr ht hiLower hiUpper).le)
  have hlo : hi - len = t + 5 := by dsimp [hi, len]; omega
  change HasEnvelopeSegment r (hi - len) hi
    (generalizedEnvelopeState r t (hi - len))
    (generalizedEnvelopeState r t (hi - 0)) at hseg
  rw [hlo, Nat.sub_zero] at hseg
  dsimp [hi] at hseg
  exact hseg

theorem envelope_collision_segment
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    HasEnvelopeSegment r (t + 4) (t + 5)
      (scalarState r t 0) (generalizedEnvelopeState r t (t + 5)) := by
  let f : ℕ → ℕ := fun L => if L = 0 then
    generalizedEnvelopeState r t (t + 5) else scalarState r t 0
  have hseg := hasEnvelopeSegment_of_descent (r := r) (hi := t + 5)
    (len := 1) (f := f)
    (by omega)
    (by
      intro L hL
      have hL0 : L = 0 := by omega
      subst L
      simpa [f] using (generalizedEnvelope_collision hr ht).ge)
    (by
      intro L hL
      have hcases : L = 0 ∨ L = 1 := by omega
      rcases hcases with rfl | rfl
      · simpa [f] using
          (generalizedEnvelopeState_lt_capacity hr ht (by omega)
            (show t + 5 ≤ t + phaseCount r t + 4 by
              have := five_le_phaseCount ht
              omega)).le
      · simpa [f] using (scalarState_lt_capacity ht (q := t) le_rfl).le)
  have hlo : t + 5 - 1 = t + 4 := by omega
  rw [hlo] at hseg
  exact hseg

theorem scalar_collapse_segment
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    HasEnvelopeSegment r 4 (t + 4)
      (finalFourState r (scalarResidual t 0)) (scalarState r t 0) := by
  have hseg := hasEnvelopeSegment_of_descent (r := r) (hi := t + 4) (len := t)
    (f := fun L => scalarState r (t - L) (scalarResidual t (t - L)))
    (by omega)
    (by
      intro L hL
      let q := t - L
      have hq : 1 ≤ q := by dsimp [q]; omega
      have hnext : t - (L + 1) = q - 1 := by dsimp [q]; omega
      have hlevel : t + 4 - L = q + 4 := by dsimp [q]; omega
      change r + canonicalShadow (t + 4 - L)
          (scalarState r (t - L) (scalarResidual t (t - L))) ≤
        scalarState r (t - (L + 1)) (scalarResidual t (t - (L + 1)))
      rw [hlevel, show t - L = q by rfl, hnext]
      exact (scalarState_step_auto ht hq (by dsimp [q]; omega)).ge)
    (by
      intro L hL
      let q := t - L
      have hlevel : t + 4 - L = q + 4 := by dsimp [q]; omega
      change scalarState r (t - L) (scalarResidual t (t - L)) ≤
        (r + 4).choose (t + 4 - L)
      rw [hlevel]
      exact (scalarState_lt_capacity ht (q := q) (by dsimp [q]; omega)).le)
  have hlo : t + 4 - t = 4 := by omega
  rw [hlo] at hseg
  simp only [Nat.sub_self, Nat.sub_zero, scalarResidual_top] at hseg
  rw [scalarState_bottom_eq_finalFour] at hseg
  exact hseg

end Erdos776.Uniform
