import Erdos776.Uniform.LowerWindow.Supersolution

/-!
# Finite supersolution segments

This module packages a bounded interval of the lower-window supersolution.
It lets the mathematical blocks of the construction be proved in their
natural parameters and then stitched at a common endpoint.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

def HasEnvelopeSegment
    (r lo hi bottom top : ℕ) : Prop :=
  ∃ V : ℕ → ℕ,
    V lo = bottom ∧
    V hi = top ∧
    (∀ i, lo ≤ i → i < hi →
      r + canonicalShadow (i + 1) (V (i + 1)) ≤ V i) ∧
    ∀ i, lo ≤ i → i ≤ hi → V i ≤ (r + 4).choose i

/-- Reparameterize a segment by its distance below the top level. -/
theorem hasEnvelopeSegment_of_descent
    {r hi len : ℕ} {f : ℕ → ℕ}
    (hlen : len ≤ hi)
    (hstep : ∀ L, L < len →
      r + canonicalShadow (hi - L) (f L) ≤ f (L + 1))
    (hcap : ∀ L, L ≤ len → f L ≤ (r + 4).choose (hi - L)) :
    HasEnvelopeSegment r (hi - len) hi (f len) (f 0) := by
  let V : ℕ → ℕ := fun i => f (hi - i)
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · dsimp [V]
    rw [Nat.sub_sub_self hlen]
  · simp [V]
  · intro i hlo hhi
    let L := hi - (i + 1)
    have hLlt : L < len := by
      dsimp [L]
      omega
    have hiL : hi - L = i + 1 := by
      dsimp [L]
      omega
    have hiPred : hi - i = L + 1 := by
      dsimp [L]
      omega
    have hLdef : hi - (i + 1) = L := rfl
    dsimp [V]
    rw [hLdef, hiPred]
    rw [← hiL]
    exact hstep L hLlt
  · intro i hlo hhi
    let L := hi - i
    have hL : L ≤ len := by
      dsimp [L]
      omega
    have hiL : hi - L = i := by
      dsimp [L]
      omega
    dsimp [V]
    change f L ≤ (r + 4).choose i
    rw [← hiL]
    exact hcap L hL

/-- Stitch a lower segment to a higher one at their common state. -/
theorem HasEnvelopeSegment.stitch
    {r lo mid hi bottom seam top : ℕ}
    (hlow : HasEnvelopeSegment r lo mid bottom seam)
    (hhigh : HasEnvelopeSegment r mid hi seam top)
    (hlomid : lo ≤ mid) (hmidhi : mid < hi) :
    HasEnvelopeSegment r lo hi bottom top := by
  let Vlow := hlow.choose
  let Vhigh := hhigh.choose
  let V : ℕ → ℕ := fun i => if i ≤ mid then Vlow i else Vhigh i
  have hlowSpec := hlow.choose_spec
  have hhighSpec := hhigh.choose_spec
  have hlowBottom : Vlow lo = bottom := hlowSpec.1
  have hlowSeam : Vlow mid = seam := hlowSpec.2.1
  have hhighSeam : Vhigh mid = seam := hhighSpec.1
  have hhighTop : Vhigh hi = top := hhighSpec.2.1
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · simp [V, hlomid, hlowBottom]
  · have hnot : ¬hi ≤ mid := by omega
    simp [V, hnot, hhighTop]
  · intro i hlo hhi
    by_cases hilow : i < mid
    · have hiMid : i ≤ mid := by omega
      have hisMid : i + 1 ≤ mid := by omega
      simpa [V, hiMid, hisMid] using hlowSpec.2.2.1 i hlo hilow
    · by_cases hieq : i = mid
      · subst i
        have hstep := hhighSpec.2.2.1 mid le_rfl hmidhi
        have hstep' : r + canonicalShadow (mid + 1) (Vhigh (mid + 1)) ≤
            Vhigh mid := hstep
        have hnext : ¬mid + 1 ≤ mid := by omega
        simp only [V, if_pos le_rfl, if_neg hnext]
        rw [hlowSeam]
        rw [hhighSeam] at hstep'
        exact hstep'
      · have hmidlt : mid < i := by omega
        have hiNot : ¬i ≤ mid := by omega
        have hisNot : ¬i + 1 ≤ mid := by omega
        simpa [V, hiNot, hisNot] using
          hhighSpec.2.2.1 i (by omega) hhi
  · intro i hlo hhi
    by_cases hiMid : i ≤ mid
    · simp only [V, if_pos hiMid]
      exact hlowSpec.2.2.2 i hlo hiMid
    · simp only [V, if_neg hiMid]
      exact hhighSpec.2.2.2 i (by omega) hhi

end Erdos776.Uniform
