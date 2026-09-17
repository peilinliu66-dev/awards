/-
Released under the MIT license.
The actual two endpoint fans and the length-many right channels in Case I.A
have total capacity at most length+4 when there is no empty hexagon.
Their coverage of the deletion cap is not assumed or proved in this file.
-/
import JSP198NicolasCaseISampled

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

variable {P : Finset Point} {hgp : GeneralPosition P}
  {o : Point} {ho : o ∈ inner (inner (inner P))}

def caseIRightChannelUnion (R : ActualCaseIRun P hgp o ho) : Finset Point :=
  (Finset.univ : Finset (Fin R.length)).biUnion (fun j =>
    let r := orbit (chainCycle P hgp o ho) R.first j.val
    matchChannel P r (chainCycle P hgp o ho r)
      (matchStart P hgp o ho r) (matchEnd P hgp o ho r))

def caseILocalCoverSet (R : ActualCaseIRun P hgp o ho) : Finset Point :=
  (outerFan P (matchStart P hgp o ho R.first)
    ((chainCycle P hgp o ho).symm R.first, R.first) ∪ caseIRightChannelUnion R) ∪
  outerFan P (matchEnd P hgp o ho R.last)
    (R.last, chainCycle P hgp o ho R.last)

theorem caseIRightChannelUnion_card_le (R : ActualCaseIRun P hgp o ho)
    (hno : ¬HasEmptySix P) : (caseIRightChannelUnion R).card ≤ R.length := by
  let cells := fun j : Fin R.length =>
    let r := orbit (chainCycle P hgp o ho) R.first j.val
    matchChannel P r (chainCycle P hgp o ho r)
      (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
  have hc (j : Fin R.length) : (cells j).card ≤ 1 := by
    let r := orbit (chainCycle P hgp o ho) R.first j.val
    exact boundary_match_channel_le_one P hgp hno r (chainCycle P hgp o ho r)
      (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
      (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho r)
      (sectorEdge_outward P hgp o ho r) (R.right_before j.val j.isLt)
  calc
    (caseIRightChannelUnion R).card ≤ ∑ j : Fin R.length, (cells j).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin R.length, (1 : ℕ) := Finset.sum_le_sum (fun j _ => hc j)
    _ = R.length := by simp

theorem caseILocalCoverSet_card_le (R : ActualCaseIRun P hgp o ho)
    (hno : ¬HasEmptySix P) : (caseILocalCoverSet R).card ≤ R.length+4 := by
  let f := chainCycle P hgp o ho
  let a := f.symm R.first
  let b := f R.last
  let left := outerFan P (matchStart P hgp o ho R.first) (a,R.first)
  let right := outerFan P (matchEnd P hgp o ho R.last) (R.last,b)
  have hedge : BoundaryEdge (ChainSecond P) a R.first := by
    simpa only [a,f,Equiv.apply_symm_apply] using chainCycle_edge P hgp o ho a
  have hleft : left.card ≤ 2 := by
    have hm := matchStart_mem P hgp o ho R.first
    exact outerFan_card_le_two P hgp hno _ (Finset.mem_sdiff.mp hm).1
      (a,R.first) hedge (chain_inner2_ne_second hm a)
      (chain_inner2_ne_second hm R.first)
  have hright : right.card ≤ 2 := by
    have hm := matchEnd_mem P hgp o ho R.last
    exact outerFan_card_le_two P hgp hno _ (Finset.mem_sdiff.mp hm).1
      (R.last,b) (chainCycle_edge P hgp o ho R.last)
      (chain_inner2_ne_second hm R.last) (chain_inner2_ne_second hm b)
  have hchannels := caseIRightChannelUnion_card_le R hno
  have hu := Finset.card_union_le (left ∪ caseIRightChannelUnion R) right
  have hv := Finset.card_union_le left (caseIRightChannelUnion R)
  change ((left ∪ caseIRightChannelUnion R) ∪ right).card ≤ _
  omega

end JSP198.Nicolas

#print axioms JSP198.Nicolas.caseIRightChannelUnion_card_le
#print axioms JSP198.Nicolas.caseILocalCoverSet_card_le
