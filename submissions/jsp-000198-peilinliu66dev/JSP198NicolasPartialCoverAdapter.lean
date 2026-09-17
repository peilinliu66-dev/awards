/-
Released under the MIT license.
Direct adapter to the existing PASS CaseII.SeparatedRun structure.
No Case II, arc-order, or endpoint-support proof is repeated.
-/
import JSP198NicolasPartialCover
import JSP198NicolasCaseIISelection

open Horton
namespace JSP198.Nicolas.PartialCover

variable {P : Finset Point} {hgp : GeneralPosition P}
  {o : Point} {ho : o ∈ inner (inner (inner P))}

theorem separated_run_cap_cover
    (R : CaseII.SeparatedRun P hgp o ho) :
    deletionCap R.run ⊆ coverCells R.run := by
  apply actual_run_cap_cover
  intro j hj
  exact R.changes j hj

theorem separated_run_cap_card_le
    (R : CaseII.SeparatedRun P hgp o ho)
    (hno : ¬ HasEmptySix P) :
    (deletionCap R.run).card ≤ R.run.length + 4 := by
  apply actual_run_cap_card_le R.run
  · intro j hj
    exact R.changes j hj
  · exact hno

end JSP198.Nicolas.PartialCover

#print axioms JSP198.Nicolas.PartialCover.separated_run_cap_cover
#print axioms JSP198.Nicolas.PartialCover.separated_run_cap_card_le
