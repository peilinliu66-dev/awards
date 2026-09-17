/- Released under the MIT license. Nicolas Case I.A with all geometric inputs proved. -/
import JSP198NicolasCaseIASampledSupport
import FinalAssemblyAdapter

noncomputable section
open Classical Horton

namespace JSP198.Nicolas

theorem hasEmptySix_of_caseIA_run
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho) (hmin : MinimalOuter P)
    (hsingle : RunHasSingletonSectors R)
    (hshort : R.length+3 ≤ (ChainSecond P).card) : HasEmptySix P :=
  SampledCapAssembly.hasEmptySix_of_caseIA_sampled_edge_support
    R hmin hsingle hshort (caseIA_sampled_edge_support R hsingle hshort)

end JSP198.Nicolas

namespace JSP198.FinalAssembly
open Nicolas

/-- The former remaining I.A obligation is discharged universally, without a
point-support, cover, order, SAT or other mathematical premise. -/
theorem remainingCaseIACore : RemainingCaseIACore := by
  intro P hgp hmin o ho R hsingle hshort
  exact hasEmptySix_of_caseIA_run R hmin hsingle hshort

end JSP198.FinalAssembly

#print axioms JSP198.Nicolas.hasEmptySix_of_caseIA_run
#print axioms JSP198.FinalAssembly.remainingCaseIACore
