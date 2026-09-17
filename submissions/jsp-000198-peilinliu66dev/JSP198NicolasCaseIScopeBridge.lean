/-
Copyright (c) 2026 JSP198 formalization contributors.
Released under the MIT license. See LICENSE.
Mathematics: C. M. Nicolas, The Empty Hexagon Theorem (2007).
The separately imported MIT foundations retain the attribution to
CollinYuanjieRen/awards, commit b8bb4f7803f921a7970abc880291ad9372111360.

Scope adapter only: the local singleton-sector property of a SeparatedRun
becomes a global property ONLY when the run enumerates the entire second layer.
The existing complete I.C theorem then excludes that full-length case.
No Case I.A/I.B, I.C, or Case II geometric proof is reimplemented here.

Target: Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Uncompiled candidate: the authoring environment has no Lean/lake executable.
The default imports the combined Case II module. The modular/ variant differs
only by importing JSP198NicolasCaseII instead of JSP198NicolasCaseIIAll.
-/
import Mathlib
import JSP198NicolasCaseII
import JSP198NicolasCaseIC

open Horton

namespace JSP198.Nicolas
namespace CaseII

/-- A full separated run has globally injective sector labels. The proof uses
actual full-prefix enumeration and the previously proved global singleton
fiber of each vertex occurring in the run. No global sector premise is assumed. -/
theorem SeparatedRun.sectorEdge_injective_of_full
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : SeparatedRun P hgp o ho)
    (hno : ¬ HasEmptySix P)
    (hfull : R.run.length + 1 = (ChainSecond P).card) :
    Function.Injective (sectorEdge P hgp o ho) := by
  intro u v huv
  obtain ⟨j, hj⟩ := R.run.prefix_surjective_of_full hfull v
  have hsame : sectorEdge P hgp o ho u =
      sectorEdge P hgp o ho
        (orbit (chainCycle P hgp o ho) R.run.first j.val) :=
    huv.trans (congrArg (sectorEdge P hgp o ho) hj.symm)
  exact (SeparatedRun.sector_fiber_unique hno R j u hsame).trans hj

/-- Full-prefix enumeration upgrades LOCAL separated-run data to the GLOBAL
hypothesis required by the existing Case I.C theorem. A genuine boundary edge
has distinct endpoints, so injective sector labels exclude every equal-sector
successor pair, including the closing pair. -/
theorem SeparatedRun.adjacentSectorsDistinct_of_full
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : SeparatedRun P hgp o ho)
    (hno : ¬ HasEmptySix P)
    (hfull : R.run.length + 1 = (ChainSecond P).card) :
    AdjacentSectorsDistinct P hgp o ho := by
  unfold AdjacentSectorsDistinct
  intro u heq
  have huv : u = chainCycle P hgp o ho u :=
    R.sectorEdge_injective_of_full hno hfull heq
  exact (chainCycle_edge P hgp o ho u).2.2.1
    (congrArg (fun z : ChainVertex P => (z : Point)) huv)

end CaseII

/-- Complete scope bridge to the existing full-run I.C terminal. Its global
adjacent-sector hypothesis is PROVED inside the contradiction argument, not
passed as an extra hypothesis. -/
theorem hasEmptySix_of_full_separated_run
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (R : CaseII.SeparatedRun P hgp o ho)
    (hfull : R.run.length + 1 = (ChainSecond P).card) :
    HasEmptySix P := by
  classical
  by_contra hno
  have hdiff : AdjacentSectorsDistinct P hgp o ho :=
    R.adjacentSectorsDistinct_of_full hno hfull
  exact hno
    (hasEmptySix_of_full_caseI_run P hgp hmin o ho hdiff R.run hfull)

namespace CaseII

/-- Every separated run in a counterexample is shorter than a full enumeration.
This is the local-condition version of the existing full-run elimination. -/
theorem SeparatedRun.length_add_two_le
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : SeparatedRun P hgp o ho)
    (hmin : MinimalOuter P) (hno : ¬ HasEmptySix P) :
    R.run.length + 2 ≤ (ChainSecond P).card := by
  have hlt := R.run.shorter
  have hnot : R.run.length + 1 ≠ (ChainSecond P).card := by
    intro hfull
    exact hno (hasEmptySix_of_full_separated_run P hgp hmin o ho R hfull)
  omega

/-- Precisely the two remaining short-run ranges: Case I.A or Case I.B.
No global adjacent-sector distinctness is required for either alternative. -/
theorem SeparatedRun.short_cases
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : SeparatedRun P hgp o ho)
    (hmin : MinimalOuter P) (hno : ¬ HasEmptySix P) :
    R.run.length + 3 ≤ (ChainSecond P).card ∨
      R.run.length + 2 = (ChainSecond P).card := by
  have hlen := R.length_add_two_le hmin hno
  omega

end CaseII

/-- Counterexample form of the reduction. The run is obtained from the existing
unconditional Case II alternative, not supplied by the caller. -/
theorem exists_short_separated_run_of_no_emptySix
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (hno : ¬ HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) :
    ∃ R : CaseII.SeparatedRun P hgp o ho,
      R.run.length + 3 ≤ (ChainSecond P).card ∨
        R.run.length + 2 = (ChainSecond P).card := by
  rcases CaseII.emptySix_or_separated_caseI P hgp hmin o ho with hSix | hR
  · exact (hno hSix).elim
  · obtain ⟨R⟩ := hR
    exact ⟨R, R.short_cases hmin hno⟩

/-- UNCONDITIONAL BRANCH REDUCTION, under only the original geometric premises:
either an empty hexagon already exists, or an actual separated run lies in
exactly the two ranges delegated to the independent Case I.A/I.B proof.
There is no global hdiff, cover, coherence, bridge, or convexity argument. -/
theorem emptySix_or_short_separated_run
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) :
    HasEmptySix P ∨
      ∃ R : CaseII.SeparatedRun P hgp o ho,
        R.run.length + 3 ≤ (ChainSecond P).card ∨
          R.run.length + 2 = (ChainSecond P).card := by
  classical
  by_cases hSix : HasEmptySix P
  · exact Or.inl hSix
  · exact Or.inr
      (exists_short_separated_run_of_no_emptySix P hgp hmin hSix o ho)

/-- Adapter to Pro1's existing ActualCaseIRun input. Every sector occurring IN
THE RUN is globally singleton. Vertices outside the run are not required to
have distinct sectors. This is not a proof of the remaining I.A/I.B geometry. -/
theorem emptySix_or_short_actual_singleton_run
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) :
    HasEmptySix P ∨
      ∃ R : ActualCaseIRun P hgp o ho,
        (R.length + 3 ≤ (ChainSecond P).card ∨
          R.length + 2 = (ChainSecond P).card) ∧
        ∀ j : Fin (R.length + 1), ∀ s : ChainVertex P,
          sectorEdge P hgp o ho s =
            sectorEdge P hgp o ho
              (orbit (chainCycle P hgp o ho) R.first j.val) →
          s = orbit (chainCycle P hgp o ho) R.first j.val := by
  classical
  by_cases hSix : HasEmptySix P
  · exact Or.inl hSix
  · obtain ⟨R, hshort⟩ :=
      exists_short_separated_run_of_no_emptySix P hgp hmin hSix o ho
    refine Or.inr ⟨R.run, hshort, ?_⟩
    intro j s heq
    exact CaseII.SeparatedRun.sector_fiber_unique hSix R j s heq

end JSP198.Nicolas

#print axioms JSP198.Nicolas.CaseII.SeparatedRun.sectorEdge_injective_of_full
#print axioms JSP198.Nicolas.CaseII.SeparatedRun.adjacentSectorsDistinct_of_full
#print axioms JSP198.Nicolas.hasEmptySix_of_full_separated_run
#print axioms JSP198.Nicolas.CaseII.SeparatedRun.length_add_two_le
#print axioms JSP198.Nicolas.CaseII.SeparatedRun.short_cases
#print axioms JSP198.Nicolas.exists_short_separated_run_of_no_emptySix
#print axioms JSP198.Nicolas.emptySix_or_short_separated_run
#print axioms JSP198.Nicolas.emptySix_or_short_actual_singleton_run
