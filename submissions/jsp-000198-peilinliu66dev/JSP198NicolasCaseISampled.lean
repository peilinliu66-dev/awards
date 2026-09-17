/-
Released under the MIT license.
The actual sampled replacement set in Nicolas Case I.A.
This file proves only its exact size and inner-layer membership.
Convex support and local cap coverage are separate remaining obligations.
-/
import JSP198NicolasCaseIArc

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

variable {P : Finset Point} {hgp : GeneralPosition P}
  {o : Point} {ho : o ∈ inner (inner (inner P))}

def caseIStarts (R : ActualCaseIRun P hgp o ho) : Finset Point :=
  Finset.univ.image (fun j : Fin (R.length+1) =>
    matchStart P hgp o ho (orbit (chainCycle P hgp o ho) R.first j.val))

def caseISampledReplacement (R : ActualCaseIRun P hgp o ho) : Finset Point :=
  insert ((chainCycle P hgp o ho).symm R.first : Point)
    (insert (chainCycle P hgp o ho R.last : Point)
      (insert (matchEnd P hgp o ho R.last) (caseIStarts R)))

lemma caseIStarts_subset_third (R : ActualCaseIRun P hgp o ho) :
    caseIStarts R ⊆ ChainThird P := by
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  exact (matchStartEnd_edge P hgp o ho _).1

lemma caseIStarts_card (R : ActualCaseIRun P hgp o ho)
    (arc : ActualCaseIArc R) : (caseIStarts R).card = R.length+1 := by
  have hi : Function.Injective (fun j : Fin (R.length+1) =>
      matchStart P hgp o ho (orbit (chainCycle P hgp o ho) R.first j.val)) := by
    intro a b hab
    have bound (j : Fin (R.length+1)) : arc.index j < (ChainThird P).card := by
      have hm := arc.strictMono.monotone (show j ≤ ⟨R.length, by omega⟩ from by
        exact Nat.le_of_lt_succ j.isLt)
      have := arc.last_lt
      omega
    have he : orbit arc.cycle (sectorVertex P hgp o ho R.first) (arc.index a) =
        orbit arc.cycle (sectorVertex P hgp o ho R.first) (arc.index b) := by
      apply Subtype.ext
      simpa only [arc.start] using hab
    have hh : (⟨arc.index a, bound a⟩ : Fin ((ChainThird P).card)) =
        ⟨arc.index b, bound b⟩ := arc.enumeration.1 he
    exact arc.strictMono.injective (congrArg Fin.val hh)
  unfold caseIStarts
  rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]

lemma caseIEnd_not_mem_starts (R : ActualCaseIRun P hgp o ho)
    (arc : ActualCaseIArc R) : matchEnd P hgp o ho R.last ∉ caseIStarts R := by
  intro hm
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
  have hle := arc.strictMono.monotone
    (show j ≤ ⟨R.length, by omega⟩ from Nat.le_of_lt_succ j.isLt)
  have hb : arc.index j < (ChainThird P).card := by have := arc.last_lt; omega
  have he : orbit arc.cycle (sectorVertex P hgp o ho R.first) (arc.index j) =
      orbit arc.cycle (sectorVertex P hgp o ho R.first)
        (arc.index ⟨R.length, by omega⟩+1) := by
    apply Subtype.ext
    rw [arc.start, arc.finish]
    exact hj
  have hh : (⟨arc.index j, hb⟩ : Fin ((ChainThird P).card)) =
      ⟨arc.index ⟨R.length, by omega⟩+1, arc.last_lt⟩ := arc.enumeration.1 he
  have := congrArg Fin.val hh
  simp only at this
  omega

lemma caseI_outer_endpoints_ne (R : ActualCaseIRun P hgp o ho)
    (hshort : R.length+3 ≤ (ChainSecond P).card) :
    ((chainCycle P hgp o ho).symm R.first : Point) ≠
      (chainCycle P hgp o ho R.last : Point) := by
  intro he
  let f := chainCycle P hgp o ho
  have hsub : f.symm R.first = f R.last := Subtype.ext he
  have hf : R.first = f (f R.last) := by
    have hh := congrArg f hsub
    simpa only [Equiv.apply_symm_apply] using hh
  have heq : orbit f R.first 0 = orbit f R.first (R.length+2) := hf
  have hh : (⟨0, by omega⟩ : Fin ((ChainSecond P).card)) =
      ⟨R.length+2, by omega⟩ :=
    (ib_full_cycle_enumeration P hgp o ho R.first).1 heq
  have := congrArg Fin.val hh
  simp only at this
  omega

/-- Exact size of the sampled replacement; no convexity is assumed here. -/
theorem caseISampledReplacement_card (R : ActualCaseIRun P hgp o ho)
    (arc : ActualCaseIArc R) (hshort : R.length+3 ≤ (ChainSecond P).card) :
    (caseISampledReplacement R).card = R.length+4 := by
  let a := (chainCycle P hgp o ho).symm R.first
  let b := chainCycle P hgp o ho R.last
  let z := matchEnd P hgp o ho R.last
  have hz : z ∈ inner (inner P) :=
    chain_third_mem_inner2 (matchStartEnd_edge P hgp o ho R.last).2.1
  have ha : (a : Point) ∉ caseIStarts R := by
    intro hx
    exact chain_inner2_ne_second (chain_third_mem_inner2 (caseIStarts_subset_third R hx)) a rfl
  have hb : (b : Point) ∉ caseIStarts R := by
    intro hx
    exact chain_inner2_ne_second (chain_third_mem_inner2 (caseIStarts_subset_third R hx)) b rfl
  have hab : (a : Point) ≠ b := caseI_outer_endpoints_ne R hshort
  have haz : (a : Point) ≠ z := (chain_inner2_ne_second hz a).symm
  have hbz : (b : Point) ≠ z := (chain_inner2_ne_second hz b).symm
  have he : z ∉ caseIStarts R := caseIEnd_not_mem_starts R arc
  have hc := caseIStarts_card R arc
  change (insert (a : Point) (insert (b : Point) (insert z (caseIStarts R)))).card = _
  have hbi : (b : Point) ∉ insert z (caseIStarts R) := by simp [hbz, hb]
  have hai : (a : Point) ∉ insert (b : Point) (insert z (caseIStarts R)) := by
    simp [hab, haz, ha]
  rw [Finset.card_insert_of_notMem hai, Finset.card_insert_of_notMem hbi,
    Finset.card_insert_of_notMem he, hc]

theorem caseISampledReplacement_subset_inner (R : ActualCaseIRun P hgp o ho) :
    caseISampledReplacement R ⊆ inner P := by
  intro x hx
  simp only [caseISampledReplacement, Finset.mem_insert] at hx
  rcases hx with rfl | rfl | rfl | hx
  · exact hullVertices_subset _ ((chainCycle P hgp o ho).symm R.first).property
  · exact hullVertices_subset _ (chainCycle P hgp o ho R.last).property
  · exact Finset.sdiff_subset (chain_third_mem_inner2
      (matchStartEnd_edge P hgp o ho R.last).2.1)
  · exact Finset.sdiff_subset (chain_third_mem_inner2 (caseIStarts_subset_third R hx))

end JSP198.Nicolas

#print axioms JSP198.Nicolas.caseISampledReplacement_card
#print axioms JSP198.Nicolas.caseISampledReplacement_subset_inner
