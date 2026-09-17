/-
Copyright (c) 2026 JSP198 formalization contributors.
Released under the MIT license. See LICENSE.

Nicolas Theorem 4, Case I.A: pointwise sampled support -> strict
replacement-cardinality inequality -> lower bound for the actual deletion cap.

Imports the existing sampled-set/count and partial-cover developments without
modifying them. The only remaining geometric input to this assembly is the
explicit point-level predicate `SampledPointSupport` (or its convenient,
stronger version `SampledEdgeSupport`). Neither predicate contains a convexity,
cap-cover, cardinality, minimality, or empty-hexagon conclusion.

Mathematics: C. M. Nicolas, The Empty Hexagon Theorem (2007).
Underlying geometry: credited MIT sources from CollinYuanjieRen/awards,
commit b8bb4f7803f921a7970abc880291ad9372111360, and the existing JSP198 modules.
Target: Lean 4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Candidate source: not compiled in the authoring environment.
-/
import Mathlib
import JSP198NicolasCaseISampled
import JSP198NicolasPartialCover

noncomputable section
open Classical Horton

namespace JSP198.Nicolas.SampledCapAssembly
open PartialCover

variable {P : Finset Point} {hgp : GeneralPosition P}
  {o : Point} {ho : o ∈ inner (inner (inner P))}

/-- The actual oriented edges of (A,a0,...,ak,bk,B), not edges of the
unabridged third-layer arc and not a full boundary cycle. -/
def SampledEdge (R : ActualCaseIRun P hgp o ho) (u v : Point) : Prop :=
  (u = (beforeRun R : Point) ∧ v = runStart R 0) ∨
  (∃ j : ℕ, j < R.length ∧
    u = runStart R j ∧ v = runStart R (j + 1)) ∨
  (u = runStart R R.length ∧ v = runEnd R R.length) ∨
  (u = runEnd R R.length ∧ v = (afterRun R : Point))

/-- Minimal point-level input for the existing replacement theorem:
for each sampled vertex, choose an incident ACTUAL sampled edge supporting
all sampled vertices on its closed right side. Edge membership, endpoint
inequality and the strict right side for undeleted outer vertices are proved
below, not required as inputs. -/
def SampledPointSupport (R : ActualCaseIRun P hgp o ho) : Prop :=
  ∀ x ∈ caseISampledReplacement R, ∃ u v : Point,
    SampledEdge R u v ∧ (x = u ∨ x = v) ∧
      ∀ z ∈ caseISampledReplacement R, orient u v z ≤ 0

/-- Convenient stronger input when the endpoint-support task proves every
sampled edge. The theorem `pointSupport_of_edgeSupport` discharges incidence. -/
def SampledEdgeSupport (R : ActualCaseIRun P hgp o ho) : Prop :=
  ∀ u v : Point, SampledEdge R u v →
    ∀ z ∈ caseISampledReplacement R, orient u v z ≤ 0

lemma sampledReplacement_eq (R : ActualCaseIRun P hgp o ho) :
    caseISampledReplacement R =
      insert (beforeRun R : Point)
        (insert (afterRun R : Point)
          (insert (runEnd R R.length) (caseIStarts R))) := rfl

lemma before_mem_sampled (R : ActualCaseIRun P hgp o ho) :
    (beforeRun R : Point) ∈ caseISampledReplacement R := by
  rw [sampledReplacement_eq]
  exact Finset.mem_insert_self _ _

lemma after_mem_sampled (R : ActualCaseIRun P hgp o ho) :
    (afterRun R : Point) ∈ caseISampledReplacement R := by
  rw [sampledReplacement_eq]
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))

lemma end_mem_sampled (R : ActualCaseIRun P hgp o ho) :
    runEnd R R.length ∈ caseISampledReplacement R := by
  rw [sampledReplacement_eq]
  exact Finset.mem_insert.mpr (Or.inr
    (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))))

lemma start_mem_sampled (R : ActualCaseIRun P hgp o ho)
    (j : ℕ) (hj : j ≤ R.length) :
    runStart R j ∈ caseISampledReplacement R := by
  have hs : runStart R j ∈ caseIStarts R := by
    unfold caseIStarts
    exact Finset.mem_image.mpr
      ⟨(⟨j, Nat.lt_succ_of_le hj⟩ : Fin (R.length + 1)),
        Finset.mem_univ _, rfl⟩
  rw [sampledReplacement_eq]
  exact Finset.mem_insert.mpr (Or.inr
    (Finset.mem_insert.mpr (Or.inr
      (Finset.mem_insert.mpr (Or.inr hs)))))

/-- All edge endpoints belong to the already defined sampled replacement. -/
lemma sampledEdge_endpoints (R : ActualCaseIRun P hgp o ho)
    {u v : Point} (he : SampledEdge R u v) :
    u ∈ caseISampledReplacement R ∧ v ∈ caseISampledReplacement R := by
  rcases he with ⟨rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨before_mem_sampled R, start_mem_sampled R 0 (Nat.zero_le _)⟩
  · exact ⟨start_mem_sampled R j (by omega),
      start_mem_sampled R (j + 1) (by omega)⟩
  · exact ⟨start_mem_sampled R R.length (le_refl _), end_mem_sampled R⟩
  · exact ⟨end_mem_sampled R, after_mem_sampled R⟩

/-- Incidence is proved by the actual finite generating set; it is not a
separate geometric assumption. -/
lemma sampled_vertex_incident (R : ActualCaseIRun P hgp o ho)
    {x : Point} (hx : x ∈ caseISampledReplacement R) :
    ∃ u v : Point, SampledEdge R u v ∧ (x = u ∨ x = v) := by
  rw [sampledReplacement_eq] at hx
  simp only [Finset.mem_insert] at hx
  rcases hx with hA | hB | hend | hstarts
  · refine ⟨beforeRun R, runStart R 0,
      Or.inl ⟨rfl, rfl⟩, Or.inl hA⟩
  · refine ⟨runEnd R R.length, afterRun R,
      Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), Or.inr hB⟩
  · refine ⟨runEnd R R.length, afterRun R,
      Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), Or.inl hend⟩
  · obtain ⟨j, _, hjx⟩ := Finset.mem_image.mp hstarts
    have hxj : x = runStart R j.val := hjx.symm
    by_cases hj : j.val < R.length
    · exact ⟨runStart R j.val, runStart R (j.val + 1),
        Or.inr (Or.inl ⟨j.val, hj, rfl, rfl⟩), Or.inl hxj⟩
    · have hjk : j.val = R.length := by have := j.isLt; omega
      refine ⟨runStart R R.length, runEnd R R.length,
        Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), Or.inl ?_⟩
      simpa only [hjk] using hxj

lemma pointSupport_of_edgeSupport (R : ActualCaseIRun P hgp o ho)
    (hs : SampledEdgeSupport R) : SampledPointSupport R := by
  intro x hx
  obtain ⟨u, v, he, hinc⟩ := sampled_vertex_incident R hx
  exact ⟨u, v, he, hinc, hs u v he⟩

/-- Reuse the PASS exact start-count theorem: an image of the same finite
cardinality has injective indexing. This does not reprove radial order. -/
lemma starts_injective_from_count (R : ActualCaseIRun P hgp o ho)
    (arc : ActualCaseIArc R) :
    Function.Injective (fun j : Fin (R.length + 1) => runStart R j.val) := by
  let f : Fin (R.length + 1) → Point := fun j => runStart R j.val
  have hc : ((Finset.univ : Finset (Fin (R.length + 1))).image f).card =
      (Finset.univ : Finset (Fin (R.length + 1))).card := by
    calc
      ((Finset.univ : Finset (Fin (R.length + 1))).image f).card =
          (caseIStarts R).card := rfl
      _ = R.length + 1 := caseIStarts_card R arc
      _ = (Finset.univ : Finset (Fin (R.length + 1))).card := by simp
  have hi := Finset.injOn_of_card_image_eq hc
  intro i j hij
  exact hi (Finset.mem_univ i) (Finset.mem_univ j) hij

/-- Every chosen sampled edge is nondegenerate. Only the PASS arc/count
certificate is used for consecutive selected third-layer starts. -/
lemma sampledEdge_ne (R : ActualCaseIRun P hgp o ho)
    (arc : ActualCaseIArc R) {u v : Point} (he : SampledEdge R u v) :
    u ≠ v := by
  rcases he with ⟨rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (chain_inner2_ne_second
      (matchStart_mem P hgp o ho (runPoint R 0)) (beforeRun R)).symm
  · intro h
    let i : Fin (R.length + 1) := ⟨j, by omega⟩
    let l : Fin (R.length + 1) := ⟨j + 1, by omega⟩
    have hil : i = l := starts_injective_from_count R arc h
    have hval := congrArg Fin.val hil
    change j = j + 1 at hval
    omega
  · exact (matchStartEnd_edge P hgp o ho (runPoint R R.length)).2.2.1
  · exact chain_inner2_ne_second
      (matchEnd_mem P hgp o ho (runPoint R R.length)) (afterRun R)

/-- Positive orientation at ANY actual sampled edge puts an outer vertex in
exactly the original PartialCover.deletionCap. No new deletion set is used. -/
lemma mem_deletionCap_of_sampledEdge_pos (R : ActualCaseIRun P hgp o ho)
    {u v x : Point} (he : SampledEdge R u v)
    (hx : x ∈ hullVertices P) (hpos : 0 < orient u v x) :
    x ∈ deletionCap R := by
  apply Finset.mem_filter.mpr
  refine ⟨hx, ?_⟩
  rcases he with ⟨rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hpos
  · exact Or.inr (Or.inl ⟨j, Finset.mem_range.mpr hj, hpos⟩)
  · exact Or.inr (Or.inr (Or.inl hpos))
  · exact Or.inr (Or.inr (Or.inr hpos))

/-- Outside the strict deletion cap, each actual sampled edge is STRICTLY
negative. Nonpositivity comes from the cap definition; equality is excluded
by the ORIGINAL general-position predicate and layer disjointness. -/
lemma sampledEdge_neg_on_undeleted_outer
    (R : ActualCaseIRun P hgp o ho) (arc : ActualCaseIArc R)
    {u v x : Point} (he : SampledEdge R u v)
    (hx : x ∈ hullVertices P \ deletionCap R) :
    orient u v x < 0 := by
  obtain ⟨hxH, hxD⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨huT, hvT⟩ := sampledEdge_endpoints R he
  have huI := caseISampledReplacement_subset_inner R huT
  have hvI := caseISampledReplacement_subset_inner R hvT
  have huP : u ∈ P := (Finset.mem_sdiff.mp huI).1
  have hvP : v ∈ P := (Finset.mem_sdiff.mp hvI).1
  have huNot : u ∉ hullVertices P := (Finset.mem_sdiff.mp huI).2
  have hvNot : v ∉ hullVertices P := (Finset.mem_sdiff.mp hvI).2
  have hux : u ≠ x := by
    intro h
    apply huNot
    simpa only [h] using hxH
  have hvx : v ≠ x := by
    intro h
    apply hvNot
    simpa only [h] using hxH
  have hle : orient u v x ≤ 0 := by
    apply le_of_not_gt
    intro hp
    exact hxD (mem_deletionCap_of_sampledEdge_pos R he hxH hp)
  have hne : orient u v x ≠ 0 :=
    hgp u huP v hvP x (hullVertices_subset P hxH)
      (sampledEdge_ne R arc he) hux hvx
  exact lt_of_le_of_ne hle hne

/-- Complete application of the existing replacement theorem. All membership,
nonemptiness, disjointness, edge-incidence and undeleted-outer strictness
obligations are discharged here. Only point-level sampled support remains. -/
theorem sampled_replacement_card_lt_deletionCap
    (R : ActualCaseIRun P hgp o ho) (arc : ActualCaseIArc R)
    (hmin : MinimalOuter P) (hs : SampledPointSupport R) :
    (caseISampledReplacement R).card < (deletionCap R).card := by
  have hTI : caseISampledReplacement R ⊆ inner P :=
    caseISampledReplacement_subset_inner R
  have hTP : caseISampledReplacement R ⊆ P :=
    hTI.trans Finset.sdiff_subset
  have hTne : (caseISampledReplacement R).Nonempty :=
    ⟨(beforeRun R : Point), before_mem_sampled R⟩
  have hdis : Disjoint (caseISampledReplacement R) (hullVertices P) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxH
    exact (Finset.mem_sdiff.mp (hTI hx)).2 hxH
  have hD : deletionCap R ⊆ hullVertices P := Finset.filter_subset _ _
  apply replacement_card_lt P (caseISampledReplacement R) (deletionCap R)
    hgp hmin hTP hTne hdis hD
  intro x hx
  obtain ⟨u, v, he, hinc, hside⟩ := hs x hx
  obtain ⟨hu, hv⟩ := sampledEdge_endpoints R he
  refine ⟨u, hu, v, hv, sampledEdge_ne R arc he, hinc, hside, ?_⟩
  intro z hz
  exact sampledEdge_neg_on_undeleted_outer R arc he hz

/-- Exact requested finite lower bound. The already PASS sampled count is
used verbatim; no new counting proof or replacement-convexity assumption. -/
theorem deletionCap_card_ge_length_add_five
    (R : ActualCaseIRun P hgp o ho) (arc : ActualCaseIArc R)
    (hmin : MinimalOuter P)
    (hshort : R.length + 3 ≤ (ChainSecond P).card)
    (hs : SampledPointSupport R) :
    R.length + 5 ≤ (deletionCap R).card := by
  have hlt := sampled_replacement_card_lt_deletionCap R arc hmin hs
  have hc := caseISampledReplacement_card R arc hshort
  rw [hc] at hlt
  omega

/-- All-edges convenience version of the same finite lower bound. -/
theorem deletionCap_card_ge_length_add_five_of_all_edges
    (R : ActualCaseIRun P hgp o ho) (arc : ActualCaseIArc R)
    (hmin : MinimalOuter P)
    (hshort : R.length + 3 ≤ (ChainSecond P).card)
    (hs : SampledEdgeSupport R) :
    R.length + 5 ≤ (deletionCap R).card :=
  deletionCap_card_ge_length_add_five R arc hmin hshort
    (pointSupport_of_edgeSupport R hs)

/-- Case I.A once the explicit sampled support is supplied. The actual arc
is constructed from RUN-LOCAL singleton fibers by the existing PASS theorem;
the upper bound is the existing PASS partial-cap theorem. This is a proved
conditional assembly lemma, NOT an unconditional original-problem endpoint. -/
theorem hasEmptySix_of_caseIA_sampled_point_support
    (R : ActualCaseIRun P hgp o ho) (hmin : MinimalOuter P)
    (hsingle : RunHasSingletonSectors R)
    (hshort : R.length + 3 ≤ (ChainSecond P).card)
    (hs : SampledPointSupport R) : HasEmptySix P := by
  by_contra hno
  obtain ⟨arc⟩ := exists_actual_caseIArc P hgp o ho R hsingle (by omega)
  have hlow := deletionCap_card_ge_length_add_five R arc hmin hshort hs
  have hupp := actual_run_cap_card_le_of_singleton_fibers R hsingle hno
  omega

/-- Convenient integration point for the worker proving all actual support
lines. It has no global AdjacentSectorsDistinct assumption. -/
theorem hasEmptySix_of_caseIA_sampled_edge_support
    (R : ActualCaseIRun P hgp o ho) (hmin : MinimalOuter P)
    (hsingle : RunHasSingletonSectors R)
    (hshort : R.length + 3 ≤ (ChainSecond P).card)
    (hs : SampledEdgeSupport R) : HasEmptySix P :=
  hasEmptySix_of_caseIA_sampled_point_support R hmin hsingle hshort
    (pointSupport_of_edgeSupport R hs)

end JSP198.Nicolas.SampledCapAssembly

#print axioms JSP198.Nicolas.SampledCapAssembly.sampled_replacement_card_lt_deletionCap
#print axioms JSP198.Nicolas.SampledCapAssembly.deletionCap_card_ge_length_add_five
#print axioms JSP198.Nicolas.SampledCapAssembly.hasEmptySix_of_caseIA_sampled_point_support
#print axioms JSP198.Nicolas.SampledCapAssembly.hasEmptySix_of_caseIA_sampled_edge_support
