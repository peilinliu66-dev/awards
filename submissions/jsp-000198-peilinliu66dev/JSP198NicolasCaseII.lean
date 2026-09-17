/-
Copyright (c) 2026 JSP198 formalization contributors. MIT license.
Mathematical source: C. M. Nicolas (2007), complete Case II, including all
double-sector blocks. Underlying MIT geometry: CollinYuanjieRen/awards,
b8bb4f7803f921a7970abc880291ad9372111360, as credited in the bridge module.

The actual cover and its capacity bound are proved here, not assumed.
The public Case II theorem assumes only raw geometry/minimality and absence of
the precisely specified Case I run. The unconditional alternative returns that
actual Case I run or an empty convex six-set. It is NOT the full empty-hexagon
theorem until the separately assigned Case I proof is attached.

Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Candidate: not compiled in the generating environment.
-/
import Mathlib
import JSP198NicolasCaseIISelection

noncomputable section
open Classical Horton
namespace JSP198.Nicolas.CaseII

variable {P : Finset Point} {hgp : GeneralPosition P}
variable {o : Point} {ho : o ∈ inner (inner (inner P))}

/-- The start of the actual inner edge, or the actual bridge vertex. -/
def cellStart (M : MatchMask P hgp o ho) (r : ChainVertex P) : Point :=
  if M.rightSet r then matchStart P hgp o ho r
  else if M.rightSet (chainCycle P hgp o ho r)
    then bridgeVertex P hgp o ho r
    else matchStart P hgp o ho (chainCycle P hgp o ho r)

/-- The end of the actual inner edge; equal to cellStart at an L-to-R bridge. -/
def cellEnd (M : MatchMask P hgp o ho) (r : ChainVertex P) : Point :=
  if M.rightSet r then matchEnd P hgp o ho r
  else if M.rightSet (chainCycle P hgp o ho r)
    then bridgeVertex P hgp o ho r
    else matchEnd P hgp o ho (chainCycle P hgp o ho r)

lemma cellStart_mem (M : MatchMask P hgp o ho) (r : ChainVertex P) :
    cellStart M r ∈ inner (inner P) := by
  unfold cellStart
  split_ifs
  · exact matchStart_mem P hgp o ho r
  · exact chain_third_mem_inner2 (bridgeVertex_mem_third P hgp o ho r)
  · exact matchStart_mem P hgp o ho (chainCycle P hgp o ho r)

lemma cellEnd_mem (M : MatchMask P hgp o ho) (r : ChainVertex P) :
    cellEnd M r ∈ inner (inner P) := by
  unfold cellEnd
  split_ifs
  · exact matchEnd_mem P hgp o ho r
  · exact chain_third_mem_inner2 (bridgeVertex_mem_third P hgp o ho r)
  · exact matchEnd_mem P hgp o ho (chainCycle P hgp o ho r)

lemma different_of_left (M : MatchMask P hgp o ho) (r : ChainVertex P)
    (hr : ¬ M.rightSet r) :
    sectorEdge P hgp o ho r ≠
      sectorEdge P hgp o ho (chainCycle P hgp o ho r) := by
  intro he
  exact hr ((M.resets r).mp he).1

lemma different_of_next_right (M : MatchMask P hgp o ho) (r : ChainVertex P)
    (hv : M.rightSet (chainCycle P hgp o ho r)) :
    sectorEdge P hgp o ho r ≠
      sectorEdge P hgp o ho (chainCycle P hgp o ho r) := by
  intro he
  exact ((M.resets r).mp he).2 hv

lemma left_match_next_outward (M : MatchMask P hgp o ho) (r : ChainVertex P)
    (hv : ¬ M.rightSet (chainCycle P hgp o ho r)) :
    0 < orient (matchStart P hgp o ho (chainCycle P hgp o ho r))
      (matchEnd P hgp o ho (chainCycle P hgp o ho r)) (r : Point) := by
  have hh := M.left_ok (chainCycle P hgp o ho r) hv
  simpa only [CanMatchLeft, Equiv.symm_apply_apply] using hh

/-- Every nondegenerate selected cell is an actual matched quadrilateral.
At a bridge the two inner endpoints coincide, as accepted by coherent_strips_cover. -/
theorem cell_shape (M : MatchMask P hgp o ho) (r : ChainVertex P) :
    cellStart M r = cellEnd M r ∨
      (0 < orient (r : Point) (cellStart M r) (cellEnd M r) ∧
       0 < orient (r : Point) (cellStart M r) (chainCycle P hgp o ho r : Point) ∧
       0 < orient (r : Point) (cellEnd M r) (chainCycle P hgp o ho r : Point) ∧
       0 < orient (cellStart M r) (cellEnd M r) (chainCycle P hgp o ho r : Point)) := by
  by_cases hr : M.rightSet r
  · right
    simp only [cellStart, cellEnd, if_pos hr]
    exact boundary_match_four_signs P hgp r (chainCycle P hgp o ho r)
      (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
      (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho r)
      (sectorEdge_outward P hgp o ho r) (M.right_ok r hr)
  · by_cases hv : M.rightSet (chainCycle P hgp o ho r)
    · left
      simp only [cellStart, cellEnd, if_neg hr, if_pos hv]
    · right
      simp only [cellStart, cellEnd, if_neg hr, if_neg hv]
      exact boundary_match_four_signs P hgp r (chainCycle P hgp o ho r)
        (matchStart P hgp o ho (chainCycle P hgp o ho r))
        (matchEnd P hgp o ho (chainCycle P hgp o ho r))
        (chainCycle_edge P hgp o ho r)
        (matchStartEnd_edge P hgp o ho (chainCycle P hgp o ho r))
        (left_match_next_outward M r hv)
        (sectorEdge_outward P hgp o ho (chainCycle P hgp o ho r))

/-- At a left-labelled vertex, the incoming cell ends at that vertex's sector
endpoint, even when it is the second vertex of a double-sector reset. -/
lemma incoming_end_at_left_vertex (M : MatchMask P hgp o ho) (r : ChainVertex P)
    (hv : ¬ M.rightSet (chainCycle P hgp o ho r)) :
    cellEnd M r = matchEnd P hgp o ho (chainCycle P hgp o ho r) := by
  by_cases hr : M.rightSet r
  · simp only [cellEnd, if_pos hr]
    have he := (M.resets r).mpr ⟨hr,hv⟩
    change (sectorEdge P hgp o ho r).val.2 =
      (sectorEdge P hgp o ho (chainCycle P hgp o ho r)).val.2
    rw [show sectorEdge P hgp o ho r =
      sectorEdge P hgp o ho (chainCycle P hgp o ho r) from he]
  · simp only [cellEnd, if_neg hr, if_neg hv]

/-- Complete local coherence, including both ends of every bridge and every
zero-capacity double-sector reset. -/
theorem cell_join (M : MatchMask P hgp o ho) (r : ChainVertex P) :
    0 ≤ orient (chainCycle P hgp o ho r : Point)
      (cellEnd M r) (cellStart M (chainCycle P hgp o ho r)) := by
  let f := chainCycle P hgp o ho
  by_cases hv : M.rightSet (f r)
  all_goals dsimp only [f] at hv
  · by_cases hr : M.rightSet r
    · simp only [cellStart, cellEnd, if_pos hr, if_pos hv]
      exact right_radial_join_coherent P hgp o ho r
        (different_of_next_right M r hv) (M.right_ok r hr)
    · simp only [cellStart, cellEnd, if_neg hr, if_pos hv]
      exact (bridgeVertex_join P hgp o ho r (different_of_left M r hr)).2
  · rw [incoming_end_at_left_vertex M r hv]
    by_cases hw : M.rightSet (f (f r))
    all_goals dsimp only [f] at hw
    · simp only [cellStart, if_neg hv, if_pos hw]
      exact (bridgeVertex_join P hgp o ho (f r) (different_of_left M (f r) hv)).1
    · simp only [cellStart, if_neg hv, if_neg hw]
      exact left_radial_join_coherent P hgp o ho (f r)
        (different_of_left M (f r) hv) (M.left_ok (f (f r)) hw)

/-- ACTUAL global covering. The mask does not store this property: the preceding
geometric shape/join lemmas discharge every hypothesis of coherent_strips_cover. -/
theorem mask_covers_outer (M : MatchMask P hgp o ho) :
    ∀ x ∈ hullVertices P, ∃ r : ChainVertex P,
      x ∈ stripCell P r (chainCycle P hgp o ho r) (cellStart M r) (cellEnd M r) :=
  coherent_strips_cover P hgp o ho (cellStart M) (cellEnd M)
    (cellStart_mem M) (cellEnd_mem M) (cell_shape M) (cell_join M)

/-- One exact budget per actual second-layer edge:
ordinary matching <= 1, double-sector reset = 0, bridge fan <= 2. -/
theorem cell_capacity_budget (hno : ¬ HasEmptySix P)
    (M : MatchMask P hgp o ho) (r : ChainVertex P) :
    (stripCell P r (chainCycle P hgp o ho r) (cellStart M r) (cellEnd M r)).card +
        (if M.rightSet r ∧ ¬ M.rightSet (chainCycle P hgp o ho r) then 1 else 0) ≤
      1 + (if ¬ M.rightSet r ∧ M.rightSet (chainCycle P hgp o ho r) then 1 else 0) := by
  let f := chainCycle P hgp o ho
  by_cases hr : M.rightSet r
  · by_cases hv : M.rightSet (f r)
    all_goals dsimp only [f] at hv
    · have hcap := boundary_match_channel_le_one P hgp hno r (f r)
        (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
        (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho r)
        (sectorEdge_outward P hgp o ho r) (M.right_ok r hr)
      simp only [cellStart, cellEnd, if_pos hr]
      rw [stripCell_eq_matchChannel _ _ _ _ _
        (matchStartEnd_edge P hgp o ho r).2.2.1]
      simpa [hr, hv] using hcap
    · have hD := (M.resets r).mpr ⟨hr,hv⟩
      have hempty := double_sector_channel_eq_empty P hgp hno o ho r hD
      simp only [cellStart, cellEnd, if_pos hr]
      rw [stripCell_eq_matchChannel _ _ _ _ _
        (matchStartEnd_edge P hgp o ho r).2.2.1, hempty]
      simp [hr, hv]
  · by_cases hv : M.rightSet (f r)
    all_goals dsimp only [f] at hv
    · have hcap := bridge_fan_card_le_two P hgp hno o ho r
      simp only [cellStart, cellEnd, if_neg hr, if_pos hv]
      rw [stripCell_self_eq_outerFan]
      simpa [hr, hv] using hcap
    · have hcap := boundary_match_channel_le_one P hgp hno r (f r)
        (matchStart P hgp o ho (f r)) (matchEnd P hgp o ho (f r))
        (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho (f r))
        (left_match_next_outward M r hv) (sectorEdge_outward P hgp o ho (f r))
      simp only [cellStart, cellEnd, if_neg hr, if_neg hv]
      rw [stripCell_eq_matchChannel _ _ _ _ _
        (matchStartEnd_edge P hgp o ho (f r)).2.2.1]
      simpa [hr, hv] using hcap

/-- Balanced reset/bridge counts give total capacity at most the actual number
of second-layer vertices. This covers arbitrarily many double sectors and all
lengths of intervening singleton-sector blocks simultaneously. -/
theorem mask_outer_card_le_second (hno : ¬ HasEmptySix P)
    (M : MatchMask P hgp o ho) :
    (hullVertices P).card ≤ (ChainSecond P).card := by
  have hcover := coherent_strips_card_le P hgp o ho (cellStart M) (cellEnd M)
    (cellStart_mem M) (cellEnd_mem M) (cell_shape M) (cell_join M)
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset (ChainVertex P)))
    (fun r _ => cell_capacity_budget hno M r)
  simp only [Finset.sum_add_distrib] at hsum
  have hbal := transition_balance (chainCycle P hgp o ho) M.rightSet
  rw [hbal] at hsum
  have hones : (∑ _r : ChainVertex P, (1 : ℕ)) = (ChainSecond P).card := by
    simp [ChainVertex]
  rw [hones] at hsum
  omega

/-- Complete Case II terminal. The sole branch hypothesis is absence of an
actual Case I run; there is NO cover, coherence, bridge or convexity hypothesis. -/
theorem hasEmptySix_of_no_separated_run
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hII : ¬ Nonempty (SeparatedRun P hgp o ho)) :
    HasEmptySix P := by
  by_contra hno
  obtain ⟨M⟩ := exists_matchMask P hgp hmin hno o ho hII
  have hle := mask_outer_card_le_second hno M
  have hRne : (ChainSecond P).Nonempty := Finset.card_pos.mp (by
    have h3 := chain_second_card_ge_three P hgp o ho
    omega)
  have hlt := second_card_lt_outer P hmin hRne
  omega

/-- An unconditional raw-geometry alternative for the separate Case I worker.
No auxiliary matching assumptions occur. This is a reduction to Case I, not a
claim that the separately assigned Case I has already been solved here. -/
theorem emptySix_or_separated_caseI
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) :
    HasEmptySix P ∨ Nonempty (SeparatedRun P hgp o ho) := by
  by_cases hI : Nonempty (SeparatedRun P hgp o ho)
  · exact Or.inr hI
  · exact Or.inl (hasEmptySix_of_no_separated_run P hgp hmin o ho hI)

end JSP198.Nicolas.CaseII

namespace JSP198.Nicolas

/-- Stable public name for the complete Case II branch. -/
theorem hasEmptySix_of_caseII
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hcaseII : ¬ Nonempty (CaseII.SeparatedRun P hgp o ho)) :
    HasEmptySix P :=
  CaseII.hasEmptySix_of_no_separated_run P hgp hmin o ho hcaseII

/-- Public adapter to the EXISTING ActualCaseIRun interface. Every sector
represented in the returned run is globally singleton. Vertices outside that
run are deliberately NOT required to have distinct sectors. -/
theorem emptySix_or_actual_singleton_run
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) :
    HasEmptySix P ∨
      ∃ R : ActualCaseIRun P hgp o ho,
        ∀ j : Fin (R.length + 1), ∀ s : ChainVertex P,
          sectorEdge P hgp o ho s =
            sectorEdge P hgp o ho (orbit (chainCycle P hgp o ho) R.first j.val) →
          s = orbit (chainCycle P hgp o ho) R.first j.val := by
  by_cases hno : HasEmptySix P
  · exact Or.inl hno
  rcases CaseII.emptySix_or_separated_caseI P hgp hmin o ho with h | hR
  · exact (hno h).elim
  · obtain ⟨R⟩ := hR
    right
    refine ⟨R.run, ?_⟩
    intro j s he
    exact CaseII.SeparatedRun.sector_fiber_unique hno R j s he

end JSP198.Nicolas

#print axioms JSP198.Nicolas.CaseII.mask_covers_outer
#print axioms JSP198.Nicolas.CaseII.mask_outer_card_le_second
#print axioms JSP198.Nicolas.CaseII.emptySix_or_separated_caseI
#print axioms JSP198.Nicolas.hasEmptySix_of_caseII

#print axioms JSP198.Nicolas.emptySix_or_actual_singleton_run
