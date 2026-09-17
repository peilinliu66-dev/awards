/-
Released under the MIT license.
Nicolas Theorem 4, complete Case I.C (full-length singleton-sector runs).
Imports the actual previous matching construction and the user's PASS
OnePointGlue. Both left/right chord alternatives are handled explicitly:
no unproved reflection of a right-matching run is used.
-/
import Mathlib
import JSP198NicolasCaseICGeometry

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

/-- Finite saturation used only after an actual geometric cover has been proved. -/
private lemma ic_saturated_cover_nonempty
    {A : Type*} [Fintype A] [DecidableEq A]
    (X : Finset Point) (cells : A → Finset Point) (last r0 : A)
    (hr0 : r0 ≠ last)
    (hcover : ∀ x ∈ X, ∃ r : A, x ∈ cells r)
    (hbound : ∀ r : A, (cells r).card ≤ 1 + if r = last then 1 else 0)
    (hcard : X.card = Fintype.card A + 1) : (cells r0).Nonempty := by
  by_contra hn
  have he : cells r0 = ∅ := by
    rcases (cells r0).eq_empty_or_nonempty with h | h
    · exact h
    · exact (hn h).elim
  have hc := card_le_sum_of_cover X (Finset.univ : Finset A) cells (by
    intro x hx
    obtain ⟨r,hr⟩ := hcover x hx
    exact ⟨r,Finset.mem_univ _,hr⟩)
  have hi : ∀ r : A,
      (cells r).card + (if r = r0 then 1 else 0 : ℕ) ≤
        1 + if r = last then 1 else 0 := by
    intro r
    by_cases hr : r = r0
    · subst r
      simp [he, hr0]
    · simpa only [if_neg hr,Nat.add_zero] using hbound r
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset A)) => hi r)
  have hsum : (∑ r : A, (cells r).card) + 1 ≤ Fintype.card A + 1 := by
    simpa [Finset.sum_add_distrib] using hs
  omega

/-- In the tight one-fan cover every ordinary right channel is occupied.
This conclusion uses the actual Case I.C cover, not a supplied cover premise. -/
theorem caseIC_right_channel_nonempty
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho)
    (last : ChainVertex P)
    (hright : ∀ r : ChainVertex P, r ≠ last → CanMatchRight P hgp o ho r)
    (htight : (hullVertices P).card = (ChainSecond P).card + 1)
    (r0 : ChainVertex P) (hr0 : r0 ≠ last) :
    (matchChannel P r0 (chainCycle P hgp o ho r0)
      (matchStart P hgp o ho r0) (matchEnd P hgp o ho r0)).Nonempty := by
  let f := chainCycle P hgp o ho
  let first := f last
  let z := matchStart P hgp o ho first
  let cells := fun r : ChainVertex P =>
    if r = last then outerFan P z (last,first)
    else matchChannel P r (f r) (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
  have hcover : ∀ x ∈ hullVertices P, ∃ r : ChainVertex P, x ∈ cells r := by
    intro x hx
    rcases caseIC_one_fan_cover P hgp o ho hdiff last hright x hx with h | ⟨r,hr,h⟩
    · exact ⟨last,by simpa only [cells,if_pos rfl] using h⟩
    · exact ⟨r,by simpa only [cells,if_neg hr] using h⟩
  have hbound : ∀ r : ChainVertex P, (cells r).card ≤ 1 + if r = last then 1 else 0 := by
    intro r
    by_cases hr : r = last
    · have hz := matchStart_mem P hgp o ho first
      have hh := outerFan_card_le_two P hgp hno z (Finset.mem_sdiff.mp hz).1
        (last,first) (chainCycle_edge P hgp o ho last)
        (chain_inner2_ne_second hz last) (chain_inner2_ne_second hz first)
      simpa only [cells,if_pos hr] using hh
    · have hh := boundary_match_channel_le_one P hgp hno r (f r)
        (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
        (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho r)
        (sectorEdge_outward P hgp o ho r) (hright r hr)
      simpa only [cells,if_neg hr,Nat.add_zero] using hh
  have hcard : (hullVertices P).card = Fintype.card (ChainVertex P) + 1 := by
    have hCard : Fintype.card (ChainVertex P) = (ChainSecond P).card :=
      Fintype.card_coe _
    rw [hCard]
    exact htight
  have hh := ic_saturated_cover_nonempty (hullVertices P) cells last r0 hr0
    hcover hbound hcard
  simpa only [cells,if_neg hr0] using hh

/-- A SECOND tight cover replaces the penultimate right channel by the last
vertex's left channel. Exact inner successors prove all junctions. This is
needed for the left chord alternative; symmetry of a right run is not assumed. -/
theorem caseIC_left_end_channel_nonempty
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (last : ChainVertex P)
    (hright : ∀ r : ChainVertex P, r ≠ last → CanMatchRight P hgp o ho r)
    (hleft : CanMatchLeft P hgp o ho last)
    (htight : (hullVertices P).card = (ChainSecond P).card + 1)
    (hsucc : ∀ r : ChainVertex P,
      matchEnd P hgp o ho r = matchStart P hgp o ho (chainCycle P hgp o ho r)) :
    (matchChannel P ((chainCycle P hgp o ho).symm last) last
      (matchStart P hgp o ho last) (matchEnd P hgp o ho last)).Nonempty := by
  let f := chainCycle P hgp o ho
  let t := f.symm last
  let first := f last
  let z := matchStart P hgp o ho first
  let a := matchStart P hgp o ho last
  have hft : f t = last := f.apply_symm_apply last
  have hend : matchEnd P hgp o ho last = z := hsucc last
  have htl : t ≠ last := by
    intro he
    have hh := (chainCycle_edge P hgp o ho t).2.2.1
    exact hh (by rw [hft,he])
  have hfirstL : first ≠ last := by
    intro he
    exact (chainCycle_edge P hgp o ho last).2.2.1
      (congrArg (fun r : ChainVertex P => (r : Point)) he).symm
  have hgR := gp_subset hgp ((hullVertices_subset (inner P)).trans Finset.sdiff_subset)
  have hR3 := chain_second_card_ge_three P hgp o ho
  have htlE : BoundaryEdge (ChainSecond P) t last := by
    have hh := chainCycle_edge P hgp o ho t
    change BoundaryEdge (ChainSecond P) t (f t) at hh
    rwa [hft] at hh
  have hlfE : BoundaryEdge (ChainSecond P) last first := chainCycle_edge P hgp o ho last
  have htf := boundary_neighbors_ne (ChainSecond P) hgR hR3 t last first htlE hlfE
  have hfirstT : first ≠ t := by
    intro he
    exact htf (congrArg (fun r : ChainVertex P => (r : Point)) he).symm
  let c := fun r : ChainVertex P =>
    if r = last then z else if r = t then a else matchStart P hgp o ho r
  let d := fun r : ChainVertex P =>
    if r = last then z else if r = t then z else matchEnd P hgp o ho r
  have hzII : z ∈ inner (inner P) := matchStart_mem P hgp o ho first
  have haII : a ∈ inner (inner P) := matchStart_mem P hgp o ho last
  have hc : ∀ r : ChainVertex P, c r ∈ inner (inner P) := by
    intro r
    by_cases hr : r = last
    · simpa only [c,if_pos hr] using hzII
    · by_cases ht : r = t
      · simpa only [c,if_neg hr,if_pos ht] using haII
      · simpa only [c,if_neg hr,if_neg ht] using matchStart_mem P hgp o ho r
  have hd : ∀ r : ChainVertex P, d r ∈ inner (inner P) := by
    intro r
    by_cases hr : r = last
    · simpa only [d,if_pos hr] using hzII
    · by_cases ht : r = t
      · simpa only [d,if_neg hr,if_pos ht] using hzII
      · simpa only [d,if_neg hr,if_neg ht] using matchEnd_mem P hgp o ho r
  have htface : 0 < orient a z (t : Point) := by
    have hh := hleft
    change 0 < orient a (matchEnd P hgp o ho last) (t : Point) at hh
    rwa [hend] at hh
  have hlastface : 0 < orient a z (last : Point) := by
    have hh := sectorEdge_outward P hgp o ho last
    change 0 < orient a (matchEnd P hgp o ho last) (last : Point) at hh
    rwa [hend] at hh
  have heAZ : BoundaryEdge (ChainThird P) a z := by
    have hh := matchStartEnd_edge P hgp o ho last
    rwa [hend] at hh
  have hshape : ∀ r : ChainVertex P, c r = d r ∨
      (0 < orient (r : Point) (c r) (d r) ∧
       0 < orient (r : Point) (c r) (f r : Point) ∧
       0 < orient (r : Point) (d r) (f r : Point) ∧
       0 < orient (c r) (d r) (f r : Point)) := by
    intro r
    by_cases hr : r = last
    · left; simp only [c,d,if_pos hr]
    · by_cases ht : r = t
      · subst r
        right
        simp only [c,d,if_neg htl,if_pos rfl,hft]
        exact boundary_match_four_signs P hgp t last a z htlE heAZ htface hlastface
      · right
        simp only [c,d,if_neg hr,if_neg ht]
        exact boundary_match_four_signs P hgp r (f r)
          (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
          (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho r)
          (sectorEdge_outward P hgp o ho r) (hright r hr)
  have hgap : ∀ r : ChainVertex P, 0 ≤ orient (f r : Point) (d r) (c (f r)) := by
    intro r
    by_cases hr : r = last
    · subst r
      change 0 ≤ orient (first : Point) (d last) (c first)
      simp only [c,d,if_pos rfl,if_neg hfirstL,if_neg hfirstT]
      change 0 ≤ orient (first : Point) z z
      unfold orient
      nlinarith
    · by_cases ht : r = t
      · subst r
        simp only [c,d,if_neg htl,if_pos rfl,hft]
        simp only [ite_true]
        unfold orient
        nlinarith
      · have hnlast : f r ≠ last := by
          intro he
          exact ht (f.injective (he.trans hft.symm))
        by_cases hnt : f r = t
        · simp only [c,d,if_neg hr,if_neg ht,if_neg hnlast,if_pos hnt]
          have he1 : matchEnd P hgp o ho r = matchStart P hgp o ho t := by
            have hh := hsucc r
            change matchEnd P hgp o ho r = matchStart P hgp o ho (f r) at hh
            rwa [hnt] at hh
          have he2 : a = matchEnd P hgp o ho t := by
            have hh := hsucc t
            change matchEnd P hgp o ho t = matchStart P hgp o ho (f t) at hh
            rw [hft] at hh
            exact hh.symm
          rw [hnt,he1,he2]
          have hh := sectorEdge_outward P hgp o ho t
          change 0 < orient (matchStart P hgp o ho t) (matchEnd P hgp o ho t) (t : Point) at hh
          rw [orient_rotate (t : Point) (matchStart P hgp o ho t)
            (matchEnd P hgp o ho t)]
          exact hh.le
        · simp only [c,d,if_neg hr,if_neg ht,if_neg hnlast,if_neg hnt]
          have hh : matchEnd P hgp o ho r = matchStart P hgp o ho (f r) := hsucc r
          rw [hh]
          unfold orient
          nlinarith
  let cells := fun r : ChainVertex P => stripCell P r (f r) (c r) (d r)
  have hcover : ∀ x ∈ hullVertices P, ∃ r : ChainVertex P, x ∈ cells r :=
    coherent_strips_cover P hgp o ho c d hc hd hshape hgap
  have hbound : ∀ r : ChainVertex P, (cells r).card ≤ 1 + if r = last then 1 else 0 := by
    intro r
    by_cases hr : r = last
    · subst r
      have he : cells last = outerFan P z (last,first) := by
        dsimp only [cells]
        simp only [c,d,if_pos rfl]
        exact stripCell_self_eq_outerFan P last first z
      rw [he,if_pos rfl]
      exact outerFan_card_le_two P hgp hno z (Finset.mem_sdiff.mp hzII).1
        (last,first) hlfE (chain_inner2_ne_second hzII last)
        (chain_inner2_ne_second hzII first)
    · by_cases ht : r = t
      · subst r
        have he : cells t = matchChannel P t last a z := by
          dsimp only [cells]
          simp only [c,d,if_neg htl,if_pos rfl,hft]
          exact stripCell_eq_matchChannel P t last a z heAZ.2.2.1
        rw [he,if_neg htl,Nat.add_zero]
        exact boundary_match_channel_le_one P hgp hno t last a z htlE heAZ htface hlastface
      · have he : cells r = matchChannel P r (f r)
            (matchStart P hgp o ho r) (matchEnd P hgp o ho r) := by
          dsimp only [cells]
          simp only [c,d,if_neg hr,if_neg ht]
          exact stripCell_eq_matchChannel _ _ _ _ _ (matchStartEnd_edge P hgp o ho r).2.2.1
        rw [he,if_neg hr,Nat.add_zero]
        exact boundary_match_channel_le_one P hgp hno r (f r)
          (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
          (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho r)
          (sectorEdge_outward P hgp o ho r) (hright r hr)
  have hcard : (hullVertices P).card = Fintype.card (ChainVertex P) + 1 := by
    have hCard : Fintype.card (ChainVertex P) = (ChainSecond P).card :=
      Fintype.card_coe _
    rw [hCard]
    exact htight
  have hnon := ic_saturated_cover_nonempty (hullVertices P) cells last t htl
    hcover hbound hcard
  have he : cells t = matchChannel P t last a z := by
    dsimp only [cells]
    simp only [c,d,if_neg htl,if_pos rfl,hft]
    exact stripCell_eq_matchChannel P t last a z heAZ.2.2.1
  rw [he] at hnon
  simpa only [hend] using hnon

private lemma ic_inner_edge_second_ne
    (P : Finset Point) (hgp : GeneralPosition P)
    (a b : Point) (ha : a ∈ inner (inner P)) (hb : b ∈ inner (inner P))
    (hab : a ≠ b) (r : ChainVertex P) : orient a b r ≠ 0 := by
  exact hgp a (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ha).1).1
    b (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hb).1).1
    r (Finset.mem_sdiff.mp (chain_second_mem_inner r)).1
    hab (chain_inner2_ne_second ha r) (chain_inner2_ne_second hb r)

/-- Complete original Case I.C: a full Case-I run cannot occur in an actual
minimal-outer counterexample. No further geometric, covering or SAT premise.
The arbitrary size of the middle layers, including size three, is permitted. -/
theorem hasEmptySix_of_full_caseI_run
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho)
    (R : ActualCaseIRun P hgp o ho)
    (hfull : R.length + 1 = (ChainSecond P).card) : HasEmptySix P := by
  by_contra hno
  obtain ⟨hsize,htight,hbij,hsucc⟩ := R.tight_structure_of_full hmin hno hdiff hfull
  let f := chainCycle P hgp o ho
  let l := R.last
  let s := R.first
  let t := f.symm l
  let u := f s
  let c := matchStart P hgp o ho l
  let z := matchStart P hgp o ho s
  let d := matchEnd P hgp o ho s
  have hclose : f l = s := R.cycle_closes_of_full hfull
  have hpred : f.symm s = l := by rw [← hclose,Equiv.symm_apply_apply]
  have hft : f t = l := f.apply_symm_apply l
  have hend : matchEnd P hgp o ho l = z := by
    have hh := hsucc l
    change matchEnd P hgp o ho l = matchStart P hgp o ho (f l) at hh
    rw [hclose] at hh
    exact hh
  have hright := R.right_everywhere_except_last_of_full hfull
  have hleft := R.end_canMatchLeft hmin hno
  have hsl : s ≠ l := R.first_ne_last
  have htl : BoundaryEdge (ChainSecond P) t l := by
    have hh := chainCycle_edge P hgp o ho t
    change BoundaryEdge (ChainSecond P) t (f t) at hh
    rwa [hft] at hh
  have hls : BoundaryEdge (ChainSecond P) l s := by
    have hh := chainCycle_edge P hgp o ho l
    change BoundaryEdge (ChainSecond P) l (f l) at hh
    rwa [hclose] at hh
  have hsu : BoundaryEdge (ChainSecond P) s u := chainCycle_edge P hgp o ho s
  have hcz : BoundaryEdge (ChainThird P) c z := by
    have hh := matchStartEnd_edge P hgp o ho l
    rwa [hend] at hh
  have hzd : BoundaryEdge (ChainThird P) z d := matchStartEnd_edge P hgp o ho s
  have hc := chain_third_mem_inner2 hcz.1
  have hz := chain_third_mem_inner2 hcz.2.1
  have hd := chain_third_mem_inner2 hzd.2.1
  have hgI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hgII := gp_subset hgI (show inner (inner P) ⊆ inner P from Finset.sdiff_subset)
  have hgQ := gp_subset hgII (hullVertices_subset (inner (inner P)))
  have hQ3 : 3 ≤ (ChainThird P).card :=
    three_le_hull_of_inner_nonempty (inner (inner P)) hgII ⟨o,ho⟩
  have hcd := boundary_neighbors_ne (ChainThird P) hgQ hQ3 c z d hcz hzd
  have htri := hcz.strict hgQ hzd.2.1 hcd.symm hzd.2.2.1.symm
  have hct : 0 < orient c z t := by
    change 0 < orient c (matchEnd P hgp o ho l) (t : Point) at hleft
    rwa [hend] at hleft
  have hcl : 0 < orient c z l := by
    have hh := sectorEdge_outward P hgp o ho l
    change 0 < orient c (matchEnd P hgp o ho l) (l : Point) at hh
    rwa [hend] at hh
  have hds : 0 < orient z d s := sectorEdge_outward P hgp o ho s
  have hdu : 0 < orient z d u := hright s hsl
  have hcs : orient c z s < 0 := by
    have hn : ¬ 0 < orient c z s := by
      intro h
      apply R.noRight_end
      change 0 < orient c (matchEnd P hgp o ho l) (f l : Point)
      simpa only [hend,hclose] using h
    exact lt_of_le_of_ne (le_of_not_gt hn)
      (ic_inner_edge_second_ne P hgp c z hc hz hcz.2.2.1 s)
  have hdl : orient z d l < 0 := by
    have hn : ¬ 0 < orient z d l := by
      intro h
      apply R.noLeft
      change 0 < orient z d (f.symm s : Point)
      simpa only [hpred] using h
    exact lt_of_le_of_ne (le_of_not_gt hn)
      (ic_inner_edge_second_ne P hgp z d hz hd hzd.2.2.1 l)
  by_cases hU : 0 < orient c d u
  · have hempty := ic_right_channel_empty P hgp hno s u c z d
      hsu hcz hzd htri hcs hds hdu hU
    have hnon := caseIC_right_channel_nonempty P hgp hno o ho hdiff l hright htight s hsl
    change (matchChannel P s u z d).Nonempty at hnon
    rw [hempty] at hnon
    exact Finset.not_nonempty_empty hnon
  have hUne : orient c d u ≠ 0 := ic_inner_edge_second_ne P hgp c d hc hd hcd u
  have hUn : orient c d u < 0 := lt_of_le_of_ne (le_of_not_gt hU) hUne
  by_cases hT : 0 < orient c d t
  · have hempty := ic_left_channel_empty P hgp hno t l c z d
      htl hcz hzd htri hct hcl hdl hT
    have hL : CanMatchLeft P hgp o ho l := R.end_canMatchLeft hmin hno
    have hnon := caseIC_left_end_channel_nonempty P hgp hno o ho l hright hL htight hsucc
    change (matchChannel P t l c (matchEnd P hgp o ho l)).Nonempty at hnon
    rw [hend,hempty] at hnon
    exact Finset.not_nonempty_empty hnon
  have hTne : orient c d t ≠ 0 := ic_inner_edge_second_ne P hgp c d hc hd hcd t
  have hTn : orient c d t < 0 := lt_of_le_of_ne (le_of_not_gt hT) hTne
  exact hno (hasEmptySix_of_ic_middle_chord_negative P hgp hmin t l s u c z d
    htl hls hsu hcz hzd htri hct hcl hds hdu hTn hUn)

/-- In a counterexample only the two SHORT run branches remain after this file. -/
theorem ActualCaseIRun.length_add_two_le
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hmin : MinimalOuter P) (hno : ¬HasEmptySix P)
    (hdiff : AdjacentSectorsDistinct P hgp o ho) :
    R.length + 2 ≤ (ChainSecond P).card := by
  have hs := R.shorter
  have hn : R.length + 1 ≠ (ChainSecond P).card := by
    intro he
    exact hno (hasEmptySix_of_full_caseI_run P hgp hmin o ho hdiff R he)
  omega

/-- Exact original singleton-sector classification after eliminating I.C.
The two alternatives on the right are precisely I.A and I.B, not a weakened
six-hole assertion and not an added geometric condition. -/
theorem caseI_reduction_to_A_or_B
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho) :
    HasEmptySix P ∨ ∃ R : ActualCaseIRun P hgp o ho,
      R.length + 3 ≤ (ChainSecond P).card ∨
        R.length + 2 = (ChainSecond P).card := by
  by_cases hno : HasEmptySix P
  · exact Or.inl hno
  obtain ⟨R⟩ := exists_actual_caseI_run P hgp hmin hno o ho hdiff
  have hlen := R.length_add_two_le hmin hno hdiff
  exact Or.inr ⟨R,by omega⟩

#print axioms hasEmptySix_of_full_caseI_run
#print axioms caseI_reduction_to_A_or_B

end JSP198.Nicolas
