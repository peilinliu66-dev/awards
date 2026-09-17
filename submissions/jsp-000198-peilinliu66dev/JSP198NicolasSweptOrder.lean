/-
Released under the MIT license.
Real radial sweeps, sector injectivity, and the tight layer counts used in
Nicolas Case I.C. No cyclic-order hypothesis is postulated.
-/
import Mathlib
import JSP198NicolasRadialCoherence

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

/-- On a change of sectors, the starting vertex of the next inner edge is
crossed by the actual outer boundary edge. This is strict radial order. -/
theorem next_sector_start_in_swept_edge
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P)
    (hdiff : sectorEdge P hgp o ho r ≠
      sectorEdge P hgp o ho (chainCycle P hgp o ho r)) :
    InFan o r (chainCycle P hgp o ho r)
      (matchStart P hgp o ho (chainCycle P hgp o ho r)) := by
  let v := chainCycle P hgp o ho r
  let a := matchStart P hgp o ho v
  let b := matchEnd P hgp o ho v
  have he := matchStartEnd_edge P hgp o ho v
  have hf : InFan o a b v := sectorEdge_inFan P hgp o ho v
  have hn : ¬InFan o a b r := by
    intro hh
    apply hdiff
    exact Subtype.ext (sectorEdge_unique P hgp o ho r (a,b) he hh)
  have hgI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hgII := gp_subset hgI (show inner (inner P) ⊆ inner P from Finset.sdiff_subset)
  have hab := boundaryEdge_inner_strict (inner (inner P)) hgII o ho a b he
  have huv := boundaryEdge_inner_strict (inner P) hgI o
    (Finset.mem_sdiff.mp ho).1 r v (chainCycle_edge P hgp o ho r)
  have hgen := root_third_second_general P hgp o ho a he.1 r
  have hentry := fan_entry_crosses_first_ray o a b r v hab huv hn hf hgen
  constructor
  · have hh : orient (r : Point) o a = orient o a r := by unfold orient; ring
    rw [hh]; exact hentry
  · have hh : orient o v a = orient a o v := by unfold orient; ring
    rw [hh]; exact hf.1

/-- The ending vertex of the previous inner edge is crossed by the same actual
outer boundary edge. Together with unique-ray exit, this forbids skipping a
represented inner vertex in a tight configuration. -/
theorem previous_sector_end_in_swept_edge
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P)
    (hdiff : sectorEdge P hgp o ho r ≠
      sectorEdge P hgp o ho (chainCycle P hgp o ho r)) :
    InFan o r (chainCycle P hgp o ho r) (matchEnd P hgp o ho r) := by
  let v := chainCycle P hgp o ho r
  let c := matchStart P hgp o ho r
  let d := matchEnd P hgp o ho r
  have he := matchStartEnd_edge P hgp o ho r
  have hf : InFan o c d r := sectorEdge_inFan P hgp o ho r
  have hn : ¬InFan o c d v := by
    intro hh
    apply hdiff
    exact Subtype.ext (sectorEdge_unique P hgp o ho v (c,d) he hh).symm
  have hgI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hgII := gp_subset hgI (show inner (inner P) ⊆ inner P from Finset.sdiff_subset)
  have hcd := boundaryEdge_inner_strict (inner (inner P)) hgII o ho c d he
  have huv := boundaryEdge_inner_strict (inner P) hgI o
    (Finset.mem_sdiff.mp ho).1 r v (chainCycle_edge P hgp o ho r)
  have hgen := root_third_second_general P hgp o ho d he.2.1 v
  have hexit := fan_exit_crosses_second_ray o c d r v hcd huv hf hn hgen
  constructor
  · have hh : orient (r : Point) o d = orient o d r := by unfold orient; ring
    rw [hh]; exact hf.2
  · change 0 < orient o v d
    have hh : orient o v d = -orient o d v := by unfold orient; ring
    rw [hh]
    have ht : orient o d v < 0 := hexit.2
    linarith

/-- Distinct neighboring sectors and the already proved size-two fiber geometry
imply global injectivity. No ordinal labeling of either polygon is used. -/
theorem sectorEdge_injective_of_adjacent_distinct
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho) :
    Function.Injective (sectorEdge P hgp o ho) := by
  intro r s hrs
  by_contra hne
  have hg := gp_subset hgp ((hullVertices_subset (inner P)).trans Finset.sdiff_subset)
  rcases same_sector_pair_adjacent P hgp hno o ho r s hne hrs with h | h
  · have hs : chainCycle P hgp o ho r = s := by
      apply Subtype.ext
      exact boundaryEdge_right_unique hg (chainCycle_edge P hgp o ho r) h
    exact hdiff r (by simpa only [hs] using hrs)
  · have hr : chainCycle P hgp o ho s = r := by
      apply Subtype.ext
      exact boundaryEdge_right_unique hg (chainCycle_edge P hgp o ho s) h
    exact hdiff s (by simpa only [hr] using hrs.symm)

lemma sectorEdge_eq_of_sectorVertex_eq
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r s : ChainVertex P)
    (he : sectorVertex P hgp o ho r = sectorVertex P hgp o ho s) :
    sectorEdge P hgp o ho r = sectorEdge P hgp o ho s := by
  have hc : matchStart P hgp o ho r = matchStart P hgp o ho s :=
    congrArg (fun z : ((ChainThird P : Finset Point) : Set Point) => (z : Point)) he
  have hg := gp_subset hgp ((hullVertices_subset (inner (inner P))).trans
    (Finset.sdiff_subset.trans Finset.sdiff_subset))
  have h1 := matchStartEnd_edge P hgp o ho r
  have h2 := matchStartEnd_edge P hgp o ho s
  rw [hc] at h1
  have hd := boundaryEdge_right_unique hg h1 h2
  apply Subtype.ext
  exact Prod.ext hc hd

lemma sectorVertex_injective_of_adjacent_distinct
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho) :
    Function.Injective (sectorVertex P hgp o ho) := by
  intro r s he
  apply sectorEdge_injective_of_adjacent_distinct P hgp hno o ho hdiff
  exact sectorEdge_eq_of_sectorVertex_eq P hgp o ho r s he

/-- Surjectivity of the actual sector map forces exact successor compatibility.
If an inner vertex were skipped, its unique crossed outer edge would be counted
twice. This is the cyclic no-skipping assertion in Case I.C. -/
theorem sector_end_eq_next_start_of_surjective
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho)
    (hsurj : Function.Surjective (sectorVertex P hgp o ho)) :
    ∀ r : ChainVertex P,
      matchEnd P hgp o ho r = matchStart P hgp o ho (chainCycle P hgp o ho r) := by
  intro r
  let f := chainCycle P hgp o ho
  let d := matchEnd P hgp o ho r
  have hd := (matchStartEnd_edge P hgp o ho r).2.1
  obtain ⟨s,hs⟩ := hsurj ⟨d,hd⟩
  have hsval : matchStart P hgp o ho s = d :=
    congrArg (fun z : ((ChainThird P : Finset Point) : Set Point) => (z : Point)) hs
  have hfan1 : InFan o r (f r) d :=
    previous_sector_end_in_swept_edge P hgp o ho r (hdiff r)
  have hfan2 : InFan o (f.symm s) s d := by
    have hh := next_sector_start_in_swept_edge P hgp o ho (f.symm s) (hdiff (f.symm s))
    change InFan o (f.symm s) (f (f.symm s))
      (matchStart P hgp o ho (f (f.symm s))) at hh
    simpa only [Equiv.apply_symm_apply,hsval] using hh
  have he1 := chainCycle_edge P hgp o ho r
  have he2 : BoundaryEdge (ChainSecond P) (f.symm s) s := by
    have hh := chainCycle_edge P hgp o ho (f.symm s)
    change BoundaryEdge (ChainSecond P) (f.symm s) (f (f.symm s)) at hh
    simpa only [Equiv.apply_symm_apply] using hh
  have hg := gp_subset hgp ((hullVertices_subset (inner P)).trans Finset.sdiff_subset)
  obtain ⟨h1,h2⟩ := (inFan_iff_raySides o r (f r) d).mp hfan1
  obtain ⟨h3,h4⟩ := (inFan_iff_raySides o (f.symm s) s d).mp hfan2
  obtain ⟨_,hv⟩ := boundary_fan_unique (ChainSecond P) hg o d
    r (f r) (f.symm s) s he1 he2 h1 h2 h3 h4
  have hvs : f r = s := Subtype.ext hv
  change d = matchStart P hgp o ho (f r)
  rw [hvs]
  exact hsval.symm

lemma third_card_lt_outer
    (P : Finset Point) (hmin : MinimalOuter P)
    (hQne : (ChainThird P).Nonempty) :
    (ChainThird P).card < (hullVertices P).card := by
  have hQP : ChainThird P ⊆ P :=
    (hullVertices_subset (inner (inner P))).trans
      (Finset.sdiff_subset.trans Finset.sdiff_subset)
  apply hmin.smaller (ChainThird P) hQP
  · intro z hz
    rw [convexHull_hullVertices]
    exact subset_convexHull ℝ _ (hQP hz)
  · exact convexIndependent_hullVertices (inner (inner P))
  · intro he
    obtain ⟨z,hz⟩ := hQne
    have hzII := hullVertices_subset (inner (inner P)) hz
    have hzI := (Finset.mem_sdiff.mp hzII).1
    exact (Finset.mem_sdiff.mp hzI).2 (by simpa only [he] using hz)

/-- In a six-hole-free minimal configuration, a singleton-sector case with
at most one extra outer point has equal middle-layer sizes, a bijective sector
map, and exact boundary-successor compatibility. -/
theorem tight_layer_sizes_and_successors
    (P : Finset Point) (hgp : GeneralPosition P)
    (hmin : MinimalOuter P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho)
    (htight : (hullVertices P).card ≤ (ChainSecond P).card + 1) :
    (ChainThird P).card = (ChainSecond P).card ∧
    (hullVertices P).card = (ChainSecond P).card + 1 ∧
    Function.Bijective (sectorVertex P hgp o ho) ∧
    (∀ r : ChainVertex P,
      matchEnd P hgp o ho r = matchStart P hgp o ho (chainCycle P hgp o ho r)) := by
  have hinj := sectorVertex_injective_of_adjacent_distinct P hgp hno o ho hdiff
  have hcount := Fintype.card_le_of_injective (sectorVertex P hgp o ho) hinj
  have hCR : Fintype.card (ChainVertex P) = (ChainSecond P).card := Fintype.card_coe _
  have hCQ : Fintype.card (((ChainThird P : Finset Point) : Set Point)) =
      (ChainThird P).card := Fintype.card_coe _
  rw [hCR,hCQ] at hcount
  have hgpI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hQ3 := three_le_hull_of_inner_nonempty (inner (inner P))
    (gp_subset hgpI Finset.sdiff_subset) ⟨o,ho⟩
  change 3 ≤ (ChainThird P).card at hQ3
  have hlt := third_card_lt_outer P hmin (Finset.card_pos.mp (by omega))
  have hsize : (ChainThird P).card = (ChainSecond P).card := by omega
  have houter : (hullVertices P).card = (ChainSecond P).card + 1 := by omega
  have hsurj : Function.Surjective (sectorVertex P hgp o ho) := by
    let image := (Finset.univ : Finset (ChainVertex P)).image (sectorVertex P hgp o ho)
    have himage : image.card = (ChainSecond P).card := by
      dsimp [image]
      rw [Finset.card_image_of_injective _ hinj]
      exact Finset.card_attach
    have hfull : image = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simpa only [Finset.card_univ,hCQ,hsize,himage] using (le_refl (ChainSecond P).card)
    intro q
    have hq : q ∈ image := by rw [hfull]; exact Finset.mem_univ _
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hq
    exact ⟨r,hr⟩
  exact ⟨hsize,houter,⟨hinj,hsurj⟩,
    sector_end_eq_next_start_of_surjective P hgp o ho hdiff hsurj⟩

/-- At a join which skips its own sector, the outgoing endpoint of the previous
sector and incoming endpoint of the next sector are correctly ordered about
the shared outer vertex. Both radial signs are already proved swept-edge facts. -/
theorem skipped_sector_join_positive
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho) (r : ChainVertex P) :
    0 < orient (chainCycle P hgp o ho r : Point)
      (matchEnd P hgp o ho r)
      (matchStart P hgp o ho (chainCycle P hgp o ho (chainCycle P hgp o ho r))) := by
  let f := chainCycle P hgp o ho
  let d := matchEnd P hgp o ho r
  let a := matchStart P hgp o ho (f (f r))
  have he := previous_sector_end_in_swept_edge P hgp o ho r (hdiff r)
  have hs := next_sector_start_in_swept_edge P hgp o ho (f r) (hdiff (f r))
  have hdo : 0 < orient (f r : Point) d o := by
    have h := he.2
    have hid : orient o (f r) d = orient (f r : Point) d o := by unfold orient; ring
    rwa [hid] at h
  have hoa : 0 < orient (f r : Point) o a := hs.1
  exact orient_pos_trans_from_hull_vertex (inner P) (gp_subset hgp Finset.sdiff_subset)
    (f r) d o a (f r).property
    (Finset.mem_sdiff.mp (matchEnd_mem P hgp o ho r)).1
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ho).1).1
    (Finset.mem_sdiff.mp (matchStart_mem P hgp o ho (f (f r)))).1 hdo hoa

end JSP198.Nicolas

#print axioms JSP198.Nicolas.tight_layer_sizes_and_successors
#print axioms JSP198.Nicolas.skipped_sector_join_positive
