/-
Copyright (c) 2026 JSP198 formalization contributors.
Released under the MIT license.

Mathematical source: C. M. Nicolas, The Empty Hexagon Theorem (2007),
Case II. This module proves the endpoint-fan variant of the bridge step.
It does NOT assert that the endpoint triangle itself is empty: the already
proved outerFan_card_le_two performs the necessary triangle shrinking.

Imported MIT geometric infrastructure: CollinYuanjieRen/awards,
b8bb4f7803f921a7970abc880291ad9372111360,
submissions/jsp-000198-smallk-cyr/EmptyPentagon/{Hull,Certificate}.lean,
via the user's unchanged JSP198Nicolas*.lean modules.

Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Candidate: not compiled in the generating environment.
-/
import Mathlib
import JSP198NicolasSweptOrder
import JSP198NicolasOnePointGlue

noncomputable section
open Classical Horton
namespace JSP198.Nicolas.CaseII

/-- A third-layer vertex cannot lie strictly between the rays from an interior
root to the endpoints of one of its own supporting edges. -/
lemma third_vertex_not_in_root_fan
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (c d z : Point) (hcd : BoundaryEdge (ChainThird P) c d)
    (hz : z ∈ ChainThird P) : ¬ InFan o c d z := by
  intro hfan
  have hgII := gp_subset hgp
    (show inner (inner P) ⊆ P from Finset.sdiff_subset.trans Finset.sdiff_subset)
  have hc := hullVertices_subset (inner (inner P)) hcd.1
  have hd := hullVertices_subset (inner (inner P)) hcd.2.1
  have hoII := (Finset.mem_sdiff.mp ho).1
  have hco : 0 < orient z c o := by
    have he : orient z c o = orient c o z := by unfold orient; ring
    rw [he]
    exact hfan.1
  have hod : 0 < orient z o d := by
    have he : orient z o d = orient o d z := by unfold orient; ring
    rw [he]
    exact hfan.2
  have hpos := orient_pos_trans_from_hull_vertex (inner (inner P)) hgII
    z c o d hz hc hoII hd hco hod
  have hnonpos := hcd.2.2.2 z hz
  have he : orient z c d = orient c d z := by unfold orient; ring
  rw [he] at hpos
  linarith

/-- The ending vertex of the old sector occurs no later radially than the
starting vertex of the new sector. Equality is the adjacent-inner-edge case. -/
lemma old_end_new_start_radial_order
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P)
    (hdiff : sectorEdge P hgp o ho r ≠
      sectorEdge P hgp o ho (chainCycle P hgp o ho r)) :
    matchEnd P hgp o ho r =
        matchStart P hgp o ho (chainCycle P hgp o ho r) ∨
      orient o (matchEnd P hgp o ho r)
        (matchStart P hgp o ho (chainCycle P hgp o ho r)) < 0 := by
  let v := chainCycle P hgp o ho r
  let c := matchStart P hgp o ho r
  let d := matchEnd P hgp o ho r
  let a := matchStart P hgp o ho v
  by_cases hda : d = a
  · exact Or.inl hda
  right
  have hcd := matchStartEnd_edge P hgp o ho r
  have hab := matchStartEnd_edge P hgp o ho v
  have hf := next_sector_start_in_swept_edge P hgp o ho r hdiff
  have hra : orient o (r : Point) a < 0 := by
    have hh : 0 < orient (r : Point) o a := hf.1
    have he : orient o (r : Point) a = -orient (r : Point) o a := by
      unfold orient; ring
    rw [he]
    linarith
  have hgII := gp_subset hgp
    (show inner (inner P) ⊆ P from Finset.sdiff_subset.trans Finset.sdiff_subset)
  have hcdO := boundaryEdge_inner_strict (inner (inner P)) hgII o ho c d hcd
  have hnofan := third_vertex_not_in_root_fan P hgp o ho c d a hcd hab.1
  have hod : o ≠ d := by
    intro he
    exact (Finset.mem_sdiff.mp ho).2 (by rw [he]; exact hcd.2.1)
  have hoa : o ≠ a := by
    intro he
    exact (Finset.mem_sdiff.mp ho).2 (by rw [he]; exact hab.1)
  have hgen := hgII o (Finset.mem_sdiff.mp ho).1
    d (hullVertices_subset (inner (inner P)) hcd.2.1)
    a (hullVertices_subset (inner (inner P)) hab.1) hod hoa hda
  have hh := fan_exit_crosses_second_ray o c d r a hcdO hra
    (sectorEdge_inFan P hgp o ho r) hnofan hgen
  exact hh.2

/-- Elementary two-endpoint bridge alternative. All inputs are determinant
facts, and the proof uses the actual triangle (o,v,u). -/
lemma endpoint_bridge_alternative
    (o u v d a : Point)
    (huv : orient o u v < 0)
    (hd : InFan o u v d)
    (hinside : orient u v d < 0)
    (horder : orient o d a < 0) :
    0 ≤ orient u d a ∨ 0 ≤ orient v d a := by
  by_contra hn
  push_neg at hn
  have hotri : 0 < orient o v u := by
    have he : orient o v u = -orient o u v := by unfold orient; ring
    rw [he]
    linarith
  have hvud : 0 < orient v u d := by
    rw [orient_reverse]
    linarith
  have htri : d ∈ convexHull ℝ ({o,v,u} : Set Point) :=
    interior_subset (mem_interior_triangle_of_orient_pos o v u d
      hotri hd.2 hvud hd.1)
  have hoH : 0 < orient a d o := by
    have he : orient a d o = -orient o d a := by unfold orient; ring
    rw [he]
    linarith
  have huH : 0 < orient a d u := by
    have he : orient a d u = -orient u d a := by unfold orient; ring
    rw [he]
    linarith
  have hvH : 0 < orient a d v := by
    have he : orient a d v = -orient v d a := by unfold orient; ring
    rw [he]
    linarith
  have hsub : ({o,v,u} : Set Point) ⊆ {z : Point | 0 < orient a d z} := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hoH
    · exact hvH
    · exact huH
  have hbad := (convexHull_min hsub (convex_strict_orient a d)) htri
  change 0 < orient a d d at hbad
  rw [orient_refl_right] at hbad
  linarith

/-- An explicit actual third-layer vertex for every change of radial sector.
It is one of the two endpoints, not a point introduced by geometric completion. -/
def bridgeVertex
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P) : Point :=
  if 0 ≤ orient (chainCycle P hgp o ho r : Point)
      (matchEnd P hgp o ho r)
      (matchStart P hgp o ho (chainCycle P hgp o ho r))
  then matchEnd P hgp o ho r
  else matchStart P hgp o ho (chainCycle P hgp o ho r)

lemma bridgeVertex_mem_third
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P) :
    bridgeVertex P hgp o ho r ∈ ChainThird P := by
  unfold bridgeVertex
  split_ifs
  · exact (matchStartEnd_edge P hgp o ho r).2.1
  · exact (matchStartEnd_edge P hgp o ho (chainCycle P hgp o ho r)).1

/-- BOTH joining inequalities, from raw nested-layer geometry. No matching,
bridge existence, angular order, or covering assumption is used. -/
theorem bridgeVertex_join
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P)
    (hdiff : sectorEdge P hgp o ho r ≠
      sectorEdge P hgp o ho (chainCycle P hgp o ho r)) :
    0 ≤ orient (r : Point) (matchEnd P hgp o ho r) (bridgeVertex P hgp o ho r) ∧
    0 ≤ orient (chainCycle P hgp o ho r : Point) (bridgeVertex P hgp o ho r)
      (matchStart P hgp o ho (chainCycle P hgp o ho r)) := by
  let v := chainCycle P hgp o ho r
  let d := matchEnd P hgp o ho r
  let a := matchStart P hgp o ho v
  have halt : 0 ≤ orient (r : Point) d a ∨ 0 ≤ orient (v : Point) d a := by
    rcases old_end_new_start_radial_order P hgp o ho r hdiff with he | he
    · change d = a at he
      right
      rw [he]
      unfold orient
      nlinarith
    · have hgI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
      have hed := chainCycle_edge P hgp o ho r
      have hoR := boundaryEdge_inner_strict (inner P) hgI o
        (Finset.mem_sdiff.mp ho).1 r v hed
      have hdR := boundaryEdge_inner_strict (inner P) hgI d
        (matchEnd_mem P hgp o ho r) r v hed
      have hdinside : orient (r : Point) (v : Point) d < 0 := by
        rwa [orient_rotate d r v] at hdR
      exact endpoint_bridge_alternative o r v d a hoR
        (previous_sector_end_in_swept_edge P hgp o ho r hdiff) hdinside he
  unfold bridgeVertex
  change (0 ≤ orient (r : Point) d (if 0 ≤ orient (v : Point) d a then d else a)) ∧
    (0 ≤ orient (v : Point) (if 0 ≤ orient (v : Point) d a then d else a) a)
  by_cases hv : 0 ≤ orient (v : Point) d a
  · simp only [if_pos hv]
    exact ⟨by unfold orient; nlinarith, hv⟩
  · simp only [if_neg hv]
    exact ⟨halt.resolve_right hv, by unfold orient; nlinarith⟩

/-- Capacity two is valid even when the unshrunk bridge triangle is not empty.
This is precisely why an endpoint bridge suffices for the complete proof. -/
theorem bridge_fan_card_le_two
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬ HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P) :
    (outerFan P (bridgeVertex P hgp o ho r)
      (r, chainCycle P hgp o ho r)).card ≤ 2 := by
  have hzII := chain_third_mem_inner2 (bridgeVertex_mem_third P hgp o ho r)
  exact outerFan_card_le_two P hgp hno (bridgeVertex P hgp o ho r)
    (Finset.mem_sdiff.mp hzII).1 (r, chainCycle P hgp o ho r)
    (chainCycle_edge P hgp o ho r)
    (chain_inner2_ne_second hzII r)
    (chain_inner2_ne_second hzII (chainCycle P hgp o ho r))

/-- The distinguished matching inside a double sector has ZERO outer capacity,
by the user's already proved one-outer-point gluing theorem. -/
theorem double_sector_channel_eq_empty
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬ HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P)
    (heq : sectorEdge P hgp o ho r =
      sectorEdge P hgp o ho (chainCycle P hgp o ho r)) :
    matchChannel P r (chainCycle P hgp o ho r)
      (matchStart P hgp o ho r) (matchEnd P hgp o ho r) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hcd := matchStartEnd_edge P hgp o ho r
  have hgII := gp_subset hgp
    (show inner (inner P) ⊆ P from Finset.sdiff_subset.trans Finset.sdiff_subset)
  have hneg := boundaryEdge_inner_strict (inner (inner P)) hgII o ho
    (matchStart P hgp o ho r) (matchEnd P hgp o ho r) hcd
  have hneg' : orient (matchStart P hgp o ho r) (matchEnd P hgp o ho r) o < 0 := by
    rwa [orient_rotate o (matchStart P hgp o ho r) (matchEnd P hgp o ho r)] at hneg
  have hfnext : InFan o (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
      (chainCycle P hgp o ho r) := by
    have hh := sectorEdge_inFan P hgp o ho (chainCycle P hgp o ho r)
    rw [← heq] at hh
    exact hh
  apply hno
  exact hasEmptySix_of_one_point_double_sector P hgp
    r (chainCycle P hgp o ho r)
    (matchStart P hgp o ho r) (matchEnd P hgp o ho r) o x
    (chainCycle_edge P hgp o ho r) hcd (Finset.mem_sdiff.mp ho).1 hneg'
    (sectorEdge_inFan P hgp o ho r) hfnext
    (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2

end JSP198.Nicolas.CaseII

#print axioms JSP198.Nicolas.CaseII.bridgeVertex_join
#print axioms JSP198.Nicolas.CaseII.bridge_fan_card_le_two
#print axioms JSP198.Nicolas.CaseII.double_sector_channel_eq_empty
