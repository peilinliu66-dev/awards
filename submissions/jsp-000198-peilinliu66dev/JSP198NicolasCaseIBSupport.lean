/-
Released under the MIT license.
Mathematical source: Carlos M. Nicolas, The Empty Hexagon Theorem (2007),
Theorem 4, Case I.B.  The support-vertex choice below makes explicit the
order-preserving join; it does not assume an exterior cover.
Imports the existing project unchanged. Candidate source, not locally compiled here.
-/
import Mathlib
import JSP198NicolasCaseIRuns

set_option maxHeartbeats 1400000
set_option maxRecDepth 2048

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

/-- An inner point in the radial sector of an actual boundary edge is in
its actual triangle with the root. -/
lemma ib_swept_point_in_triangle
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (u v : ChainVertex P) (he : BoundaryEdge (ChainSecond P) u v)
    (z : Point) (hz : z ∈ inner (inner P)) (hf : InFan o u v z) :
    z ∈ convexHull ℝ ({o,(u : Point),(v : Point)} : Set Point) := by
  have hgpI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hO := boundaryEdge_inner_strict (inner P) hgpI o
    (Finset.mem_sdiff.mp ho).1 u v he
  have hZ := boundaryEdge_inner_strict (inner P) hgpI z hz u v he
  have htri : 0 < orient o v u := by
    have hh : orient o v u = -orient o u v := by unfold orient; ring
    rw [hh]; linarith
  have hV : 0 < orient (v : Point) u z := by
    rw [orient_reverse]
    rw [orient_rotate z u v] at hZ
    linarith
  have hh := interior_subset
    (mem_interior_triangle_of_orient_pos o v u z htri hf.2 hV hf.1)
  apply convexHull_mono _ hh
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
  tauto

/-- A vertex of the inner convex polygon cannot be strictly between the root
rays to the endpoints of another supporting edge. -/
lemma ib_third_vertex_not_in_edge_fan
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (c d a : Point) (he : BoundaryEdge (ChainThird P) c d)
    (ha : a ∈ ChainThird P) (hf : InFan o c d a) : False := by
  have hgpI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hgpII := gp_subset hgpI (show inner (inner P) ⊆ inner P from Finset.sdiff_subset)
  have hgpQ := gp_subset hgpII (hullVertices_subset (inner (inner P)))
  have hQ3 : 3 ≤ (ChainThird P).card :=
    three_le_hull_of_inner_nonempty (inner (inner P)) hgpII ⟨o,ho⟩
  have hO := boundaryEdge_inner_strict (inner (inner P)) hgpII o ho c d he
  have hac : a ≠ c := by intro h; subst a; simp [InFan,orient] at hf
  have had : a ≠ d := by intro h; subst a; simp [InFan,orient,mul_comm] at hf
  have hA := he.strict hgpQ ha hac had
  have htri : 0 < orient o d c := by
    have hh : orient o d c = -orient o c d := by unfold orient; ring
    rw [hh]; linarith
  have hdca : 0 < orient d c a := by rw [orient_reverse]; linarith
  have hInside := mem_interior_triangle_of_orient_pos o d c a htri hf.2 hdca hf.1
  have hoQ : o ∈ convexHull ℝ (ChainThird P : Set Point) := by
    rw [convexHull_hullVertices]
    exact subset_convexHull ℝ _ (Finset.mem_sdiff.mp ho).1
  have hHull : convexHull ℝ ({o,d,c} : Set Point) ⊆
      convexHull ℝ (ChainThird P : Set Point) := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hoQ
    · exact subset_convexHull ℝ _ he.2.1
    · exact subset_convexHull ℝ _ he.1
  obtain ⟨b,hab⟩ := exists_boundaryEdge_from (ChainThird P)
    (convexIndependent_hullVertices (inner (inner P))) hgpQ (by omega) a ha
  have hAll : ∀ x ∈ ChainThird P, 0 ≤ orient b a x := by
    intro x hx
    rw [orient_reverse]
    linarith [hab.2.2.2 x hx]
  exact not_mem_interior_convexHull_of_halfplane (ChainThird P) b a a
    hab.2.2.1.symm hAll (by simp [orient,mul_comm]) (interior_mono hHull hInside)

/-- The two endpoints swept between consecutive different sectors occur in
clockwise radial order. This uses supporting lines of the actual third layer. -/
lemma ib_radial_gap_nonpos
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (r : ChainVertex P)
    (hdiff : sectorEdge P hgp o ho r ≠
      sectorEdge P hgp o ho (chainCycle P hgp o ho r)) :
    orient o (matchEnd P hgp o ho r)
      (matchStart P hgp o ho (chainCycle P hgp o ho r)) ≤ 0 := by
  let v := chainCycle P hgp o ho r
  let c := matchStart P hgp o ho r
  let d := matchEnd P hgp o ho r
  let a := matchStart P hgp o ho v
  have he := matchStartEnd_edge P hgp o ho r
  have haQ := (matchStartEnd_edge P hgp o ho v).1
  have hrF : InFan o c d r := sectorEdge_inFan P hgp o ho r
  have haF : InFan o r v a := next_sector_start_in_swept_edge P hgp o ho r hdiff
  have hgpI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hgpII := gp_subset hgpI (show inner (inner P) ⊆ inner P from Finset.sdiff_subset)
  have hcd := boundaryEdge_inner_strict (inner (inner P)) hgpII o ho c d he
  have hcr : orient o c r < 0 := by
    have hh : orient c o r = -orient o c r := by unfold orient; ring
    have hp := hrF.1
    rw [hh] at hp
    linarith
  have hra : orient o (r : Point) a < 0 := by
    have hh : orient (r : Point) o a = -orient o (r : Point) a := by unfold orient; ring
    have hp := haF.1
    rw [hh] at hp
    linarith
  by_contra hn
  have hda : 0 < orient o d a := lt_of_not_ge hn
  have hca : orient o c a < 0 := by
    have hid := radial_plucker o c d r a
    have hp := mul_pos_of_neg_of_neg hcd hra
    have hm := mul_neg_of_neg_of_pos hcr hda
    have hdr : 0 < orient o d r := hrF.2
    by_contra h
    have hnp := mul_nonneg (le_of_not_gt h) hdr.le
    nlinarith
  apply ib_third_vertex_not_in_edge_fan P hgp o ho c d a he haQ
  refine ⟨?_,hda⟩
  have hh : orient c o a = -orient o c a := by unfold orient; ring
  rw [hh]; linarith

/-- Choose the ACTUAL vertex bridging two consecutive sectors. Picking the
next sector's first vertex alone is not valid in general; one of the two
swept endpoints always meets BOTH local joining inequalities. -/
theorem ib_sector_bridge_vertex
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (r : ChainVertex P)
    (hdiff : sectorEdge P hgp o ho r ≠
      sectorEdge P hgp o ho (chainCycle P hgp o ho r)) :
    ∃ z : Point, z ∈ inner (inner P) ∧
      (z = matchEnd P hgp o ho r ∨
       z = matchStart P hgp o ho (chainCycle P hgp o ho r)) ∧
      0 ≤ orient (r : Point) (matchEnd P hgp o ho r) z ∧
      0 ≤ orient (chainCycle P hgp o ho r : Point) z
        (matchStart P hgp o ho (chainCycle P hgp o ho r)) := by
  let v := chainCycle P hgp o ho r
  let d := matchEnd P hgp o ho r
  let a := matchStart P hgp o ho v
  by_cases hda : d = a
  · refine ⟨a,matchStart_mem P hgp o ho v,Or.inr rfl,?_,?_⟩
    · change 0 ≤ orient (r : Point) d a
      rw [hda]; simp [orient,mul_comm]
    · change 0 ≤ orient (v : Point) a a
      simp [orient,mul_comm]
  have hO : orient o d a < 0 := by
    have hnon := ib_radial_gap_nonpos P hgp o ho r hdiff
    have hoII := (Finset.mem_sdiff.mp ho).1
    have hdII := matchEnd_mem P hgp o ho r
    have haII := matchStart_mem P hgp o ho v
    have hod : o ≠ d := by
      intro h
      exact (Finset.mem_sdiff.mp ho).2 (by rw [h]; exact (matchStartEnd_edge P hgp o ho r).2.1)
    have hoa : o ≠ a := by
      intro h
      exact (Finset.mem_sdiff.mp ho).2 (by rw [h]; exact (matchStartEnd_edge P hgp o ho v).1)
    have hne := hgp o (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hoII).1).1
      d (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hdII).1).1
      a (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp haII).1).1 hod hoa hda
    exact lt_of_le_of_ne hnon hne
  by_cases hR : 0 ≤ orient (r : Point) d a
  · refine ⟨a,matchStart_mem P hgp o ho v,Or.inr rfl,hR,?_⟩
    change 0 ≤ orient (v : Point) a a
    simp [orient,mul_comm]
  have hRneg : orient (r : Point) d a < 0 := lt_of_not_ge hR
  have hV : 0 ≤ orient (v : Point) d a := by
    by_contra h
    have hVneg : orient (v : Point) d a < 0 := lt_of_not_ge h
    have hdf := previous_sector_end_in_swept_edge P hgp o ho r hdiff
    have hdT := ib_swept_point_in_triangle P hgp o ho r v
      (chainCycle_edge P hgp o ho r) d (matchEnd_mem P hgp o ho r) hdf
    have hs : convexHull ℝ ({o,(r : Point),(v : Point)} : Set Point) ⊆
        {z : Point | 0 < orient a d z} := by
      apply convexHull_min _ (convex_strict_orient a d)
      intro z hz
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
      rcases hz with hzo | hzr | hzv
      · subst z
        change 0 < orient a d o
        have he : orient a d o = -orient o d a := by unfold orient; ring
        rw [he]; linarith
      · subst z
        change 0 < orient a d (r : Point)
        have he : orient a d (r : Point) = -orient (r : Point) d a := by unfold orient; ring
        rw [he]; linarith
      · subst z
        change 0 < orient a d (v : Point)
        have he : orient a d (v : Point) = -orient (v : Point) d a := by unfold orient; ring
        rw [he]; linarith
    have hh := hs hdT
    simp [orient,mul_comm] at hh
  exact ⟨d,matchEnd_mem P hgp o ho r,Or.inl rfl,by simp [d,orient,mul_comm],hV⟩

/-! ## Exact convex insertion when one edge is visible and its neighbors are not -/

/-- Clockwise dual of the existing supporting-corner halfplane lemma. -/
lemma ib_corner_nonpos
    (Q : Finset Point) (hgp : GeneralPosition Q) (h3 : 3 ≤ Q.card)
    (a b c x : Point) (hab : BoundaryEdge Q a b) (hbc : BoundaryEdge Q b c)
    (hA : orient b x a ≤ 0) (hC : orient b x c ≤ 0) :
    ∀ z ∈ Q, orient b x z ≤ 0 := by
  let y : Point := 2 • b - x
  have he : ∀ z : Point, orient b y z = -orient b x z := by
    intro z
    simp only [y,orient,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring
  have hh := hull_in_corner_halfplane Q hgp h3 a b c y hab hbc
    (by rw [he]; linarith) (by rw [he]; linarith)
  intro z hz
  have ht := hh (subset_convexHull ℝ _ hz)
  change 0 ≤ orient b y z at ht
  rw [he] at ht
  linarith

/-- If an exterior point sees an edge but not its two neighbors, inserting it
preserves EVERY old hull vertex. The proof derives the absence of all other
visible edges; it is not a hypothesis about visibility being consecutive. -/
theorem ib_insert_single_visible_edge_convex
    (S Q : Finset Point) (hgpS : GeneralPosition S) (hQS : Q ⊆ S)
    (hconv : InConvexPosition Q) (h3 : 3 ≤ Q.card)
    (x a u v b : Point) (hx : x ∈ S) (hxQ : x ∉ Q)
    (hau : BoundaryEdge Q a u) (huv : BoundaryEdge Q u v)
    (hvb : BoundaryEdge Q v b)
    (hface : 0 < orient u v x)
    (hprev : orient a u x < 0) (hnext : orient v b x < 0) :
    InConvexPosition (insert x Q) := by
  have hgQ := gp_subset hgpS hQS
  have hxu : x ≠ u := by
    intro h
    apply hxQ
    simpa only [h] using huv.1
  have hxv : x ≠ v := by
    intro h
    apply hxQ
    simpa only [h] using huv.2.1
  have hlow : ∀ z ∈ Q, 0 ≤ orient x u z := by
    have hA : orient u x a ≤ 0 := by rw [orient_rotate a u x] at hprev; exact hprev.le
    have hV : orient u x v ≤ 0 := by
      have he : orient u x v = -orient u v x := by unfold orient; ring
      rw [he]; linarith
    intro z hz
    have hh := ib_corner_nonpos Q hgQ h3 a u v x hau huv hA hV z hz
    rw [orient_reverse]
    linarith
  have hhigh : ∀ z ∈ Q, 0 ≤ orient x z v := by
    have hU : 0 ≤ orient v x u := by rw [← orient_rotate u v x]; exact hface.le
    have hB : 0 ≤ orient v x b := by
      have he : orient v x b = -orient v b x := by unfold orient; ring
      rw [he]; linarith
    have hh := hull_in_corner_halfplane Q hgQ h3 u v b x huv hvb hU hB
    intro z hz
    have ht := hh (subset_convexHull ℝ _ hz)
    change 0 ≤ orient v x z at ht
    rw [orient_rotate v x z] at ht
    exact ht
  have strictLow : ∀ z ∈ Q, z ≠ u → 0 < orient x u z := by
    intro z hz hzu
    have hxz : x ≠ z := by
      intro h
      apply hxQ
      simpa only [h] using hz
    exact lt_of_le_of_ne (hlow z hz) (hgpS x hx u (hQS huv.1) z (hQS hz)
      hxu hxz hzu.symm).symm
  have strictHigh : ∀ z ∈ Q, z ≠ v → 0 < orient x z v := by
    intro z hz hzv
    have hxz : x ≠ z := by
      intro h
      apply hxQ
      simpa only [h] using hz
    exact lt_of_le_of_ne (hhigh z hz) (hgpS x hx z (hQS hz) v (hQS huv.2.1)
      hxz hxv hzv).symm
  have otherNonpos : ∀ c d : Point, BoundaryEdge Q c d → c ≠ u →
      orient c d x ≤ 0 := by
    intro c d hcd hcu
    by_contra hn
    have hpos : 0 < orient c d x := lt_of_not_ge hn
    by_cases hcv : c = v
    · subst c
      have hdv : d ≠ v := hcd.2.2.1.symm
      have hdu : d ≠ u := (boundary_neighbors_ne Q hgQ h3 u v d huv hcd).symm
      exact visible_endpoint_not_between Q hgQ x u v v d d huv hcd hface hpos
        (Or.inr rfl) (strictLow d hcd.2.1 hdu) (strictHigh d hcd.2.1 hdv)
    · exact visible_endpoint_not_between Q hgQ x u v c d c huv hcd hface hpos
        (Or.inl rfl) (strictLow c hcd.1 hcu) (strictHigh c hcd.1 hcv)
  apply convex_position_of_supported
  intro q hq
  rcases Finset.mem_insert.mp hq with hqx | hqQ
  · subst q
    refine ⟨u,Finset.mem_insert_of_mem huv.1,x,Finset.mem_insert_self _ _,
      hxu.symm,Or.inr rfl,?_⟩
    intro z hz hzu hzx
    have hzQ : z ∈ Q := (Finset.mem_insert.mp hz).resolve_left hzx
    have hh := strictLow z hzQ hzu
    rw [orient_reverse]
    linarith
  · by_cases hqu : q = u
    · subst q
      refine ⟨a,Finset.mem_insert_of_mem hau.1,u,Finset.mem_insert_of_mem hau.2.1,
        hau.2.2.1,Or.inr rfl,?_⟩
      intro z hz hza hzu
      rcases Finset.mem_insert.mp hz with hzx | hzQ
      · subst z
        exact hprev
      · exact hau.strict hgQ hzQ hza hzu
    · obtain ⟨d,hqd⟩ := exists_boundaryEdge_from Q hconv hgQ (by omega) q hqQ
      refine ⟨q,Finset.mem_insert_of_mem hqQ,d,Finset.mem_insert_of_mem hqd.2.1,
        hqd.2.2.1,Or.inl rfl,?_⟩
      intro z hz hzq hzd
      rcases Finset.mem_insert.mp hz with hzx | hzQ
      · subst z
        have hxq : x ≠ q := by
          intro h
          apply hxQ
          simpa only [h] using hqQ
        have hxd : x ≠ d := by
          intro h
          apply hxQ
          simpa only [h] using hqd.2.1
        exact lt_of_le_of_ne (otherNonpos q d hqd hqu)
          (hgpS q (hQS hqQ) d (hQS hqd.2.1) x hx hqd.2.2.1 hxq.symm hxd.symm)
      · exact hqd.strict hgQ hzQ hzq hzd

end JSP198.Nicolas

#print axioms JSP198.Nicolas.ib_sector_bridge_vertex
#print axioms JSP198.Nicolas.ib_insert_single_visible_edge_convex
