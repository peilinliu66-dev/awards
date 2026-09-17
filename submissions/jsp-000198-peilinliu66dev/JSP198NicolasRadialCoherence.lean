/-
Released under the MIT license.
Mathematics: C. M. Nicolas (2007); finite determinant/ray-cut implementation.
Actual sector matchings are proved locally coherent and hence globally cover.
This module does not assume an annular covering or a cyclic monotonicity axiom.
-/
import Mathlib
import JSP198NicolasCoherentCover

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

/-! Two visible supporting edges cannot project over one another.
The proof uses an actual point on their segment, not a planar picture. -/

lemma visible_endpoint_not_between
    (Q : Finset Point) (hgp : GeneralPosition Q)
    (v a b c d z : Point)
    (hab : BoundaryEdge Q a b) (hcd : BoundaryEdge Q c d)
    (hfaceAB : 0 < orient a b v) (hfaceCD : 0 < orient c d v)
    (hz : z = c ∨ z = d)
    (haz : 0 < orient v a z) (hzb : 0 < orient v z b) : False := by
  have hzQ : z ∈ Q := by
    rcases hz with rfl | rfl
    · exact hcd.1
    · exact hcd.2.1
  have hza : z ≠ a := by rintro rfl; unfold orient at haz; nlinarith
  have hzb' : z ≠ b := by rintro rfl; unfold orient at hzb; nlinarith
  have hstrict := hab.strict hgp hzQ hza hzb'
  have hB : 0 < raySide v z b := hzb
  have hA : raySide v z a < 0 := by
    change orient v z a < 0
    have he : orient v z a = -orient v a z := by unfold orient; ring
    rw [he]; linarith
  let D := rayDen v z b a
  let t := rayCut v z b a
  have hD : 0 < D := rayDen_pos hB hA
  have htD : t * D = orient a b v := by
    have hh := rayCut_eq_mul v z b a (ne_of_gt hD)
    have he : -orient v b a = orient a b v := by unfold orient; ring
    rw [he] at hh
    exact hh
  have hval : orient a b z = orient a b v - D := by
    dsimp [D,rayDen,raySide]
    unfold orient
    ring
  have htlt : t < 1 := by nlinarith
  have hzH : v + t • (z-v) ∈ convexHull ℝ (Q : Set Point) :=
    rayCut_mem_hull hab.2.1 hab.1 hB hA
  have hh := orient_nonpos_on_hull hcd.2.2.2 hzH
  have hzero : orient c d z = 0 := by
    rcases hz with rfl | rfl <;> unfold orient <;> ring
  have he : orient c d (v + t • (z-v)) =
      (1-t) * orient c d v + t * orient c d z := by
    simp only [orient,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
      Prod.fst_sub,Prod.snd_sub,smul_eq_mul]
    ring
  rw [he,hzero,mul_zero,add_zero] at hh
  have hp := mul_pos (sub_pos.mpr htlt) hfaceCD
  linarith

lemma visible_gap_right
    (S Q : Finset Point) (hgp : GeneralPosition S) (hQS : Q ⊆ S)
    (v o c d a b : Point) (hv : v ∈ hullVertices S) (ho : o ∈ S)
    (hcd : BoundaryEdge Q c d) (hab : BoundaryEdge Q a b)
    (hfaceCD : 0 < orient c d v) (hfaceAB : 0 < orient a b v)
    (hdo : 0 < orient v d o) (hob : 0 < orient v o b) :
    0 ≤ orient v d a := by
  have hdb := orient_pos_trans_from_hull_vertex S hgp v d o b hv
    (hQS hcd.2.1) ho (hQS hab.2.1) hdo hob
  by_contra hn
  have hneg : orient v d a < 0 := lt_of_not_ge hn
  have had : 0 < orient v a d := by
    have he : orient v a d = -orient v d a := by unfold orient; ring
    rw [he]; linarith
  exact visible_endpoint_not_between Q (gp_subset hgp hQS) v a b c d d
    hab hcd hfaceAB hfaceCD (Or.inr rfl) had hdb

lemma visible_gap_left
    (S Q : Finset Point) (hgp : GeneralPosition S) (hQS : Q ⊆ S)
    (v o c d a b : Point) (hv : v ∈ hullVertices S) (ho : o ∈ S)
    (hcd : BoundaryEdge Q c d) (hab : BoundaryEdge Q a b)
    (hfaceCD : 0 < orient c d v) (hfaceAB : 0 < orient a b v)
    (hco : 0 < orient v c o) (hoa : 0 < orient v o a) :
    0 ≤ orient v d a := by
  have hca := orient_pos_trans_from_hull_vertex S hgp v c o a hv
    (hQS hcd.1) ho (hQS hab.1) hco hoa
  by_contra hn
  have hneg : orient v d a < 0 := lt_of_not_ge hn
  have had : 0 < orient v a d := by
    have he : orient v a d = -orient v d a := by unfold orient; ring
    rw [he]; linarith
  exact visible_endpoint_not_between Q (gp_subset hgp hQS) v c d a b a
    hcd hab hfaceCD hfaceAB (Or.inl rfl) hca had

/-- Dual of the already proved exit lemma: an actual clockwise boundary edge
can enter a sector only through its first boundary ray. -/
lemma fan_entry_crosses_first_ray
    (o a b u v : Point)
    (hab : orient o a b < 0) (huv : orient o u v < 0)
    (hu : ¬InFan o a b u) (hv : InFan o a b v)
    (hgen : orient o a u ≠ 0) : 0 < orient o a u := by
  by_contra hn
  have hau : orient o a u < 0 := lt_of_le_of_ne (le_of_not_gt hn) hgen
  have hbu : orient o b u ≤ 0 := by
    by_contra hh
    have hpos : 0 < orient o b u := lt_of_not_ge hh
    apply hu
    refine ⟨?_,hpos⟩
    have he : orient a o u = -orient o a u := by unfold orient; ring
    rw [he]; linarith
  have hav : orient o a v < 0 := by
    have he : orient a o v = -orient o a v := by unfold orient; ring
    have h := hv.1
    rw [he] at h
    linarith
  have hbv := hv.2
  have hid := radial_plucker o a b u v
  have hL := mul_pos_of_neg_of_neg hab huv
  have hR1 := mul_neg_of_neg_of_pos hau hbv
  have hR2 := mul_nonneg_of_nonpos_of_nonpos hav.le hbu
  nlinarith

noncomputable def matchStart
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P) : Point :=
  (sectorEdge P hgp o ho r).val.1

noncomputable def matchEnd
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P) : Point :=
  (sectorEdge P hgp o ho r).val.2

lemma matchStartEnd_edge
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P) :
    BoundaryEdge (ChainThird P) (matchStart P hgp o ho r) (matchEnd P hgp o ho r) :=
  mem_boundaryEdges.mp (sectorEdge P hgp o ho r).property

lemma matchStart_mem
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P) :
    matchStart P hgp o ho r ∈ inner (inner P) :=
  hullVertices_subset _ (matchStartEnd_edge P hgp o ho r).1

lemma matchEnd_mem
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P) :
    matchEnd P hgp o ho r ∈ inner (inner P) :=
  hullVertices_subset _ (matchStartEnd_edge P hgp o ho r).2.1

lemma root_third_second_general
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (z : Point) (hz : z ∈ ChainThird P) (r : ChainVertex P) :
    orient o z r ≠ 0 := by
  have hoII := (Finset.mem_sdiff.mp ho).1
  have hoI := (Finset.mem_sdiff.mp hoII).1
  have hzII := hullVertices_subset (inner (inner P)) hz
  have hzI := (Finset.mem_sdiff.mp hzII).1
  have hoz : o ≠ z := by
    intro he
    exact (Finset.mem_sdiff.mp ho).2 (by simpa only [he] using hz)
  have hor : o ≠ (r : Point) := chain_inner2_ne_second hoII r
  have hzr : z ≠ (r : Point) := chain_inner2_ne_second hzII r
  exact hgp o (Finset.mem_sdiff.mp hoI).1 z (Finset.mem_sdiff.mp hzI).1
    r (Finset.mem_sdiff.mp (chain_second_mem_inner r)).1 hoz hor hzr

/-- Actual right/left availability, expressed only by a determinant at the
neighbor of a real supporting edge. Annularity/emptiness follow from old lemmas. -/
def CanMatchRight
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P) : Prop :=
  0 < orient (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
    (chainCycle P hgp o ho r : Point)

def CanMatchLeft
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P) : Prop :=
  0 < orient (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
    ((chainCycle P hgp o ho).symm r : Point)

lemma actual_match_left_or_right
    (P : Finset Point) (hgp : GeneralPosition P)
    (hmin : MinimalOuter P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P) :
    CanMatchLeft P hgp o ho r ∨ CanMatchRight P hgp o ho r := by
  obtain ⟨u,w,hur,hrw,hh⟩ := actual_sector_match_exists P hgp hmin hno o ho r
  have hg := gp_subset hgp ((hullVertices_subset (inner P)).trans Finset.sdiff_subset)
  have heR := chainCycle_edge P hgp o ho r
  have heL : BoundaryEdge (ChainSecond P) ((chainCycle P hgp o ho).symm r) r := by
    have h := chainCycle_edge P hgp o ho ((chainCycle P hgp o ho).symm r)
    simpa only [Equiv.apply_symm_apply] using h
  have hu := boundaryEdge_left_unique hg hur heL
  have hw := boundaryEdge_right_unique hg hrw heR
  rcases hh with h | h
  · left
    change 0 < orient (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
      ((chainCycle P hgp o ho).symm r : Point)
    simpa only [matchStart,matchEnd,hu] using h.1
  · right
    change 0 < orient (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
      (chainCycle P hgp o ho r : Point)
    simpa only [matchStart,matchEnd,hw] using h.1

/-- Coherence at a join of two right-assigned cells. The radial-order fact is
DERIVED using the proved unique-exit determinant lemma. -/
theorem right_radial_join_coherent
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P)
    (hdiff : sectorEdge P hgp o ho r ≠
      sectorEdge P hgp o ho (chainCycle P hgp o ho r))
    (hright : CanMatchRight P hgp o ho r) :
    0 ≤ orient (chainCycle P hgp o ho r : Point)
      (matchEnd P hgp o ho r)
      (matchStart P hgp o ho (chainCycle P hgp o ho r)) := by
  let v := chainCycle P hgp o ho r
  let c := matchStart P hgp o ho r
  let d := matchEnd P hgp o ho r
  let a := matchStart P hgp o ho v
  let b := matchEnd P hgp o ho v
  have hcd := matchStartEnd_edge P hgp o ho r
  have hab := matchStartEnd_edge P hgp o ho v
  have hfanU : InFan o c d r := sectorEdge_inFan P hgp o ho r
  have hfanV : InFan o a b v := sectorEdge_inFan P hgp o ho v
  have hnfan : ¬InFan o c d v := by
    intro hh
    have he := sectorEdge_unique P hgp o ho v (c,d) hcd hh
    apply hdiff
    apply Subtype.ext
    exact he.symm
  have hgpI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hgpII := gp_subset hgpI (show inner (inner P) ⊆ inner P from Finset.sdiff_subset)
  have hcdO := boundaryEdge_inner_strict (inner (inner P)) hgpII o ho c d hcd
  have huvO := boundaryEdge_inner_strict (inner P) hgpI o
    (Finset.mem_sdiff.mp ho).1 r v (chainCycle_edge P hgp o ho r)
  have hgen := root_third_second_general P hgp o ho d hcd.2.1 v
  have hexit := fan_exit_crosses_second_ray o c d r v hcdO huvO hfanU hnfan hgen
  have hdo : 0 < orient (v : Point) d o := by
    have he : orient (v : Point) d o = -orient o d v := by unfold orient; ring
    rw [he]
    have hh : orient o d v < 0 := hexit.2
    linarith
  have hob : 0 < orient (v : Point) o b := by
    have he : orient (v : Point) o b = orient o b v := by unfold orient; ring
    rw [he]; exact hfanV.2
  exact visible_gap_right (inner P) (ChainThird P) hgpI
    ((hullVertices_subset (inner (inner P))).trans Finset.sdiff_subset)
    v o c d a b v.property (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ho).1).1
    hcd hab hright (sectorEdge_outward P hgp o ho v) hdo hob

/-- Coherence at a join of two left-assigned cells. -/
theorem left_radial_join_coherent
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P)
    (hdiff : sectorEdge P hgp o ho r ≠
      sectorEdge P hgp o ho (chainCycle P hgp o ho r))
    (hleft : CanMatchLeft P hgp o ho (chainCycle P hgp o ho r)) :
    0 ≤ orient (r : Point) (matchEnd P hgp o ho r)
      (matchStart P hgp o ho (chainCycle P hgp o ho r)) := by
  let v := chainCycle P hgp o ho r
  let c := matchStart P hgp o ho r
  let d := matchEnd P hgp o ho r
  let a := matchStart P hgp o ho v
  let b := matchEnd P hgp o ho v
  have hcd := matchStartEnd_edge P hgp o ho r
  have hab := matchStartEnd_edge P hgp o ho v
  have hfanU : InFan o c d r := sectorEdge_inFan P hgp o ho r
  have hfanV : InFan o a b v := sectorEdge_inFan P hgp o ho v
  have hnfan : ¬InFan o a b r := by
    intro hh
    have he := sectorEdge_unique P hgp o ho r (a,b) hab hh
    apply hdiff
    exact Subtype.ext he
  have hgpI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hgpII := gp_subset hgpI (show inner (inner P) ⊆ inner P from Finset.sdiff_subset)
  have habO := boundaryEdge_inner_strict (inner (inner P)) hgpII o ho a b hab
  have huvO := boundaryEdge_inner_strict (inner P) hgpI o
    (Finset.mem_sdiff.mp ho).1 r v (chainCycle_edge P hgp o ho r)
  have hgen := root_third_second_general P hgp o ho a hab.1 r
  have hentry := fan_entry_crosses_first_ray o a b r v habO huvO hnfan hfanV hgen
  have hco : 0 < orient (r : Point) c o := by
    have he : orient (r : Point) c o = orient c o r := by unfold orient; ring
    rw [he]; exact hfanU.1
  have hoa : 0 < orient (r : Point) o a := by
    have he : orient (r : Point) o a = orient o a r := by unfold orient; ring
    rw [he]; exact hentry
  have hfaceAB : 0 < orient a b r := by
    have hh := hleft
    change 0 < orient a b ((chainCycle P hgp o ho).symm v : Point) at hh
    simpa only [v,Equiv.symm_apply_apply] using hh
  exact visible_gap_left (inner P) (ChainThird P) hgpI
    ((hullVertices_subset (inner (inner P))).trans Finset.sdiff_subset)
    r o c d a b r.property (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ho).1).1
    hcd hab (sectorEdge_outward P hgp o ho r) hfaceAB hco hoa

/-- No adjacent equal sectors is enough here; no global order/injectivity is
assumed to prove these covers. -/
def AdjacentSectorsDistinct
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) : Prop :=
  ∀ r : ChainVertex P, sectorEdge P hgp o ho r ≠
    sectorEdge P hgp o ho (chainCycle P hgp o ho r)

/-- Nicolas's all-right covering, from actual sector choices. -/
theorem right_matching_cover
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho)
    (hright : ∀ r, CanMatchRight P hgp o ho r) :
    ∀ x ∈ hullVertices P, ∃ r : ChainVertex P,
      x ∈ matchChannel P r (chainCycle P hgp o ho r)
        (matchStart P hgp o ho r) (matchEnd P hgp o ho r) := by
  have hc := matchStart_mem P hgp o ho
  have hd := matchEnd_mem P hgp o ho
  have hshape : ∀ r : ChainVertex P,
      matchStart P hgp o ho r = matchEnd P hgp o ho r ∨
      (0 < orient (r : Point) (matchStart P hgp o ho r) (matchEnd P hgp o ho r) ∧
       0 < orient (r : Point) (matchStart P hgp o ho r) (chainCycle P hgp o ho r : Point) ∧
       0 < orient (r : Point) (matchEnd P hgp o ho r) (chainCycle P hgp o ho r : Point) ∧
       0 < orient (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
         (chainCycle P hgp o ho r : Point)) := by
    intro r
    exact Or.inr (boundary_match_four_signs P hgp r (chainCycle P hgp o ho r)
      (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
      (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho r)
      (sectorEdge_outward P hgp o ho r) (hright r))
  intro x hx
  obtain ⟨r,hr⟩ := coherent_strips_cover P hgp o ho
    (matchStart P hgp o ho) (matchEnd P hgp o ho) hc hd hshape
    (fun r => right_radial_join_coherent P hgp o ho r (hdiff r) (hright r)) x hx
  refine ⟨r,?_⟩
  rw [stripCell_eq_matchChannel _ _ _ _ _ (matchStartEnd_edge P hgp o ho r).2.2.1] at hr
  exact hr

/-- Nicolas's all-left covering, indexed by the actual OUTER EDGE start. -/
theorem left_matching_cover
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho)
    (hleft : ∀ r, CanMatchLeft P hgp o ho r) :
    ∀ x ∈ hullVertices P, ∃ r : ChainVertex P,
      x ∈ matchChannel P r (chainCycle P hgp o ho r)
        (matchStart P hgp o ho (chainCycle P hgp o ho r))
        (matchEnd P hgp o ho (chainCycle P hgp o ho r)) := by
  let f := chainCycle P hgp o ho
  let c := fun r : ChainVertex P => matchStart P hgp o ho (f r)
  let d := fun r : ChainVertex P => matchEnd P hgp o ho (f r)
  have hc : ∀ r, c r ∈ inner (inner P) := fun r => matchStart_mem P hgp o ho (f r)
  have hd : ∀ r, d r ∈ inner (inner P) := fun r => matchEnd_mem P hgp o ho (f r)
  have hface : ∀ r, 0 < orient (c r) (d r) (r : Point) := by
    intro r
    have hh := hleft (f r)
    change 0 < orient (c r) (d r) (f.symm (f r) : Point) at hh
    simpa only [Equiv.symm_apply_apply] using hh
  have hshape : ∀ r : ChainVertex P, c r = d r ∨
      (0 < orient (r : Point) (c r) (d r) ∧
       0 < orient (r : Point) (c r) (f r : Point) ∧
       0 < orient (r : Point) (d r) (f r : Point) ∧
       0 < orient (c r) (d r) (f r : Point)) := by
    intro r
    exact Or.inr (boundary_match_four_signs P hgp r (f r) (c r) (d r)
      (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho (f r))
      (hface r) (sectorEdge_outward P hgp o ho (f r)))
  have hgap : ∀ r, 0 ≤ orient (f r : Point) (d r) (c (f r)) := by
    intro r
    exact left_radial_join_coherent P hgp o ho (f r) (hdiff (f r)) (hleft (f (f r)))
  intro x hx
  obtain ⟨r,hr⟩ := coherent_strips_cover P hgp o ho c d hc hd hshape hgap x hx
  refine ⟨r,?_⟩
  rw [stripCell_eq_matchChannel _ _ _ _ _ (matchStartEnd_edge P hgp o ho (f r)).2.2.1] at hr
  exact hr

/-- Complete Case II.A all-right subcase. No exterior-cover premise. -/
theorem hasEmptySix_of_all_right_matches
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho)
    (hright : ∀ r, CanMatchRight P hgp o ho r) : HasEmptySix P := by
  by_contra hno
  let cells := fun r : ChainVertex P => matchChannel P r (chainCycle P hgp o ho r)
    (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
  have hc := card_le_sum_of_cover (hullVertices P) Finset.univ cells (by
    intro x hx
    obtain ⟨r,hr⟩ := right_matching_cover P hgp o ho hdiff hright x hx
    exact ⟨r,Finset.mem_univ _,hr⟩)
  have hb : ∀ r : ChainVertex P, (cells r).card ≤ 1 := by
    intro r
    exact boundary_match_channel_le_one P hgp hno r (chainCycle P hgp o ho r)
      (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
      (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho r)
      (sectorEdge_outward P hgp o ho r) (hright r)
  have hs : (∑ r : ChainVertex P, (cells r).card) ≤ Fintype.card (ChainVertex P) := by
    calc
      (∑ r : ChainVertex P, (cells r).card) ≤ ∑ _r : ChainVertex P, (1 : ℕ) :=
        Finset.sum_le_sum (fun r _ => hb r)
      _ = Fintype.card (ChainVertex P) := by simp
  have hCard : Fintype.card (ChainVertex P) = (ChainSecond P).card := Fintype.card_coe _
  have h3 := chain_second_card_ge_three P hgp o ho
  have hlt := second_card_lt_outer P hmin (Finset.card_pos.mp (by omega))
  rw [hCard] at hs
  omega

/-- Complete Case II.A all-left subcase. -/
theorem hasEmptySix_of_all_left_matches
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho)
    (hleft : ∀ r, CanMatchLeft P hgp o ho r) : HasEmptySix P := by
  by_contra hno
  let f := chainCycle P hgp o ho
  let cells := fun r : ChainVertex P => matchChannel P r (f r)
    (matchStart P hgp o ho (f r)) (matchEnd P hgp o ho (f r))
  have hc := card_le_sum_of_cover (hullVertices P) Finset.univ cells (by
    intro x hx
    obtain ⟨r,hr⟩ := left_matching_cover P hgp o ho hdiff hleft x hx
    exact ⟨r,Finset.mem_univ _,hr⟩)
  have hb : ∀ r : ChainVertex P, (cells r).card ≤ 1 := by
    intro r
    have hl := hleft (f r)
    change 0 < orient (matchStart P hgp o ho (f r)) (matchEnd P hgp o ho (f r))
      (f.symm (f r) : Point) at hl
    rw [Equiv.symm_apply_apply] at hl
    exact boundary_match_channel_le_one P hgp hno r (f r)
      (matchStart P hgp o ho (f r)) (matchEnd P hgp o ho (f r))
      (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho (f r))
      hl (sectorEdge_outward P hgp o ho (f r))
  have hs : (∑ r : ChainVertex P, (cells r).card) ≤ Fintype.card (ChainVertex P) := by
    calc
      (∑ r : ChainVertex P, (cells r).card) ≤ ∑ _r : ChainVertex P, (1 : ℕ) :=
        Finset.sum_le_sum (fun r _ => hb r)
      _ = Fintype.card (ChainVertex P) := by simp
  have hCard : Fintype.card (ChainVertex P) = (ChainSecond P).card := Fintype.card_coe _
  have h3 := chain_second_card_ge_three P hgp o ho
  have hlt := second_card_lt_outer P hmin (Finset.card_pos.mp (by omega))
  rw [hCard] at hs
  omega

end JSP198.Nicolas

#print axioms JSP198.Nicolas.hasEmptySix_of_all_right_matches
#print axioms JSP198.Nicolas.hasEmptySix_of_all_left_matches
#print axioms JSP198.Nicolas.right_matching_cover
#print axioms JSP198.Nicolas.left_matching_cover
