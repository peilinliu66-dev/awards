/-
Released under the MIT license.
Actual sector fibers are consecutive on the second-layer boundary cycle.
Uses only actual points and the completed supporting-edge/ray constructions.
-/
import Mathlib
import JSP198NicolasMatching

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

lemma radial_plucker (o u v a b : Point) :
    orient o u v * orient o a b =
      orient o u a * orient o v b - orient o u b * orient o v a := by
  unfold orient
  ring

/-- A clockwise boundary edge can exit a radial sector only through its second
boundary ray. This is a determinant identity, not an assumed radial order. -/
lemma fan_exit_crosses_second_ray
    (o u v a b : Point)
    (huv : orient o u v < 0) (hab : orient o a b < 0)
    (ha : InFan o u v a) (hb : ¬InFan o u v b)
    (hbv : orient o v b ≠ 0) :
    0 < raySide o v a ∧ raySide o v b < 0 := by
  have hua : orient o u a < 0 := by
    have he : orient u o a = -orient o u a := by unfold orient; ring
    have hfirst : 0 < orient u o a := ha.1
    rw [he] at hfirst
    linarith
  have hva : 0 < orient o v a := ha.2
  refine ⟨hva,?_⟩
  change orient o v b < 0
  by_contra hn
  have hvb : 0 < orient o v b :=
    lt_of_le_of_ne (le_of_not_gt hn) hbv.symm
  have hub : 0 ≤ orient o u b := by
    by_contra hneg
    have hlt : orient o u b < 0 := lt_of_not_ge hneg
    apply hb
    refine ⟨?_,hvb⟩
    have he : orient u o b = -orient o u b := by unfold orient; ring
    rw [he]
    linarith
  have h1 := mul_pos_of_neg_of_neg huv hab
  have h2 := mul_neg_of_neg_of_pos hua hvb
  have h3 := mul_nonneg hub hva.le
  have heq := radial_plucker o u v a b
  nlinarith

/-- At most one actual clockwise boundary edge exits a fixed radial fan. -/
theorem radial_fan_exit_unique
    (Q : Finset Point) (hgp : GeneralPosition Q)
    (o u v a b c d : Point)
    (hab : BoundaryEdge Q a b) (hcd : BoundaryEdge Q c d)
    (huv : orient o u v < 0)
    (habO : orient o a b < 0) (hcdO : orient o c d < 0)
    (ha : InFan o u v a) (hb : ¬InFan o u v b)
    (hc : InFan o u v c) (hd : ¬InFan o u v d)
    (hgenB : orient o v b ≠ 0) (hgenD : orient o v d ≠ 0) :
    a = c ∧ b = d := by
  obtain ⟨ha',hb'⟩ := fan_exit_crosses_second_ray o u v a b huv habO ha hb hgenB
  obtain ⟨hc',hd'⟩ := fan_exit_crosses_second_ray o u v c d huv hcdO hc hd hgenD
  exact boundary_fan_unique Q hgp o v a b c d hab hcd ha' hb' hc' hd'

lemma boundaryEdge_inner_strict
    (S : Finset Point) (hgp : GeneralPosition S)
    (o : Point) (ho : o ∈ inner S) (a b : Point)
    (he : BoundaryEdge (hullVertices S) a b) : orient o a b < 0 := by
  have hoS := (Finset.mem_sdiff.mp ho).1
  have hoa : o ≠ a := fun hh =>
    (Finset.mem_sdiff.mp ho).2 (by simpa only [hh] using he.1)
  have hob : o ≠ b := fun hh =>
    (Finset.mem_sdiff.mp ho).2 (by simpa only [hh] using he.2.1)
  have hle := boundaryEdge_hull_support he o hoS
  have hne := hgp a (hullVertices_subset S he.1) b (hullVertices_subset S he.2.1)
    o hoS he.2.2.1 hoa.symm hob.symm
  rw [orient_rotate o a b]
  exact lt_of_le_of_ne hle hne

/-- A double radial sector consists of consecutive actual layer-two vertices.
No cyclic interval assumption is used: two separated points would give two
exiting edges, contradicting the proved unique-exit theorem. -/
theorem same_sector_pair_adjacent
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (r s : ((hullVertices (inner P) : Finset Point) : Set Point))
    (hrs : r ≠ s) (heq : sectorEdge P hgp o ho r = sectorEdge P hgp o ho s) :
    BoundaryEdge (hullVertices (inner P)) r s ∨
    BoundaryEdge (hullVertices (inner P)) s r := by
  let R := hullVertices (inner P)
  let e := sectorEdge P hgp o ho r
  have he := mem_boundaryEdges.mp e.property
  have hgpI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hRgp : GeneralPosition R := gp_subset hgpI (hullVertices_subset (inner P))
  have hRc : InConvexPosition R := convexIndependent_hullVertices (inner P)
  have hR3 : 3 ≤ R.card := three_le_hull_of_inner_nonempty (inner P) hgpI
    ⟨o,(Finset.mem_sdiff.mp ho).1⟩
  let f := boundaryPerm R hRc hRgp (by omega : 2 ≤ R.card)
  have hrf : BoundaryEdge R r (f r) := boundaryPerm_edge R hRc hRgp _ r
  have hsf : BoundaryEdge R s (f s) := boundaryPerm_edge R hRc hRgp _ s
  by_cases hrfs : f r = s
  · exact Or.inl (by simpa only [hrfs] using hrf)
  by_cases hsfr : f s = r
  · exact Or.inr (by simpa only [hsfr] using hsf)
  have hrsp : (r : Point) ≠ (s : Point) := fun hh => hrs (Subtype.ext hh)
  have hrFan := sectorEdge_inFan P hgp o ho r
  have hsFan : InFan o e.val.1 e.val.2 s := by
    have hh := sectorEdge_inFan P hgp o ho s
    rw [← heq] at hh
    exact hh
  let C := outerFan (inner P) o e.val
  have hC2 : C.card ≤ 2 := third_layer_sector_card_le_two P hgp hno o ho e.val he
  have hPair : ({(r : Point),(s : Point)} : Finset Point) ⊆ C := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨r.property,hrFan⟩
    · exact Finset.mem_filter.mpr ⟨s.property,hsFan⟩
  have hCeq : C = {(r : Point),(s : Point)} := by
    symm
    apply Finset.eq_of_subset_of_card_le hPair
    simpa [hrsp] using hC2
  have hnrf : ¬InFan o e.val.1 e.val.2 (f r) := by
    intro hh
    have hm : (f r : Point) ∈ C := Finset.mem_filter.mpr ⟨(f r).property,hh⟩
    rw [hCeq] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with h | h
    · exact hrf.2.2.1 h.symm
    · exact hrfs (Subtype.ext h)
  have hnsf : ¬InFan o e.val.1 e.val.2 (f s) := by
    intro hh
    have hm : (f s : Point) ∈ C := Finset.mem_filter.mpr ⟨(f s).property,hh⟩
    rw [hCeq] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with h | h
    · exact hsfr (Subtype.ext h)
    · exact hsf.2.2.1 h.symm
  have hgpII := gp_subset hgpI (show inner (inner P) ⊆ inner P from Finset.sdiff_subset)
  have heO := boundaryEdge_inner_strict (inner (inner P)) hgpII o ho e.val.1 e.val.2 he
  have hrfO := boundaryEdge_inner_strict (inner P) hgpI o
    (Finset.mem_sdiff.mp ho).1 r (f r) hrf
  have hsfO := boundaryEdge_inner_strict (inner P) hgpI o
    (Finset.mem_sdiff.mp ho).1 s (f s) hsf
  have hgen : ∀ x ∈ R, orient o e.val.2 x ≠ 0 := by
    intro x hx
    have hoII := (Finset.mem_sdiff.mp ho).1
    have hoI := (Finset.mem_sdiff.mp hoII).1
    have hdII := hullVertices_subset (inner (inner P)) he.2.1
    have hdI := (Finset.mem_sdiff.mp hdII).1
    have hod : o ≠ e.val.2 := fun hh =>
      (Finset.mem_sdiff.mp ho).2 (by simpa only [hh] using he.2.1)
    have hox : o ≠ x := fun hh =>
      (Finset.mem_sdiff.mp hoII).2 (by simpa only [hh] using hx)
    have hdx : e.val.2 ≠ x := fun hh =>
      (Finset.mem_sdiff.mp hdII).2 (by simpa only [hh] using hx)
    exact hgpI o hoI e.val.2 hdI x (hullVertices_subset (inner P) hx) hod hox hdx
  have hh := radial_fan_exit_unique R hRgp o e.val.1 e.val.2 r (f r) s (f s)
    hrf hsf heO hrfO hsfO hrFan hnrf hsFan hnsf
    (hgen (f r) (f r).property) (hgen (f s) (f s).property)
  exact (hrsp hh.1).elim

/-- Double-sector vertices give an actual empty quadrilateral, with the order
chosen by the proved boundary adjacency rather than by a guessed enumeration. -/
theorem double_sector_empty_quad
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (r s : ((hullVertices (inner P) : Finset Point) : Set Point))
    (hrs : r ≠ s) (heq : sectorEdge P hgp o ho r = sectorEdge P hgp o ho s) :
    let c := (sectorEdge P hgp o ho r).val.1
    let d := (sectorEdge P hgp o ho r).val.2
    (BoundaryEdge (hullVertices (inner P)) r s ∧
      EmptyConvexPolygon P ({(r : Point),c,d,(s : Point)} : Finset Point)) ∨
    (BoundaryEdge (hullVertices (inner P)) s r ∧
      EmptyConvexPolygon P ({(s : Point),c,d,(r : Point)} : Finset Point)) := by
  dsimp only
  let e := sectorEdge P hgp o ho r
  have he := mem_boundaryEdges.mp e.property
  have hr := sectorEdge_outward P hgp o ho r
  have hs : 0 < orient e.val.1 e.val.2 s := by
    have hh := sectorEdge_outward P hgp o ho s
    rw [← heq] at hh
    exact hh
  rcases same_sector_pair_adjacent P hgp hno o ho r s hrs heq with h | h
  · exact Or.inl ⟨h,boundary_match_empty_quad P hgp r s e.val.1 e.val.2 h he hr hs⟩
  · exact Or.inr ⟨h,boundary_match_empty_quad P hgp s r e.val.1 e.val.2 h he hs hr⟩

end JSP198.Nicolas

#print axioms JSP198.Nicolas.same_sector_pair_adjacent
#print axioms JSP198.Nicolas.double_sector_empty_quad
