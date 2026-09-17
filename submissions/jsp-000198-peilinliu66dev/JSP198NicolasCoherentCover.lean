/-
Released under the MIT license.
Mathematical source: C. M. Nicolas, The Empty Hexagon Theorem (2007).
This file proves exterior covering from actual supporting edges and local
orientation inequalities. Covering is a CONCLUSION, not a data field.
The earlier JSP198Nicolas*.lean files and their attributed dependencies are unchanged.
-/
import Mathlib
import JSP198NicolasSectorOrder

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

abbrev ChainSecond (P : Finset Point) : Finset Point := hullVertices (inner P)
abbrev ChainThird (P : Finset Point) : Finset Point := hullVertices (inner (inner P))
abbrev ChainVertex (P : Finset Point) := ((ChainSecond P : Finset Point) : Set Point)

lemma chain_second_mem_inner {P : Finset Point} (r : ChainVertex P) :
    (r : Point) ∈ inner P := hullVertices_subset (inner P) r.property

lemma chain_third_mem_inner2 {P : Finset Point} {c : Point}
    (hc : c ∈ ChainThird P) : c ∈ inner (inner P) :=
  hullVertices_subset (inner (inner P)) hc

lemma chain_inner_ne_outer {P : Finset Point} {z x : Point}
    (hz : z ∈ inner P) (hx : x ∈ hullVertices P) : z ≠ x := by
  intro h
  exact (Finset.mem_sdiff.mp hz).2 (by simpa only [h] using hx)

lemma chain_inner2_ne_second {P : Finset Point} {z : Point}
    (hz : z ∈ inner (inner P)) (r : ChainVertex P) : z ≠ (r : Point) := by
  intro h
  exact (Finset.mem_sdiff.mp hz).2 (by rw [h]; exact r.property)

lemma chain_inner2_mem_hull {P : Finset Point} {z : Point}
    (hz : z ∈ inner (inner P)) :
    z ∈ convexHull ℝ (ChainSecond P : Set Point) := by
  rw [convexHull_hullVertices]
  exact subset_convexHull ℝ _ (Finset.mem_sdiff.mp hz).1

lemma chain_inner2_mem_interior {P : Finset Point} (hgp : GeneralPosition P)
    {z : Point} (hz : z ∈ inner (inner P)) :
    z ∈ interior (convexHull ℝ (ChainSecond P : Set Point)) := by
  exact mem_interior_hullVertices_of_not_mem (inner P)
    (gp_subset hgp Finset.sdiff_subset) z
    (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hz).2

lemma chain_second_card_ge_three
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) :
    3 ≤ (ChainSecond P).card :=
  three_le_hull_of_inner_nonempty (inner P) (gp_subset hgp Finset.sdiff_subset)
    ⟨o, (Finset.mem_sdiff.mp ho).1⟩

noncomputable def chainCycle
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) : Equiv.Perm (ChainVertex P) :=
  boundaryPerm (ChainSecond P) (convexIndependent_hullVertices (inner P))
    (gp_subset hgp ((hullVertices_subset (inner P)).trans Finset.sdiff_subset))
    (by have := chain_second_card_ge_three P hgp o ho; omega)

lemma chainCycle_edge
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P) :
    BoundaryEdge (ChainSecond P) r (chainCycle P hgp o ho r) :=
  boundaryPerm_edge _ _ _ _ r

lemma chainCycle_reaches
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r s : ChainVertex P) :
    ∃ j : ℕ, j ≤ (ChainSecond P).card ∧ orbit (chainCycle P hgp o ho) r j = s :=
  boundaryPerm_reaches _ _ _ _ r s

/-! A supporting corner contains the entire convex hull. The line under
consideration passes through its middle vertex; no polygon-order axiom is used. -/

lemma hull_in_corner_halfplane
    (Q : Finset Point) (hgp : GeneralPosition Q) (h3 : 3 ≤ Q.card)
    (u v w x : Point) (huv : BoundaryEdge Q u v) (hvw : BoundaryEdge Q v w)
    (hU : 0 ≤ orient v x u) (hW : 0 ≤ orient v x w) :
    convexHull ℝ (Q : Set Point) ⊆ {z : Point | 0 ≤ orient v x z} := by
  have huw := boundary_neighbors_ne Q hgp h3 u v w huv hvw
  have hbase := huv.strict hgp hvw.2.1 huw.symm hvw.2.2.1.symm
  have hD : 0 < orient v u w := by rw [orient_reverse]; linarith
  apply convexHull_min _ (convex_halfplane v x)
  intro z hz
  let B : ℝ := orient v z w / orient v u w
  let C : ℝ := orient v u z / orient v u w
  have hB : 0 ≤ B := by
    apply div_nonneg _ hD.le
    have h := hvw.2.2.2 z hz
    have he : orient v z w = -orient v w z := by unfold orient; ring
    rw [he]
    linarith
  have hC : 0 ≤ C := by
    apply div_nonneg _ hD.le
    have h := huv.2.2.2 z hz
    rw [orient_reverse]
    linarith
  have hzrep : z = (1-B-C) • v + B • u + C • w :=
    corner_affine v u w z (ne_of_gt hD)
  change 0 ≤ orient v x z
  rw [hzrep, orient_affine_comb v x v u w (1-B-C) B C (by ring)]
  have hv0 : orient v x v = 0 := by unfold orient; ring
  rw [hv0, mul_zero, zero_add]
  exact add_nonneg (mul_nonneg hB hU) (mul_nonneg hC hW)

/-- A visible incoming edge cannot become invisible while its outward connector
still points left of the exterior point. This proves the needed visible-chain
monotonicity directly from two genuine supporting edges. -/
lemma visible_next_of_connector
    (Q : Finset Point) (hgp : GeneralPosition Q) (h3 : 3 ≤ Q.card)
    (u v w c x : Point) (huv : BoundaryEdge Q u v) (hvw : BoundaryEdge Q v w)
    (hc : c ∈ convexHull ℝ (Q : Set Point))
    (hvis : 0 < orient u v x) (hconn : 0 < orient v c x) :
    0 < orient v w x := by
  by_contra hn
  have hle : orient v w x ≤ 0 := le_of_not_gt hn
  have hU : 0 ≤ orient v x u := by
    have he : orient v x u = orient u v x := by unfold orient; ring
    rw [he]; exact hvis.le
  have hW : 0 ≤ orient v x w := by
    have he : orient v x w = -orient v w x := by unfold orient; ring
    rw [he]; linarith
  have hh := hull_in_corner_halfplane Q hgp h3 u v w x huv hvw hU hW hc
  have he : orient v x c = -orient v c x := by unfold orient; ring
  change 0 ≤ orient v x c at hh
  rw [he] at hh
  linarith

/-- The only local joining condition used for the exterior-cover theorem.
It is a signed determinant inequality, not an assumed covering property. -/
lemma outward_connector_propagates
    (u v d a x : Point)
    (hvis : 0 < orient u v x)
    (hd : orient u v d < 0) (ha : orient u v a < 0)
    (hdx : 0 < orient v d x) (hgap : 0 ≤ orient v d a) :
    0 < orient v a x := by
  by_contra hn
  have hax : orient v a x ≤ 0 := le_of_not_gt hn
  have h1 : orient v u x < 0 := by rw [orient_reverse]; linarith
  have h2 : 0 < orient v u d := by rw [orient_reverse]; linarith
  have h3 : 0 < orient v u a := by rw [orient_reverse]; linarith
  have h4 : 0 ≤ orient v x a := by
    have he : orient v x a = -orient v a x := by unfold orient; ring
    rw [he]; linarith
  have h5 : orient v x d < 0 := by
    have he : orient v x d = -orient v d x := by unfold orient; ring
    rw [he]; linarith
  have hid := radial_plucker v u x d a
  have hL := mul_nonpos_of_nonpos_of_nonneg h1.le hgap
  have hR1 := mul_nonneg h2.le h4
  have hR2 := mul_neg_of_pos_of_neg h3 h5
  nlinarith

/-- An exterior point left of both lateral sides and outside the outer edge of
an actual convex quadrilateral is left of its inner edge as well. -/
lemma front_strip_middle
    (P : Finset Point) (hgp : GeneralPosition P)
    (x u c d v : Point) (hx : x ∈ hullVertices P)
    (hu : u ∈ inner P) (hc : c ∈ inner P)
    (hd : d ∈ inner P) (hv : v ∈ inner P)
    (h1 : 0 < orient u c d) (h2 : 0 < orient u c v)
    (h3 : 0 < orient u d v) (h4 : 0 < orient c d v)
    (hvis : 0 < orient u v x)
    (hleft : 0 < orient u c x) (hright : 0 < orient d v x) :
    0 < orient c d x := by
  have huP := (Finset.mem_sdiff.mp hu).1
  have hcP := (Finset.mem_sdiff.mp hc).1
  have hdP := (Finset.mem_sdiff.mp hd).1
  have hvP := (Finset.mem_sdiff.mp hv).1
  have hux := chain_inner_ne_outer hu hx
  have hcx := chain_inner_ne_outer hc hx
  have hdx := chain_inner_ne_outer hd hx
  have hvx := chain_inner_ne_outer hv hx
  have huc : u ≠ c := by rintro rfl; simp [orient] at h1
  have huv : u ≠ v := by rintro rfl; simp [orient] at h2
  have hdc : d ≠ c := by rintro rfl; unfold orient at h1; nlinarith
  have hdv : d ≠ v := by rintro rfl; unfold orient at h4; nlinarith
  have hcv : c ≠ v := by rintro rfl; simp [orient] at h4
  have hov := viewRank_overlap_of_balance P hgp x u d c v hx
    huP hdP hcP hvP hux hdx hcx hvx huc huv hdc hdv hcv
    (orient c d v) (orient u c v) (orient u d v) (orient u c d)
    h4 h2 h3 h1 (by intro z; unfold orient; ring)
  have hUC : viewRank P x u < viewRank P x c := by
    apply outer_viewRank_lt P hgp x u c hx huP hcP
    rw [orient_rotate x u c]; exact hleft
  have hUV : viewRank P x u < viewRank P x v := by
    apply outer_viewRank_lt P hgp x u v hx huP hvP
    rw [orient_rotate x u v]; exact hvis
  have hDV : viewRank P x d < viewRank P x v := by
    apply outer_viewRank_lt P hgp x d v hx hdP hvP
    rw [orient_rotate x d v]; exact hright
  by_contra hn
  have hneg : orient c d x < 0 := lt_of_le_of_ne (le_of_not_gt hn)
    (hgp c hcP d hdP x (hullVertices_subset P hx) hdc.symm hcx hdx)
  have hDC : viewRank P x d < viewRank P x c := by
    apply outer_viewRank_lt P hgp x d c hx hdP hcP
    have he : orient x d c = -orient c d x := by unfold orient; ring
    rw [he]; linarith
  omega

/-- A vertex cell is allowed (`c = d`); in that case it is exactly a fan.
An edge cell has all three strict channel signs. -/
def stripCell (P : Finset Point) (u v c d : Point) : Finset Point :=
  (hullVertices P).filter (fun x =>
    0 < orient u c x ∧ (c = d ∨ 0 < orient c d x) ∧ 0 < orient d v x)

lemma stripCell_eq_matchChannel (P : Finset Point) (u v c d : Point) (hcd : c ≠ d) :
    stripCell P u v c d = matchChannel P u v c d := by
  ext x
  simp [stripCell, matchChannel, hcd]

lemma stripCell_self_eq_outerFan (P : Finset Point) (u v c : Point) :
    stripCell P u v c c = outerFan P c (u,v) := by
  unfold stripCell outerFan
  apply Finset.filter_congr
  intro x hx
  simp [InFan]

/-- The one-step implication along the ACTUAL outer support cycle. -/
lemma coherent_strip_step
    (P : Finset Point) (hgp : GeneralPosition P)
    (x u v c d a : Point) (hx : x ∈ hullVertices P)
    (huv : BoundaryEdge (ChainSecond P) u v)
    (hc : c ∈ inner (inner P)) (hd : d ∈ inner (inner P))
    (ha : a ∈ inner (inner P))
    (hshape : c = d ∨
      (0 < orient u c d ∧ 0 < orient u c v ∧
       0 < orient u d v ∧ 0 < orient c d v))
    (hgap : 0 ≤ orient v d a)
    (hvis : 0 < orient u v x) (hleft : 0 < orient u c x)
    (hnot : x ∉ stripCell P u v c d) :
    0 < orient v a x := by
  have hu := hullVertices_subset (inner P) huv.1
  have hv := hullVertices_subset (inner P) huv.2.1
  have hcI := (Finset.mem_sdiff.mp hc).1
  have hdI := (Finset.mem_sdiff.mp hd).1
  have hnotright : ¬ 0 < orient d v x := by
    intro hright
    have hmid : c = d ∨ 0 < orient c d x := by
      rcases hshape with he | ⟨h1,h2,h3,h4⟩
      · exact Or.inl he
      · exact Or.inr (front_strip_middle P hgp x u c d v hx hu hcI hdI hv
          h1 h2 h3 h4 hvis hleft hright)
    exact hnot (Finset.mem_filter.mpr ⟨hx,hleft,hmid,hright⟩)
  have hdv : d ≠ v := fun he => (Finset.mem_sdiff.mp hd).2 (by simpa only [he] using huv.2.1)
  have hdx := chain_inner_ne_outer hdI hx
  have hvx := chain_inner_ne_outer hv hx
  have hneg : orient d v x < 0 := lt_of_le_of_ne (le_of_not_gt hnotright)
    (hgp d (Finset.mem_sdiff.mp hdI).1 v (Finset.mem_sdiff.mp hv).1
      x (hullVertices_subset P hx) hdv hdx hvx)
  have hdpos : 0 < orient v d x := by rw [orient_reverse]; linarith
  have hdi : orient u v d < 0 := by
    have hh := boundaryEdge_inner_strict (inner P) (gp_subset hgp Finset.sdiff_subset)
      d hd u v huv
    rw [orient_rotate d u v] at hh
    exact hh
  have hai : orient u v a < 0 := by
    have hh := boundaryEdge_inner_strict (inner P) (gp_subset hgp Finset.sdiff_subset)
      a ha u v huv
    rw [orient_rotate a u v] at hh
    exact hh
  exact outward_connector_propagates u v d a x hvis hdi hai hdpos hgap

lemma least_view_vertex_connector
    (P : Finset Point) (hgp : GeneralPosition P)
    (x : Point) (hx : x ∈ hullVertices P)
    (r : ChainVertex P)
    (hmin : ∀ y : ChainVertex P, viewRank P x r ≤ viewRank P x y)
    (c : Point) (hc : c ∈ inner (inner P)) :
    0 < orient (r : Point) c x := by
  have hrI := chain_second_mem_inner r
  have hrP := (Finset.mem_sdiff.mp hrI).1
  have hrx := chain_inner_ne_outer hrI hx
  have hside : ∀ y ∈ ChainSecond P, 0 ≤ orient x r y := by
    intro y hy
    by_contra hn
    have hneg : orient x r y < 0 := lt_of_not_ge hn
    have hpos : 0 < orient x y r := by
      have he : orient x y r = -orient x r y := by unfold orient; ring
      rw [he]; linarith
    have hyI := hullVertices_subset (inner P) hy
    have hh := outer_viewRank_lt P hgp x y r hx
      (Finset.mem_sdiff.mp hyI).1 hrP hpos
    have hm := hmin ⟨y,hy⟩
    change viewRank P x r ≤ viewRank P x y at hm
    omega
  have hcx := chain_inner_ne_outer (Finset.mem_sdiff.mp hc).1 hx
  by_contra hn
  have hle : orient x r c ≤ 0 := by
    have he : orient x r c = orient r c x := by unfold orient; ring
    rw [he]; exact le_of_not_gt hn
  exact not_mem_interior_convexHull_of_halfplane (ChainSecond P) x r c
    hrx.symm hside hle (chain_inner2_mem_interior hgp hc)

/-- Full exterior cover for a cycle of triangle/quadrilateral cells.
The hypotheses specify actual supporting edges, actual interior points, and
one signed determinant at each join. There is NO cover or winding assumption.
The proof follows a visible boundary chain and forces a strict integer-rank
increase forever if an outer extreme point were uncovered. -/
theorem coherent_strips_cover
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (c d : ChainVertex P → Point)
    (hc : ∀ r, c r ∈ inner (inner P))
    (hd : ∀ r, d r ∈ inner (inner P))
    (hshape : ∀ r,
      c r = d r ∨
      (0 < orient (r : Point) (c r) (d r) ∧
       0 < orient (r : Point) (c r) (chainCycle P hgp o ho r : Point) ∧
       0 < orient (r : Point) (d r) (chainCycle P hgp o ho r : Point) ∧
       0 < orient (c r) (d r) (chainCycle P hgp o ho r : Point)))
    (hgap : ∀ r, 0 ≤ orient (chainCycle P hgp o ho r : Point)
      (d r) (c (chainCycle P hgp o ho r))) :
    ∀ x ∈ hullVertices P, ∃ r : ChainVertex P,
      x ∈ stripCell P r (chainCycle P hgp o ho r) (c r) (d r) := by
  intro x hx
  let R := ChainSecond P
  let f := chainCycle P hgp o ho
  have hR3 : 3 ≤ R.card := chain_second_card_ge_three P hgp o ho
  have hRgp : GeneralPosition R := gp_subset hgp
    ((hullVertices_subset (inner P)).trans Finset.sdiff_subset)
  have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r0,hr0,hmin0⟩ := Finset.exists_min_image R (fun y => viewRank P x y) hRne
  let r : ChainVertex P := ⟨r0,hr0⟩
  have hmin : ∀ y : ChainVertex P, viewRank P x r ≤ viewRank P x y :=
    fun y => hmin0 y y.property
  have hconn0 := least_view_vertex_connector P hgp x hx r hmin (c r) (hc r)
  have hedge0 := chainCycle_edge P hgp o ho r
  have hneq : viewRank P x r ≠ viewRank P x (f r) :=
    outer_viewRank_ne P hgp x r (f r) hx
      (Finset.mem_sdiff.mp (chain_second_mem_inner r)).1
      (Finset.mem_sdiff.mp (chain_second_mem_inner (f r))).1
      (chain_inner_ne_outer (chain_second_mem_inner r) hx)
      (chain_inner_ne_outer (chain_second_mem_inner (f r)) hx) hedge0.2.2.1
  have hstart : 0 < orient (r : Point) (f r : Point) x := by
    have hh := (outer_viewRank_lt_iff P hgp x r (f r) hx
      (Finset.mem_sdiff.mp (chain_second_mem_inner r)).1
      (Finset.mem_sdiff.mp (chain_second_mem_inner (f r))).1
      (chain_inner_ne_outer (chain_second_mem_inner r) hx)
      (chain_inner_ne_outer (chain_second_mem_inner (f r)) hx)).mp
        (lt_of_le_of_ne (hmin (f r)) hneq)
    rw [orient_rotate x r (f r)] at hh
    exact hh
  by_contra hn
  have hnot : ∀ z : ChainVertex P,
      x ∉ stripCell P z (f z) (c z) (d z) := by
    intro z hz
    exact hn ⟨z,hz⟩
  have hstep : ∀ z : ChainVertex P,
      0 < orient (z : Point) (c z) x →
      0 < orient (z : Point) (f z : Point) x →
      0 < orient (f z : Point) (c (f z)) x ∧
      0 < orient (f z : Point) (f (f z) : Point) x := by
    intro z hconn hvis
    have hnconn := coherent_strip_step P hgp x z (f z) (c z) (d z) (c (f z)) hx
      (chainCycle_edge P hgp o ho z) (hc z) (hd z) (hc (f z))
      (hshape z) (hgap z) hvis hconn (hnot z)
    refine ⟨hnconn,?_⟩
    exact visible_next_of_connector R hRgp hR3 z (f z) (f (f z)) (c (f z)) x
      (chainCycle_edge P hgp o ho z) (chainCycle_edge P hgp o ho (f z))
      (chain_inner2_mem_hull (hc (f z))) hvis hnconn
  have hstates : ∀ j : ℕ,
      0 < orient (orbit (α := ChainVertex P) f r j : Point) (c (orbit (α := ChainVertex P) f r j)) x ∧
      0 < orient (orbit (α := ChainVertex P) f r j : Point) (f (orbit (α := ChainVertex P) f r j) : Point) x := by
    intro j
    induction j with
    | zero => exact ⟨hconn0,hstart⟩
    | succ j ih => exact hstep (orbit (α := ChainVertex P) f r j) ih.1 ih.2
  have hgrowth : ∀ j : ℕ, j ≤ viewRank P x (orbit (α := ChainVertex P) f r j) := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have hh := outer_viewRank_lt P hgp x (orbit (α := ChainVertex P) f r j) (f (orbit (α := ChainVertex P) f r j)) hx
        (Finset.mem_sdiff.mp (chain_second_mem_inner (orbit (α := ChainVertex P) f r j))).1
        (Finset.mem_sdiff.mp (chain_second_mem_inner (f (orbit (α := ChainVertex P) f r j)))).1
        (by rw [orient_rotate x (orbit (α := ChainVertex P) f r j) (f (orbit (α := ChainVertex P) f r j))]; exact (hstates j).2)
      change j+1 ≤ viewRank P x (f (orbit (α := ChainVertex P) f r j))
      omega
  have hlo := hgrowth (P.card+1)
  have hup : viewRank P x (orbit (α := ChainVertex P) f r (P.card+1)) ≤ P.card := Nat.sub_le _ _
  omega

/-- A proved exterior cover gives the exact finite capacity inequality. -/
theorem coherent_strips_card_le
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (c d : ChainVertex P → Point)
    (hc : ∀ r, c r ∈ inner (inner P)) (hd : ∀ r, d r ∈ inner (inner P))
    (hshape : ∀ r, c r = d r ∨
      (0 < orient (r : Point) (c r) (d r) ∧
       0 < orient (r : Point) (c r) (chainCycle P hgp o ho r : Point) ∧
       0 < orient (r : Point) (d r) (chainCycle P hgp o ho r : Point) ∧
       0 < orient (c r) (d r) (chainCycle P hgp o ho r : Point)))
    (hgap : ∀ r, 0 ≤ orient (chainCycle P hgp o ho r : Point)
      (d r) (c (chainCycle P hgp o ho r))) :
    (hullVertices P).card ≤
      ∑ r : ChainVertex P,
        (stripCell P r (chainCycle P hgp o ho r) (c r) (d r)).card := by
  apply card_le_sum_of_cover (hullVertices P) Finset.univ
    (fun r : ChainVertex P => stripCell P r (chainCycle P hgp o ho r) (c r) (d r))
  intro x hx
  obtain ⟨r,hr⟩ := coherent_strips_cover P hgp o ho c d hc hd hshape hgap x hx
  exact ⟨r,Finset.mem_univ _,hr⟩

lemma second_card_lt_outer
    (P : Finset Point) (hmin : MinimalOuter P)
    (hRne : (ChainSecond P).Nonempty) :
    (ChainSecond P).card < (hullVertices P).card := by
  apply hmin.smaller (ChainSecond P)
  · exact (hullVertices_subset (inner P)).trans Finset.sdiff_subset
  · intro z hz
    rw [convexHull_hullVertices]
    exact subset_convexHull ℝ _ ((Finset.mem_sdiff.mp
      (hullVertices_subset (inner P) hz)).1)
  · exact convexIndependent_hullVertices (inner P)
  · intro he
    obtain ⟨z,hz⟩ := hRne
    have hzI := hullVertices_subset (inner P) hz
    exact (Finset.mem_sdiff.mp hzI).2 (by simpa only [he] using hz)

end JSP198.Nicolas

#print axioms JSP198.Nicolas.coherent_strips_cover
#print axioms JSP198.Nicolas.coherent_strips_card_le
