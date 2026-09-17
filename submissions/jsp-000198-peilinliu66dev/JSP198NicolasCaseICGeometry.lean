/-
Released under the MIT license.
Mathematics: Carlos M. Nicolas, The Empty Hexagon Theorem (2007), Case I.C.
This module proves the actual three-cell exterior cap cover and the two
one-point-channel eliminations. It imports the user's compiled local glue.
No covering statement, cyclic-order axiom, or emptiness theorem is assumed.
-/
import Mathlib
import JSP198NicolasCaseIRuns
import JSP198NicolasOnePointGlue

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

private lemma ic_rank_lt_iff
    (P : Finset Point) (hgp : GeneralPosition P)
    (x : Point) (hx : x ∈ hullVertices P)
    (a b : Point) (ha : a ∈ inner P) (hb : b ∈ inner P) :
    viewRank P x a < viewRank P x b ↔ 0 < orient a b x := by
  have h := outer_viewRank_lt_iff P hgp x a b hx
    (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1
    (chain_inner_ne_outer ha hx) (chain_inner_ne_outer hb hx)
  rw [orient_rotate x a b] at h
  exact h

/-- Both open diagonal-projection intervals overlap for an actual convex
quadrilateral. The sign convention here is counterclockwise. -/
private lemma ic_quad_view_overlap_pos
    (P : Finset Point) (hgp : GeneralPosition P)
    (x a b c d : Point) (hx : x ∈ hullVertices P)
    (ha : a ∈ inner P) (hb : b ∈ inner P)
    (hc : c ∈ inner P) (hd : d ∈ inner P)
    (h1 : 0 < orient a b c) (h2 : 0 < orient a b d)
    (h3 : 0 < orient a c d) (h4 : 0 < orient b c d) :
    min (viewRank P x a) (viewRank P x c) <
      max (viewRank P x b) (viewRank P x d) ∧
    min (viewRank P x b) (viewRank P x d) <
      max (viewRank P x a) (viewRank P x c) := by
  have hab : a ≠ b := by intro h; subst b; unfold orient at h1; nlinarith
  have hac : a ≠ c := by intro h; subst c; unfold orient at h1; nlinarith
  have had : a ≠ d := by intro h; subst d; unfold orient at h2; nlinarith
  have hbc : b ≠ c := by intro h; subst c; unfold orient at h1; nlinarith
  have hbd : b ≠ d := by intro h; subst d; unfold orient at h2; nlinarith
  have hcd : c ≠ d := by intro h; subst d; unfold orient at h3; nlinarith
  have hap := (Finset.mem_sdiff.mp ha).1
  have hbp := (Finset.mem_sdiff.mp hb).1
  have hcp := (Finset.mem_sdiff.mp hc).1
  have hdp := (Finset.mem_sdiff.mp hd).1
  have hax := chain_inner_ne_outer ha hx
  have hbx := chain_inner_ne_outer hb hx
  have hcx := chain_inner_ne_outer hc hx
  have hdx := chain_inner_ne_outer hd hx
  have hsecond := viewRank_overlap_of_balance P hgp x a c b d hx
    hap hcp hbp hdp hax hcx hbx hdx
    hab had hbc.symm hcd hbd
    (orient b c d) (orient a b d) (orient a c d) (orient a b c)
    h4 h2 h3 h1 (by intro y; unfold orient; ring)
  have hfirst := viewRank_overlap_of_balance P hgp x b d a c hx
    hbp hdp hap hcp hbx hdx hax hcx
    hab.symm hbc had.symm hcd.symm hac
    (orient a c d) (orient a b c) (orient b c d) (orient a b d)
    h3 h1 h4 h2 (by intro y; unfold orient; ring)
  exact ⟨hfirst, hsecond⟩

private lemma ic_quad_view_overlap_neg
    (P : Finset Point) (hgp : GeneralPosition P)
    (x a b c d : Point) (hx : x ∈ hullVertices P)
    (ha : a ∈ inner P) (hb : b ∈ inner P)
    (hc : c ∈ inner P) (hd : d ∈ inner P)
    (h1 : orient a b c < 0) (h2 : orient a b d < 0)
    (h3 : orient a c d < 0) (h4 : orient b c d < 0) :
    min (viewRank P x a) (viewRank P x c) <
      max (viewRank P x b) (viewRank P x d) ∧
    min (viewRank P x b) (viewRank P x d) <
      max (viewRank P x a) (viewRank P x c) := by
  have e1 : orient a d c = -orient a c d := by unfold orient; ring
  have e2 : orient a d b = -orient a b d := by unfold orient; ring
  have e3 : orient a c b = -orient a b c := by unfold orient; ring
  have e4 : orient d c b = -orient b c d := by unfold orient; ring
  have hh := ic_quad_view_overlap_pos P hgp x a d c b hx ha hd hc hb
    (by rw [e1]; linarith) (by rw [e2]; linarith)
    (by rw [e3]; linarith) (by rw [e4]; linarith)
  simpa only [min_comm, max_comm] using hh

/-- A strict inner point of this four-point hull has a viewing rank strictly
between the minimum and maximum of its vertices. Only hull membership is used. -/
private lemma ic_view_bounds_quad
    (P : Finset Point) (hgp : GeneralPosition P)
    (x a b c d z : Point) (hx : x ∈ hullVertices P)
    (ha : a ∈ inner P) (hb : b ∈ inner P)
    (hc : c ∈ inner P) (hd : d ∈ inner P) (hz : z ∈ inner P)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) (hzd : z ≠ d)
    (hzH : z ∈ convexHull ℝ ({a,b,c,d} : Set Point)) :
    min (viewRank P x a) (min (viewRank P x b)
      (min (viewRank P x c) (viewRank P x d))) < viewRank P x z ∧
    viewRank P x z < max (viewRank P x a) (max (viewRank P x b)
      (max (viewRank P x c) (viewRank P x d))) := by
  have nzA := outer_viewRank_ne P hgp x z a hx
    (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp ha).1
    (chain_inner_ne_outer hz hx) (chain_inner_ne_outer ha hx) hza
  have nzB := outer_viewRank_ne P hgp x z b hx
    (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hb).1
    (chain_inner_ne_outer hz hx) (chain_inner_ne_outer hb hx) hzb
  have nzC := outer_viewRank_ne P hgp x z c hx
    (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hc).1
    (chain_inner_ne_outer hz hx) (chain_inner_ne_outer hc hx) hzc
  have nzD := outer_viewRank_ne P hgp x z d hx
    (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hd).1
    (chain_inner_ne_outer hz hx) (chain_inner_ne_outer hd hx) hzd
  constructor
  · by_contra hn
    have hA := (ic_rank_lt_iff P hgp x hx z a hz ha).mp (by omega)
    have hB := (ic_rank_lt_iff P hgp x hx z b hz hb).mp (by omega)
    have hC := (ic_rank_lt_iff P hgp x hx z c hz hc).mp (by omega)
    have hD := (ic_rank_lt_iff P hgp x hx z d hz hd).mp (by omega)
    have hs : convexHull ℝ ({a,b,c,d} : Set Point) ⊆ {y | 0 < orient x z y} := by
      apply convexHull_min _ (convex_strict_orient x z)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      change 0 < orient x z y
      rcases hy with hy | hy | hy | hy <;> subst y <;>
        rw [orient_rotate x z _] <;> assumption
    have hh := hs hzH
    change 0 < orient x z z at hh
    unfold orient at hh
    nlinarith
  · by_contra hn
    have hA := (ic_rank_lt_iff P hgp x hx a z ha hz).mp (by omega)
    have hB := (ic_rank_lt_iff P hgp x hx b z hb hz).mp (by omega)
    have hC := (ic_rank_lt_iff P hgp x hx c z hc hz).mp (by omega)
    have hD := (ic_rank_lt_iff P hgp x hx d z hd hz).mp (by omega)
    have hs : convexHull ℝ ({a,b,c,d} : Set Point) ⊆ {y | 0 < orient z x y} := by
      apply convexHull_min _ (convex_strict_orient z x)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      change 0 < orient z x y
      have he : ∀ y, orient z x y = orient y z x := by
        intro y; unfold orient; ring
      rcases hy with hy | hy | hy | hy <;> subst y <;> rw [he] <;> assumption
    have hh := hs hzH
    change 0 < orient z x z at hh
    unfold orient at hh
    nlinarith

/-- Exact finite order statement for the three cells in Case I.C.
The earlier proved ear-order lemma supplies two larger cones. The following
case split refines them, using actual hull bounds and the two matched diagonals. -/
private lemma ic_three_cell_order (t l s u c z d : ℕ)
    (hcL : min t (min z u) < c) (hcU : c < max t (max z u))
    (hdL : min t (min z u) < d) (hdU : d < max t (max z u))
    (hzL : min t (min l (min s u)) < z)
    (hzU : z < max t (max l (max s u)))
    (hQ1 : min t d < max c u) (hQ2 : min c u < max t d)
    (hL : min c l < max t z) (hR : min z u < max s d)
    (hzl : z ≠ l) (hzs : z ≠ s)
    (hvis : t < c ∨ c < d ∨ d < u) :
    (t < c ∧ c < z ∧ z < l) ∨
      (l < z ∧ z < s) ∨ (s < z ∧ z < d ∧ d < u) := by
  have hcone := ear_cover_order t z u c d hcL hcU hdL hdU hQ2 hQ1 hvis
  rcases hcone with ⟨htc,hcz⟩ | ⟨hzd,hdu⟩
  · by_cases hzl' : z < l
    · exact Or.inl ⟨htc,hcz,hzl'⟩
    have hlz : l < z := by omega
    by_cases hzs' : z < s
    · exact Or.inr (Or.inl ⟨hlz,hzs'⟩)
    have hsz : s < z := by omega
    have hzu : z < u := by omega
    have hzd' : z < d := by omega
    have hdu' : d < u := by omega
    exact Or.inr (Or.inr ⟨hsz,hzd',hdu'⟩)
  · by_cases hsz : s < z
    · exact Or.inr (Or.inr ⟨hsz,hzd,hdu⟩)
    have hzs' : z < s := by omega
    by_cases hlz : l < z
    · exact Or.inr (Or.inl ⟨hlz,hzs'⟩)
    have hzl' : z < l := by omega
    have htz : t < z := by omega
    have hcz : c < z := by omega
    have htc : t < c := by omega
    exact Or.inl ⟨htc,hcz,hzl'⟩

/-- The chord through c,d cuts off the middle vertex z. If the two outside
vertices t,u are on the other side and face the two adjacent inner edges,
the replacement quadruple and all required triangle/hull containments follow. -/
theorem ic_middle_chord_geometry
    (P : Finset Point) (hgp : GeneralPosition P)
    (t l s u : ChainVertex P) (c z d : Point)
    (hc : c ∈ inner (inner P)) (hz : z ∈ inner (inner P))
    (hd : d ∈ inner (inner P))
    (htl : BoundaryEdge (ChainSecond P) t l)
    (hls : BoundaryEdge (ChainSecond P) l s)
    (hsu : BoundaryEdge (ChainSecond P) s u)
    (htri : orient c z d < 0)
    (hct : 0 < orient c z t) (hdu : 0 < orient z d u)
    (ht : orient c d t < 0) (hu : orient c d u < 0) :
    orient (t : Point) c d < 0 ∧ orient (t : Point) c u < 0 ∧
    orient (t : Point) d u < 0 ∧ orient c d u < 0 ∧
    c ∈ convexHull ℝ ({(t : Point),z,(u : Point)} : Set Point) ∧
    d ∈ convexHull ℝ ({(t : Point),z,(u : Point)} : Set Point) ∧
    z ∈ convexHull ℝ ({(t : Point),(l : Point),(s : Point),(u : Point)} : Set Point) := by
  have hgI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hgR := gp_subset hgI (hullVertices_subset (inner P))
  have htI := chain_second_mem_inner t
  have hlI := chain_second_mem_inner l
  have hsI := chain_second_mem_inner s
  have huI := chain_second_mem_inner u
  have hcI := (Finset.mem_sdiff.mp hc).1
  have hzI := (Finset.mem_sdiff.mp hz).1
  have hdI := (Finset.mem_sdiff.mp hd).1
  have hczU : orient c z u < 0 := by
    have he : orient c z d = orient c z u + orient z d u - orient c d u := by
      unfold orient; ring
    linarith
  have hzdT : orient z d t < 0 := by
    have he : orient c z d = orient c z t + orient z d t - orient c d t := by
      unfold orient; ring
    linarith
  have hTCU : orient (t : Point) c u < 0 := by
    have he : orient c z d * orient c t u =
      orient c z t * orient c d u - orient c z u * orient c d t := by
      unfold orient; ring
    have hp := mul_neg_of_pos_of_neg hct hu
    have hq := mul_pos_of_neg_of_neg hczU ht
    have hctu : 0 < orient c t u := by
      by_contra hn
      have hh := mul_nonneg_of_nonpos_of_nonpos htri.le (le_of_not_gt hn)
      nlinarith
    have hr : orient (t : Point) c u = -orient c t u := by unfold orient; ring
    rw [hr]; linarith
  have hTDU : orient (t : Point) d u < 0 := by
    have he : orient c z d * orient d t u =
      orient c d t * orient z d u - orient c d u * orient z d t := by
      unfold orient; ring
    have hp := mul_neg_of_neg_of_pos ht hdu
    have hq := mul_pos_of_neg_of_neg hu hzdT
    have hdtu : 0 < orient d t u := by
      by_contra hn
      have hh := mul_nonneg_of_nonpos_of_nonpos htri.le (le_of_not_gt hn)
      nlinarith
    have hr : orient (t : Point) d u = -orient d t u := by unfold orient; ring
    rw [hr]; linarith
  have hTCD : orient (t : Point) c d < 0 := by
    rw [orient_rotate]; exact ht
  have hTUC : 0 < orient (t : Point) u c := by
    have he : orient (t : Point) u c = -orient (t : Point) c u := by unfold orient; ring
    rw [he]; linarith
  have hTCZ : 0 < orient (t : Point) c z := by rw [orient_rotate]; exact hct
  have hTUZ := orient_pos_trans_from_hull_vertex (inner P) hgI
    t u c z t.property huI hcI hzI hTUC hTCZ
  have hC : c ∈ convexHull ℝ ({(t : Point),z,(u : Point)} : Set Point) := by
    have hUZC : 0 < orient (u : Point) z c := by
      have he : orient (u : Point) z c = -orient c z u := by unfold orient; ring
      rw [he]; linarith
    have hZTC : 0 < orient z t c := by
      have he : orient z t c = orient c z t := by unfold orient; ring
      rwa [he]
    have hh := interior_subset (mem_interior_triangle_of_orient_pos
      (t : Point) u z c hTUZ hTUC hUZC hZTC)
    apply convexHull_mono _ hh
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    tauto
  have hD : d ∈ convexHull ℝ ({(t : Point),z,(u : Point)} : Set Point) := by
    have hTUD : 0 < orient (t : Point) u d := by
      have he : orient (t : Point) u d = -orient (t : Point) d u := by unfold orient; ring
      rw [he]; linarith
    have hUZD : 0 < orient (u : Point) z d := by rw [orient_rotate]; exact hdu
    have hZTD : 0 < orient z t d := by
      have he : orient z t d = -orient z d t := by unfold orient; ring
      rw [he]; linarith
    have hh := interior_subset (mem_interior_triangle_of_orient_pos
      (t : Point) u z d hTUZ hTUD hUZD hZTD)
    apply convexHull_mono _ hh
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    tauto
  have hR3 : 3 ≤ (ChainSecond P).card :=
    three_le_hull_of_inner_nonempty (inner P) hgI ⟨z,hz⟩
  have hts := boundary_neighbors_ne (ChainSecond P) hgR hR3 t l s htl hls
  have htu : (t : Point) ≠ u := by intro he; rw [he] at hTCU; simp [orient] at hTCU
  have hzT := chain_inner2_ne_second hz t
  have hzL := chain_inner2_ne_second hz l
  have hzS := chain_inner2_ne_second hz s
  have hzU := chain_inner2_ne_second hz u
  have htlZ : orient (t : Point) l z < 0 := by
    have hh := boundaryEdge_inner_strict (inner P) hgI z hz t l htl
    rwa [orient_rotate z t l] at hh
  have hlsZ : orient (l : Point) s z < 0 := by
    have hh := boundaryEdge_inner_strict (inner P) hgI z hz l s hls
    rwa [orient_rotate z l s] at hh
  have hsuZ : orient (s : Point) u z < 0 := by
    have hh := boundaryEdge_inner_strict (inner P) hgI z hz s u hsu
    rwa [orient_rotate z s u] at hh
  have htlS := htl.strict hgR s.property hts.symm hls.2.2.1.symm
  have htsU : orient (t : Point) s u < 0 := by
    have hh := hsu.strict hgR t.property hts htu
    rwa [← orient_rotate t s u] at hh
  have hdiag := hgp (t : Point) (Finset.mem_sdiff.mp htI).1
    s (Finset.mem_sdiff.mp hsI).1 z (Finset.mem_sdiff.mp hzI).1 hts hzT.symm hzS.symm
  have hZ : z ∈ convexHull ℝ
      ({(t : Point),(l : Point),(s : Point),(u : Point)} : Set Point) := by
    rcases lt_or_gt_of_ne hdiag with hneg | hpos
    · have hTUS : 0 < orient (t : Point) u s := by
        have he : orient (t : Point) u s = -orient (t : Point) s u := by unfold orient; ring
        rw [he]; linarith
      have hUSZ : 0 < orient (u : Point) s z := by rw [orient_reverse]; linarith
      have hSTZ : 0 < orient (s : Point) t z := by rw [orient_reverse]; linarith
      have hh := interior_subset (mem_interior_triangle_of_orient_pos
        (t : Point) u s z hTUS hTUZ hUSZ hSTZ)
      apply convexHull_mono _ hh
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      tauto
    · have hTSL : 0 < orient (t : Point) s l := by
        have he : orient (t : Point) s l = -orient (t : Point) l s := by unfold orient; ring
        rw [he]; linarith
      have hSLZ : 0 < orient (s : Point) l z := by rw [orient_reverse]; linarith
      have hLTZ : 0 < orient (l : Point) t z := by rw [orient_reverse]; linarith
      have hh := interior_subset (mem_interior_triangle_of_orient_pos
        (t : Point) s l z hTSL hpos hSLZ hLTZ)
      apply convexHull_mono _ hh
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      tauto
  exact ⟨hTCD,hTCU,hTDU,hu,hC,hD,hZ⟩

/-- The exact three-region cap cover at the middle-chord subcase.
All triangle membership and diagonal-overlap conditions are derived here. -/
theorem ic_three_cell_exterior_cover
    (P : Finset Point) (hgp : GeneralPosition P)
    (t l s u : ChainVertex P) (c z d : Point)
    (htl : BoundaryEdge (ChainSecond P) t l)
    (hls : BoundaryEdge (ChainSecond P) l s)
    (hsu : BoundaryEdge (ChainSecond P) s u)
    (hcz : BoundaryEdge (ChainThird P) c z)
    (hzd : BoundaryEdge (ChainThird P) z d)
    (htri : orient c z d < 0)
    (hct : 0 < orient c z t) (hcl : 0 < orient c z l)
    (hds : 0 < orient z d s) (hdu : 0 < orient z d u)
    (ht : orient c d t < 0) (hu : orient c d u < 0)
    (x : Point) (hx : x ∈ hullVertices P)
    (hvis : 0 < orient (t : Point) c x ∨ 0 < orient c d x ∨
      0 < orient d (u : Point) x) :
    x ∈ matchChannel P t l c z ∨
      x ∈ outerFan P z (l,s) ∨ x ∈ matchChannel P s u z d := by
  have hc := chain_third_mem_inner2 hcz.1
  have hz := chain_third_mem_inner2 hcz.2.1
  have hd := chain_third_mem_inner2 hzd.2.1
  have htI := chain_second_mem_inner t
  have hlI := chain_second_mem_inner l
  have hsI := chain_second_mem_inner s
  have huI := chain_second_mem_inner u
  have hcI := (Finset.mem_sdiff.mp hc).1
  have hzI := (Finset.mem_sdiff.mp hz).1
  have hdI := (Finset.mem_sdiff.mp hd).1
  obtain ⟨q1,q2,q3,q4,hC,hD,hZ⟩ := ic_middle_chord_geometry
    P hgp t l s u c z d hc hz hd htl hls hsu htri hct hdu ht hu
  have hP := fun {a : Point} (ha : a ∈ inner P) => (Finset.mem_sdiff.mp ha).1
  have hX := fun {a : Point} (ha : a ∈ inner P) => chain_inner_ne_outer ha hx
  have hcT := chain_inner2_ne_second hc t
  have hcU := chain_inner2_ne_second hc u
  have hdT := chain_inner2_ne_second hd t
  have hdU := chain_inner2_ne_second hd u
  have hzT := chain_inner2_ne_second hz t
  have hzL := chain_inner2_ne_second hz l
  have hzS := chain_inner2_ne_second hz s
  have hzU := chain_inner2_ne_second hz u
  obtain ⟨cL,cU⟩ := viewRank_triangle_bounds P hgp x t z u c hx
    (hP htI) (hP hzI) (hP huI) (hP hcI)
    (hX htI) (hX hzI) (hX huI) (hX hcI) hcT hcz.2.2.1 hcU hC
  obtain ⟨dL,dU⟩ := viewRank_triangle_bounds P hgp x t z u d hx
    (hP htI) (hP hzI) (hP huI) (hP hdI)
    (hX htI) (hX hzI) (hX huI) (hX hdI) hdT hzd.2.2.1.symm hdU hD
  obtain ⟨zL,zU⟩ := ic_view_bounds_quad P hgp x t l s u z hx
    htI hlI hsI huI hzI hzT hzL hzS hzU hZ
  obtain ⟨Q1,Q2⟩ := ic_quad_view_overlap_neg P hgp x t c d u hx
    htI hcI hdI huI q1 q2 q3 q4
  obtain ⟨a1,a2,a3,a4⟩ := boundary_match_four_signs P hgp t l c z htl hcz hct hcl
  obtain ⟨L1,L2⟩ := ic_quad_view_overlap_pos P hgp x t c z l hx
    htI hcI hzI hlI a1 a2 a3 a4
  obtain ⟨b1,b2,b3,b4⟩ := boundary_match_four_signs P hgp s u z d hsu hzd hds hdu
  obtain ⟨R1,R2⟩ := ic_quad_view_overlap_pos P hgp x s z d u hx
    hsI hzI hdI huI b1 b2 b3 b4
  have nzL := outer_viewRank_ne P hgp x z l hx (hP hzI) (hP hlI)
    (hX hzI) (hX hlI) hzL
  have nzS := outer_viewRank_ne P hgp x z s hx (hP hzI) (hP hsI)
    (hX hzI) (hX hsI) hzS
  have hv : viewRank P x t < viewRank P x c ∨
      viewRank P x c < viewRank P x d ∨ viewRank P x d < viewRank P x u := by
    rcases hvis with h | h | h
    · exact Or.inl ((ic_rank_lt_iff P hgp x hx t c htI hcI).mpr h)
    · exact Or.inr (Or.inl ((ic_rank_lt_iff P hgp x hx c d hcI hdI).mpr h))
    · exact Or.inr (Or.inr ((ic_rank_lt_iff P hgp x hx d u hdI huI).mpr h))
  have hh := ic_three_cell_order (viewRank P x t) (viewRank P x l)
    (viewRank P x s) (viewRank P x u) (viewRank P x c) (viewRank P x z)
    (viewRank P x d) cL cU dL dU zL zU Q1 Q2 L2 R2 nzL nzS hv
  rcases hh with ⟨h1,h2,h3⟩ | ⟨h1,h2⟩ | ⟨h1,h2,h3⟩
  · exact Or.inl (Finset.mem_filter.mpr ⟨hx,
      (ic_rank_lt_iff P hgp x hx t c htI hcI).mp h1,
      (ic_rank_lt_iff P hgp x hx c z hcI hzI).mp h2,
      (ic_rank_lt_iff P hgp x hx z l hzI hlI).mp h3⟩)
  · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hx,
      (ic_rank_lt_iff P hgp x hx l z hlI hzI).mp h1,
      (ic_rank_lt_iff P hgp x hx z s hzI hsI).mp h2⟩))
  · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hx,
      (ic_rank_lt_iff P hgp x hx s z hsI hzI).mp h1,
      (ic_rank_lt_iff P hgp x hx z d hzI hdI).mp h2,
      (ic_rank_lt_iff P hgp x hx d u hdI huI).mp h3⟩))

/-- An entire geometric subcase of I.C: both outside neighbors lie on the far
side of the chord c,d. The replacement has four points but its cap must have
five; the proved three-cell cover has capacity 1+2+1. -/
theorem hasEmptySix_of_ic_middle_chord_negative
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (t l s u : ChainVertex P) (c z d : Point)
    (htl : BoundaryEdge (ChainSecond P) t l)
    (hls : BoundaryEdge (ChainSecond P) l s)
    (hsu : BoundaryEdge (ChainSecond P) s u)
    (hcz : BoundaryEdge (ChainThird P) c z)
    (hzd : BoundaryEdge (ChainThird P) z d)
    (htri : orient c z d < 0)
    (hct : 0 < orient c z t) (hcl : 0 < orient c z l)
    (hds : 0 < orient z d s) (hdu : 0 < orient z d u)
    (ht : orient c d t < 0) (hu : orient c d u < 0) : HasEmptySix P := by
  by_contra hno
  have hc := chain_third_mem_inner2 hcz.1
  have hz := chain_third_mem_inner2 hcz.2.1
  have hd := chain_third_mem_inner2 hzd.2.1
  obtain ⟨q1,q2,q3,q4,_,_,_⟩ := ic_middle_chord_geometry
    P hgp t l s u c z d hc hz hd htl hls hsu htri hct hdu ht hu
  let T : Finset Point := {(t : Point),c,d,(u : Point)}
  let D : Finset Point := (hullVertices P).filter (fun x =>
    0 ≤ orient (t : Point) c x ∨ 0 ≤ orient c d x ∨ 0 ≤ orient d (u : Point) x)
  have htI := chain_second_mem_inner t
  have huI := chain_second_mem_inner u
  have hcI := (Finset.mem_sdiff.mp hc).1
  have hdI := (Finset.mem_sdiff.mp hd).1
  have hTI : T ⊆ inner P := by
    intro x hx
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hTP : T ⊆ P := hTI.trans Finset.sdiff_subset
  have htc := (chain_inner2_ne_second hc t).symm
  have htd := (chain_inner2_ne_second hd t).symm
  have hcu := chain_inner2_ne_second hc u
  have hdu' := chain_inner2_ne_second hd u
  have htu : (t : Point) ≠ u := by intro he; rw [he] at q2; simp [orient] at q2
  have hcd : c ≠ d := by intro he; subst d; simp [orient] at htri
  have hT4 : T.card = 4 := by simp [T,htc,htd,htu,hcd,hcu,hdu']
  have hside1 : ∀ y ∈ T, orient (t : Point) c y ≤ 0 := by
    intro y hy
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy <;> subst y
    · unfold orient; nlinarith
    · unfold orient; nlinarith
    · exact q1.le
    · exact q2.le
  have hside2 : ∀ y ∈ T, orient d (u : Point) y ≤ 0 := by
    intro y hy
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy <;> subst y
    · rw [← orient_rotate (t : Point) d u]; exact q3.le
    · rw [← orient_rotate c d u]; exact q4.le
    · unfold orient; nlinarith
    · unfold orient; nlinarith
  have hout1 : ∀ y ∈ hullVertices P \ D, orient (t : Point) c y < 0 := by
    intro y hy
    obtain ⟨hyP,hyD⟩ := Finset.mem_sdiff.mp hy
    by_contra hn
    exact hyD (Finset.mem_filter.mpr ⟨hyP,Or.inl (le_of_not_gt hn)⟩)
  have hout2 : ∀ y ∈ hullVertices P \ D, orient d (u : Point) y < 0 := by
    intro y hy
    obtain ⟨hyP,hyD⟩ := Finset.mem_sdiff.mp hy
    by_contra hn
    exact hyD (Finset.mem_filter.mpr ⟨hyP,Or.inr (Or.inr (le_of_not_gt hn))⟩)
  have hrep := replacement_card_lt P T D hgp hmin hTP
    (by exact ⟨t,by simp [T]⟩)
    (Finset.disjoint_left.mpr (by intro y hy hyH; exact (Finset.mem_sdiff.mp (hTI hy)).2 hyH))
    (Finset.filter_subset _ _) (by
      intro y hy
      have hy' : (y = (t : Point) ∨ y = c) ∨ (y = d ∨ y = (u : Point)) := by
        simp only [T,Finset.mem_insert,Finset.mem_singleton] at hy
        tauto
      rcases hy' with h | h
      · exact ⟨t,by simp [T],c,by simp [T],htc,h,hside1,hout1⟩
      · exact ⟨d,by simp [T],u,by simp [T],hdu',h,hside2,hout2⟩)
  let KL := matchChannel P t l c z
  let KF := outerFan P z (l,s)
  let KR := matchChannel P s u z d
  have hL : KL.card ≤ 1 := boundary_match_channel_le_one P hgp hno t l c z htl hcz hct hcl
  have hR : KR.card ≤ 1 := boundary_match_channel_le_one P hgp hno s u z d hsu hzd hds hdu
  have hF : KF.card ≤ 2 := outerFan_card_le_two P hgp hno z
    (Finset.mem_sdiff.mp hz).1 (l,s) hls
    (chain_inner2_ne_second hz l) (chain_inner2_ne_second hz s)
  have hcover : D ⊆ (KL ∪ KF) ∪ KR := by
    intro x hx
    obtain ⟨hxP,hvis⟩ := Finset.mem_filter.mp hx
    have strict : ∀ a ∈ inner P, ∀ b ∈ inner P, a ≠ b →
        0 ≤ orient a b x → 0 < orient a b x := by
      intro a ha b hb hab hn
      exact lt_of_le_of_ne hn (hgp a (Finset.mem_sdiff.mp ha).1
        b (Finset.mem_sdiff.mp hb).1 x (hullVertices_subset P hxP)
        hab (chain_inner_ne_outer ha hxP) (chain_inner_ne_outer hb hxP)).symm
    have hvis' : 0 < orient (t : Point) c x ∨ 0 < orient c d x ∨
        0 < orient d (u : Point) x := by
      rcases hvis with h | h | h
      · exact Or.inl (strict t htI c hcI htc h)
      · exact Or.inr (Or.inl (strict c hcI d hdI hcd h))
      · exact Or.inr (Or.inr (strict d hdI u huI hdu' h))
    have hh := ic_three_cell_exterior_cover P hgp t l s u c z d
      htl hls hsu hcz hzd htri hct hcl hds hdu ht hu x hxP hvis'
    rcases hh with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    · exact Finset.mem_union_right _ h
  have hDc := (Finset.card_le_card hcover).trans (Finset.card_union_le (KL ∪ KF) KR)
  have hLc := Finset.card_union_le KL KF
  omega

/-- If the right outside neighbor is on the near side of the chord c,d,
the actual right channel has capacity zero, by the already compiled glue. -/
theorem ic_right_channel_empty
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (s u : ChainVertex P) (c z d : Point)
    (hsu : BoundaryEdge (ChainSecond P) s u)
    (hcz : BoundaryEdge (ChainThird P) c z)
    (hzd : BoundaryEdge (ChainThird P) z d)
    (htri : orient c z d < 0)
    (hcs : orient c z s < 0)
    (hds : 0 < orient z d s) (hdu : 0 < orient z d u)
    (hchord : 0 < orient c d u) : matchChannel P s u z d = ∅ := by
  have hc := chain_third_mem_inner2 hcz.1
  have hz := chain_third_mem_inner2 hcz.2.1
  have hd := chain_third_mem_inner2 hzd.2.1
  have hgI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hsz : orient (s : Point) u z < 0 := by
    have hh := boundaryEdge_inner_strict (inner P) hgI z hz s u hsu
    rwa [orient_rotate z s u] at hh
  have hsd : orient (s : Point) u d < 0 := by
    have hh := boundaryEdge_inner_strict (inner P) hgI d hd s u hsu
    rwa [orient_rotate d s u] at hh
  have hcu : orient c z u < 0 := by
    have he : orient c z d * orient (s : Point) u z =
        orient c z s * orient z d u - orient c z u * orient z d s := by
      unfold orient; ring
    have h1 := mul_pos_of_neg_of_neg htri hsz
    have h2 := mul_neg_of_neg_of_pos hcs hdu
    by_contra hn
    have h3 := mul_nonneg (le_of_not_gt hn) hds.le
    nlinarith
  have hcds : 0 < orient c d s := by
    have he : orient c z d * orient (s : Point) u d =
        orient c d s * orient z d u - orient c d u * orient z d s := by
      unfold orient; ring
    have h1 := mul_pos_of_neg_of_neg htri hsd
    have h2 := mul_pos hchord hds
    by_contra hn
    have h3 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hdu.le
    nlinarith
  have hfu : InFan c z d s := by
    constructor
    · rw [orient_reverse]; linarith
    · exact hcds
  have hfv : InFan c z d u := by
    constructor
    · rw [orient_reverse]; linarith
    · exact hchord
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxP,hxC⟩ := Finset.mem_filter.mp hx
  apply hno
  apply hasEmptySix_of_one_point_double_sector P hgp s u z d c x
    hsu hzd hc _ hfu hfv hxP hxC
  rwa [← orient_rotate c z d]

/-- The reflected near-chord alternative empties the genuine LEFT channel.
It is proved directly, without assuming that the reversed right run exists. -/
theorem ic_left_channel_empty
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (t l : ChainVertex P) (c z d : Point)
    (htl : BoundaryEdge (ChainSecond P) t l)
    (hcz : BoundaryEdge (ChainThird P) c z)
    (hzd : BoundaryEdge (ChainThird P) z d)
    (htri : orient c z d < 0)
    (hct : 0 < orient c z t) (hcl : 0 < orient c z l)
    (hdl : orient z d l < 0)
    (hchord : 0 < orient c d t) : matchChannel P t l c z = ∅ := by
  have hc := chain_third_mem_inner2 hcz.1
  have hz := chain_third_mem_inner2 hcz.2.1
  have hd := chain_third_mem_inner2 hzd.2.1
  have hgI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have htc : orient (t : Point) l c < 0 := by
    have hh := boundaryEdge_inner_strict (inner P) hgI c hc t l htl
    rwa [orient_rotate c t l] at hh
  have htz : orient (t : Point) l z < 0 := by
    have hh := boundaryEdge_inner_strict (inner P) hgI z hz t l htl
    rwa [orient_rotate z t l] at hh
  have hcdl : 0 < orient c d l := by
    have he : orient c z d * orient (t : Point) l c =
        orient c z t * orient c d l - orient c z l * orient c d t := by
      unfold orient; ring
    have h1 := mul_pos_of_neg_of_neg htri htc
    have h2 := mul_pos hcl hchord
    by_contra hn
    have h3 := mul_nonpos_of_nonneg_of_nonpos hct.le (le_of_not_gt hn)
    nlinarith
  have hdt : orient z d t < 0 := by
    have he : orient c z d * orient (t : Point) l z =
        orient c z t * orient z d l - orient c z l * orient z d t := by
      unfold orient; ring
    have h1 := mul_pos_of_neg_of_neg htri htz
    have h2 := mul_neg_of_pos_of_neg hct hdl
    by_contra hn
    have h3 := mul_nonneg hcl.le (le_of_not_gt hn)
    nlinarith
  have hft : InFan d c z t := by
    constructor
    · exact hchord
    · rw [orient_reverse]; linarith
  have hfl : InFan d c z l := by
    constructor
    · exact hcdl
    · rw [orient_reverse]; linarith
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxP,hxC⟩ := Finset.mem_filter.mp hx
  exact hno (hasEmptySix_of_one_point_double_sector P hgp t l c z d x
    htl hcz hd htri hft hfl hxP hxC)

end JSP198.Nicolas
