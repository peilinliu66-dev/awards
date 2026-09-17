/-
Released under the MIT license.
Nicolas Theorem 3 from actual layer geometry, and actual left/right matching.
Mathematics: C. M. Nicolas (2007). See attribution in README.md.
No geometric covering principle or matching-existence statement is assumed.
-/
import Mathlib
import JSP198NicolasGlobal

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

/-! ## A finite linearly ordered view from an outer extreme point -/

lemma orient_pos_trans_from_hull_vertex
    (P : Finset Point) (hgp : GeneralPosition P)
    (o a b c : Point) (ho : o ∈ hullVertices P)
    (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P)
    (hab : 0 < orient o a b) (hbc : 0 < orient o b c) :
    0 < orient o a c := by
  have hoP := hullVertices_subset P ho
  have hoa : o ≠ a := by rintro rfl; simp [orient, mul_comm] at hab
  have hob : o ≠ b := by rintro rfl; simp [orient, mul_comm] at hab
  have hoc : o ≠ c := by rintro rfl; simp [orient, mul_comm] at hbc
  have hac : a ≠ c := by
    intro he
    subst c
    have hh : orient o b a = -orient o a b := by unfold orient; ring
    rw [hh] at hbc
    linarith
  by_contra hn
  have hneg : orient o a c < 0 :=
    lt_of_le_of_ne (le_of_not_gt hn) (hgp o hoP a ha c hc hoa hoc hac)
  have h1 : 0 < orient a b o := by rw [← orient_rotate o a b]; exact hab
  have h2 : 0 < orient b c o := by rw [← orient_rotate o b c]; exact hbc
  have h3 : 0 < orient c a o := by
    have hh : orient c a o = -orient o a c := by unfold orient; ring
    rw [hh]; linarith
  have hsum : orient a b c = orient a b o + orient b c o + orient c a o := by
    unfold orient; ring
  have hinside := mem_interior_triangle_of_orient_pos a b c o (by linarith) h1 h2 h3
  apply hull_vertex_not_mem_hull_sdiff
    (show (P : Set Point) ⊆ convexHull ℝ (P : Set Point) from subset_convexHull ℝ _) ho
  apply convexHull_mono _ (interior_subset hinside)
  intro z hz
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact ⟨ha,hoa.symm⟩
  · exact ⟨hb,hob.symm⟩
  · exact ⟨hc,hoc.symm⟩

lemma outer_leftOfAt_card_lt
    (P : Finset Point) (hgp : GeneralPosition P)
    (o a b : Point) (ho : o ∈ hullVertices P) (ha : a ∈ P) (hb : b ∈ P)
    (hab : 0 < orient o a b) :
    (leftOfAt P o b).card < (leftOfAt P o a).card := by
  have hbo : b ≠ o := by rintro rfl; simp [orient, mul_comm] at hab
  have hbL : b ∈ leftOfAt P o a :=
    Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hbo,hb⟩,hab⟩
  have hsub : leftOfAt P o b ⊆ (leftOfAt P o a).erase b := by
    intro c hc
    obtain ⟨hcP,hbc⟩ := Finset.mem_filter.mp hc
    have hcb : c ≠ b := by rintro rfl; simp [orient, mul_comm] at hbc
    refine Finset.mem_erase.mpr ⟨hcb,Finset.mem_filter.mpr ⟨hcP,?_⟩⟩
    exact orient_pos_trans_from_hull_vertex P hgp o a b c ho ha hb
      (Finset.mem_erase.mp hcP).2 hab hbc
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hbL] at hcard
  have hpos := Finset.card_pos.mpr ⟨b,hbL⟩
  omega

def viewRank (P : Finset Point) (o a : Point) : ℕ :=
  P.card - (leftOfAt P o a).card

lemma outer_viewRank_lt
    (P : Finset Point) (hgp : GeneralPosition P)
    (o a b : Point) (ho : o ∈ hullVertices P) (ha : a ∈ P) (hb : b ∈ P)
    (hab : 0 < orient o a b) : viewRank P o a < viewRank P o b := by
  have hh := outer_leftOfAt_card_lt P hgp o a b ho ha hb hab
  have haC : (leftOfAt P o a).card ≤ P.card :=
    Finset.card_le_card ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _))
  have hbC : (leftOfAt P o b).card ≤ P.card :=
    Finset.card_le_card ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _))
  unfold viewRank
  omega

lemma outer_viewRank_lt_iff
    (P : Finset Point) (hgp : GeneralPosition P)
    (o a b : Point) (ho : o ∈ hullVertices P) (ha : a ∈ P) (hb : b ∈ P)
    (hao : a ≠ o) (hbo : b ≠ o) :
    viewRank P o a < viewRank P o b ↔ 0 < orient o a b := by
  constructor
  · intro hlt
    by_cases hab : a = b
    · subst b; exact (Nat.lt_irrefl _ hlt).elim
    have hn := hgp o (hullVertices_subset P ho) a ha b hb hao.symm hbo.symm hab
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · have hrev : 0 < orient o b a := by
        have hh : orient o b a = -orient o a b := by unfold orient; ring
        rw [hh]; linarith
      have hr := outer_viewRank_lt P hgp o b a ho hb ha hrev
      omega
    · exact hpos
  · exact outer_viewRank_lt P hgp o a b ho ha hb

lemma outer_viewRank_ne
    (P : Finset Point) (hgp : GeneralPosition P)
    (o a b : Point) (ho : o ∈ hullVertices P) (ha : a ∈ P) (hb : b ∈ P)
    (hao : a ≠ o) (hbo : b ≠ o) (hab : a ≠ b) :
    viewRank P o a ≠ viewRank P o b := by
  have hn := hgp o (hullVertices_subset P ho) a ha b hb hao.symm hbo.symm hab
  rcases lt_or_gt_of_ne hn with hn | hn
  · have hrev : 0 < orient o b a := by
      have hh : orient o b a = -orient o a b := by unfold orient; ring
      rw [hh]; linarith
    exact (ne_of_gt (outer_viewRank_lt P hgp o b a ho hb ha hrev))
  · exact ne_of_lt (outer_viewRank_lt P hgp o a b ho ha hb hn)

/-- An actual triangle constrains the viewing rank of every distinct point in it. -/
lemma viewRank_triangle_bounds
    (P : Finset Point) (hgp : GeneralPosition P)
    (o u v w z : Point) (ho : o ∈ hullVertices P)
    (hu : u ∈ P) (hv : v ∈ P) (hw : w ∈ P) (hz : z ∈ P)
    (huo : u ≠ o) (hvo : v ≠ o) (hwo : w ≠ o) (hzo : z ≠ o)
    (hzu : z ≠ u) (hzv : z ≠ v) (hzw : z ≠ w)
    (hzh : z ∈ convexHull ℝ ({u,v,w} : Set Point)) :
    min (viewRank P o u) (min (viewRank P o v) (viewRank P o w)) < viewRank P o z ∧
    viewRank P o z < max (viewRank P o u) (max (viewRank P o v) (viewRank P o w)) := by
  have hru := outer_viewRank_ne P hgp o z u ho hz hu hzo huo hzu
  have hrv := outer_viewRank_ne P hgp o z v ho hz hv hzo hvo hzv
  have hrw := outer_viewRank_ne P hgp o z w ho hz hw hzo hwo hzw
  constructor
  · by_contra hn
    have h1 : viewRank P o z < viewRank P o u := by omega
    have h2 : viewRank P o z < viewRank P o v := by omega
    have h3 : viewRank P o z < viewRank P o w := by omega
    have a := (outer_viewRank_lt_iff P hgp o z u ho hz hu hzo huo).mp h1
    have b := (outer_viewRank_lt_iff P hgp o z v ho hz hv hzo hvo).mp h2
    have c := (outer_viewRank_lt_iff P hgp o z w ho hz hw hzo hwo).mp h3
    have hsub : convexHull ℝ ({u,v,w} : Set Point) ⊆ {y | 0 < orient o z y} := by
      apply convexHull_min _ (convex_strict_orient o z)
      intro y hy
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    have hh := hsub hzh
    simp [orient, mul_comm] at hh
  · by_contra hn
    have h1 : viewRank P o u < viewRank P o z := by omega
    have h2 : viewRank P o v < viewRank P o z := by omega
    have h3 : viewRank P o w < viewRank P o z := by omega
    have a : 0 < orient z o u := by
      rw [orient_rotate z o u]
      exact (outer_viewRank_lt_iff P hgp o u z ho hu hz huo hzo).mp h1
    have b : 0 < orient z o v := by
      have hh : orient z o v = orient o v z := by unfold orient; ring
      rw [hh]
      exact (outer_viewRank_lt_iff P hgp o v z ho hv hz hvo hzo).mp h2
    have c : 0 < orient z o w := by
      have hh : orient z o w = orient o w z := by unfold orient; ring
      rw [hh]
      exact (outer_viewRank_lt_iff P hgp o w z ho hw hz hwo hzo).mp h3
    have hsub : convexHull ℝ ({u,v,w} : Set Point) ⊆ {y | 0 < orient z o y} := by
      apply convexHull_min _ (convex_strict_orient z o)
      intro y hy
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    have hh := hsub hzh
    simp [orient, mul_comm] at hh

/-- Positive affine dependence forces overlapping rank intervals. This is a
finite-order form of diagonal intersection, derived by evaluating a line. -/
lemma viewRank_overlap_of_balance
    (P : Finset Point) (hgp : GeneralPosition P)
    (o a b c d : Point) (ho : o ∈ hullVertices P)
    (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (hd : d ∈ P)
    (hao : a ≠ o) (hbo : b ≠ o) (hco : c ≠ o) (hdo : d ≠ o)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (A B C D : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hbal : ∀ z : Point,
      A * orient o z a + B * orient o z b =
      C * orient o z c + D * orient o z d) :
    min (viewRank P o c) (viewRank P o d) <
      max (viewRank P o a) (viewRank P o b) := by
  by_contra hn
  have nac := outer_viewRank_ne P hgp o a c ho ha hc hao hco hac
  have nad := outer_viewRank_ne P hgp o a d ho ha hd hao hdo had
  have nbc := outer_viewRank_ne P hgp o b c ho hb hc hbo hco hbc
  have nbd := outer_viewRank_ne P hgp o b d ho hb hd hbo hdo hbd
  have ncd := outer_viewRank_ne P hgp o c d ho hc hd hco hdo hcd
  by_cases hcle : viewRank P o c ≤ viewRank P o d
  · have h1 : 0 < orient o a c :=
      (outer_viewRank_lt_iff P hgp o a c ho ha hc hao hco).mp (by omega)
    have h2 : 0 < orient o b c :=
      (outer_viewRank_lt_iff P hgp o b c ho hb hc hbo hco).mp (by omega)
    have h3 : 0 < orient o c d :=
      (outer_viewRank_lt_iff P hgp o c d ho hc hd hco hdo).mp (by omega)
    have s1 : orient o c a = -orient o a c := by unfold orient; ring
    have s2 : orient o c b = -orient o b c := by unfold orient; ring
    have hEq := hbal c
    rw [s1,s2] at hEq
    have zc : orient o c c = 0 := by unfold orient; ring
    rw [zc,mul_zero,zero_add] at hEq
    have p1 := mul_pos hA h1
    have p2 := mul_pos hB h2
    have p3 := mul_pos hD h3
    nlinarith
  · have h1 : 0 < orient o a d :=
      (outer_viewRank_lt_iff P hgp o a d ho ha hd hao hdo).mp (by omega)
    have h2 : 0 < orient o b d :=
      (outer_viewRank_lt_iff P hgp o b d ho hb hd hbo hdo).mp (by omega)
    have h3 : 0 < orient o d c :=
      (outer_viewRank_lt_iff P hgp o d c ho hd hc hdo hco).mp (by omega)
    have s1 : orient o d a = -orient o a d := by unfold orient; ring
    have s2 : orient o d b = -orient o b d := by unfold orient; ring
    have hEq := hbal d
    rw [s1,s2] at hEq
    have zd : orient o d d = 0 := by unfold orient; ring
    rw [zd,mul_zero,add_zero] at hEq
    have p1 := mul_pos hA h1
    have p2 := mul_pos hB h2
    have p3 := mul_pos hC h3
    nlinarith

/-- Diagonal balance for the clockwise quadrilateral u,c,d,w. -/
lemma diagonal_balance (o z u c d w : Point) :
    (-orient c d w) * orient o z u + (-orient u c w) * orient o z d =
    (-orient u d w) * orient o z c + (-orient u c d) * orient o z w := by
  unfold orient
  ring

/-- A small ordered-set fact, with no geometric condition hidden in it. -/
lemma ear_cover_order (r s t p q : ℕ)
    (hpL : min r (min s t) < p) (hpU : p < max r (max s t))
    (hqL : min r (min s t) < q) (hqU : q < max r (max s t))
    (hcross1 : min p t < max r q) (hcross2 : min r q < max p t)
    (hvis : r < p ∨ p < q ∨ q < t) :
    (r < p ∧ p < s) ∨ (s < q ∧ q < t) := by
  omega

/-- The exterior two-cone cover in Nicolas Theorem 3, proved from actual
triangle containments and actual quadrilateral orientation signs. -/
theorem ear_exterior_cover
    (P : Finset Point) (hgp : GeneralPosition P)
    (o u v w c d : Point) (ho : o ∈ hullVertices P)
    (hu : u ∈ inner P) (hv : v ∈ inner P) (hw : w ∈ inner P)
    (hc : c ∈ inner P) (hd : d ∈ inner P)
    (hcu : c ≠ u) (hcv : c ≠ v) (hcw : c ≠ w)
    (hdu : d ≠ u) (hdv : d ≠ v) (hdw : d ≠ w)
    (hcH : c ∈ convexHull ℝ ({u,v,w} : Set Point))
    (hdH : d ∈ convexHull ℝ ({u,v,w} : Set Point))
    (h1 : orient u c d < 0) (h2 : orient u c w < 0)
    (h3 : orient u d w < 0) (h4 : orient c d w < 0)
    (hvis : 0 < orient u c o ∨ 0 < orient c d o ∨ 0 < orient d w o) :
    InFan c u v o ∨ InFan d v w o := by
  have huP := (Finset.mem_sdiff.mp hu).1
  have hvP := (Finset.mem_sdiff.mp hv).1
  have hwP := (Finset.mem_sdiff.mp hw).1
  have hcP := (Finset.mem_sdiff.mp hc).1
  have hdP := (Finset.mem_sdiff.mp hd).1
  have huu : u ≠ o := fun he => (Finset.mem_sdiff.mp hu).2 (by simpa only [he] using ho)
  have hvv : v ≠ o := fun he => (Finset.mem_sdiff.mp hv).2 (by simpa only [he] using ho)
  have hww : w ≠ o := fun he => (Finset.mem_sdiff.mp hw).2 (by simpa only [he] using ho)
  have hcc : c ≠ o := fun he => (Finset.mem_sdiff.mp hc).2 (by simpa only [he] using ho)
  have hdd : d ≠ o := fun he => (Finset.mem_sdiff.mp hd).2 (by simpa only [he] using ho)
  have huw : u ≠ w := by rintro rfl; simp [orient, mul_comm] at h2
  have hcd : c ≠ d := by rintro rfl; simp [orient, mul_comm] at h1
  obtain ⟨cL,cU⟩ := viewRank_triangle_bounds P hgp o u v w c ho huP hvP hwP hcP
    huu hvv hww hcc hcu hcv hcw hcH
  obtain ⟨dL,dU⟩ := viewRank_triangle_bounds P hgp o u v w d ho huP hvP hwP hdP
    huu hvv hww hdd hdu hdv hdw hdH
  have e1 := viewRank_overlap_of_balance P hgp o u d c w ho huP hdP hcP hwP
    huu hdd hcc hww hcu.symm huw hcd.symm hdw hcw
    (-orient c d w) (-orient u c w) (-orient u d w) (-orient u c d)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (fun z => diagonal_balance o z u c d w)
  have e2 := viewRank_overlap_of_balance P hgp o c w u d ho hcP hwP huP hdP
    hcc hww huu hdd hcu hcd huw.symm hdw.symm hdu.symm
    (-orient u d w) (-orient u c d) (-orient c d w) (-orient u c w)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (fun z => (diagonal_balance o z u c d w).symm)
  have hview : viewRank P o u < viewRank P o c ∨
      viewRank P o c < viewRank P o d ∨ viewRank P o d < viewRank P o w := by
    rcases hvis with h | h | h
    · apply Or.inl
      apply outer_viewRank_lt P hgp o u c ho huP hcP
      rw [orient_rotate o u c]
      exact h
    · apply Or.inr; apply Or.inl
      apply outer_viewRank_lt P hgp o c d ho hcP hdP
      rw [orient_rotate o c d]
      exact h
    · apply Or.inr; apply Or.inr
      apply outer_viewRank_lt P hgp o d w ho hdP hwP
      rw [orient_rotate o d w]
      exact h
  have hh := ear_cover_order (viewRank P o u) (viewRank P o v) (viewRank P o w)
    (viewRank P o c) (viewRank P o d) cL cU dL dU e1 e2 hview
  rcases hh with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · left
    refine ⟨?_,?_⟩
    · rw [← orient_rotate o u c]
      exact (outer_viewRank_lt_iff P hgp o u c ho huP hcP huu hcc).mp ha
    · rw [← orient_rotate o c v]
      exact (outer_viewRank_lt_iff P hgp o c v ho hcP hvP hcc hvv).mp hb
  · right
    refine ⟨?_,?_⟩
    · rw [← orient_rotate o v d]
      exact (outer_viewRank_lt_iff P hgp o v d ho hvP hdP hvv hdd).mp ha
    · rw [← orient_rotate o d w]
      exact (outer_viewRank_lt_iff P hgp o d w ho hdP hwP hdd hww).mp hb

/-! ## The geometric ear cut out by an isolating line -/

lemma point_on_isolating_line_in_ear
    (u v w a b z : Point)
    (hbase : orient u v w < 0)
    (hz1 : orient u v z < 0) (hz2 : orient v w z < 0)
    (hV : 0 < orient a b v) (hU : orient a b u < 0)
    (hW : orient a b w < 0) (hz0 : orient a b z = 0) :
    z ∈ convexHull ℝ ({u,v,w} : Set Point) ∧ orient u z w < 0 := by
  have hD : 0 < orient v u w := by rw [orient_reverse]; linarith
  let B := orient v z w / orient v u w
  let C := orient v u z / orient v u w
  let A := 1 - B - C
  have hB : 0 < B := by
    apply div_pos _ hD
    have he : orient v z w = -orient v w z := by unfold orient; ring
    rw [he]; linarith
  have hC : 0 < C := by
    apply div_pos _ hD
    rw [orient_reverse]; linarith
  have hsum : A+B+C=1 := by dsimp [A]; ring
  have hrep : z = A • v + B • u + C • w := corner_affine v u w z (ne_of_gt hD)
  have hEval : orient a b z = A * orient a b v + B * orient a b u + C * orient a b w := by
    rw [hrep,orient_affine_comb a b v u w A B C hsum]
  have hA : 0 < A := by
    by_contra hn
    have p1 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hV.le
    have p2 := mul_neg_of_pos_of_neg hB hU
    have p3 := mul_neg_of_pos_of_neg hC hW
    rw [hz0] at hEval
    linarith
  constructor
  · have hh := mem_triangle_of_weights v u w A B C hA.le hB.le hC.le hsum
    rw [← hrep] at hh
    apply convexHull_mono _ hh
    intro y hy
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hy ⊢
    tauto
  · have he : orient u z w = A * orient u v w := by
      rw [orient_rotate u z w,orient_rotate z w u,hrep,orient_affine_comb w u v u w A B C hsum]
      have h1 : orient w u u = 0 := by unfold orient; ring
      have h2 : orient w u w = 0 := by unfold orient; ring
      rw [h1,h2,mul_zero,mul_zero,add_zero,add_zero]
      rw [orient_rotate w u v]
    rw [he]
    exact mul_neg_of_pos_of_neg hA hbase

/-- A layer-three supporting line must see at least one layer-two vertex. -/
lemma third_edge_cap_nonempty
    (P : Finset Point) (hgp : GeneralPosition P) (c d : Point)
    (hcd : BoundaryEdge (hullVertices (inner (inner P))) c d) :
    ((hullVertices (inner P)).filter (fun x => 0 < orient c d x)).Nonempty := by
  let Q := hullVertices (inner P)
  have hcII := hullVertices_subset (inner (inner P)) hcd.1
  have hdII := hullVertices_subset (inner (inner P)) hcd.2.1
  have hcI := (Finset.mem_sdiff.mp hcII).1
  have hdI := (Finset.mem_sdiff.mp hdII).1
  have hcP := (Finset.mem_sdiff.mp hcI).1
  have hdP := (Finset.mem_sdiff.mp hdI).1
  have hneq : ∀ x ∈ Q, orient c d x ≠ 0 := by
    intro x hx
    have hxI := hullVertices_subset (inner P) hx
    have hcx : c ≠ x := fun he => (Finset.mem_sdiff.mp hcII).2 (by simpa only [he] using hx)
    have hdx : d ≠ x := fun he => (Finset.mem_sdiff.mp hdII).2 (by simpa only [he] using hx)
    exact hgp c hcP d hdP x (Finset.mem_sdiff.mp hxI).1 hcd.2.2.1 hcx hdx
  by_contra hn
  have hneg : ∀ x ∈ Q, orient c d x < 0 := by
    intro x hx
    have hle : orient c d x ≤ 0 := by
      by_contra hh
      exact hn ⟨x,Finset.mem_filter.mpr ⟨hx,lt_of_not_ge hh⟩⟩
    exact lt_of_le_of_ne hle (hneq x hx)
  have hsub : convexHull ℝ (Q : Set Point) ⊆ {x | 0 < orient d c x} := by
    apply convexHull_min _ (convex_strict_orient d c)
    intro x hx
    change 0 < orient d c x
    rw [orient_reverse]
    exact neg_pos.mpr (hneg x hx)
  have hcH : c ∈ convexHull ℝ (Q : Set Point) := by
    dsimp [Q]
    rw [convexHull_hullVertices]
    exact subset_convexHull ℝ _ hcI
  have hh := hsub hcH
  simp [orient, mul_comm] at hh


/-- Nicolas Theorem 3. The cap lower bound is derived from the real layers,
minimality, and the proved two-cone cover. It is not a matching hypothesis. -/
theorem third_edge_cap_card_ge_two
    (P : Finset Point) (hgp : GeneralPosition P)
    (hmin : MinimalOuter P) (hno : ¬HasEmptySix P)
    (c d : Point) (hcd : BoundaryEdge (hullVertices (inner (inner P))) c d) :
    2 ≤ ((hullVertices (inner P)).filter (fun x => 0 < orient c d x)).card := by
  let R := hullVertices (inner P)
  let C := R.filter (fun x => 0 < orient c d x)
  have hRgp : GeneralPosition R :=
    gp_subset hgp ((hullVertices_subset (inner P)).trans Finset.sdiff_subset)
  have hRc : InConvexPosition R := convexIndependent_hullVertices (inner P)
  have hcII := hullVertices_subset (inner (inner P)) hcd.1
  have hdII := hullVertices_subset (inner (inner P)) hcd.2.1
  have hcI := (Finset.mem_sdiff.mp hcII).1
  have hdI := (Finset.mem_sdiff.mp hdII).1
  have hcP := (Finset.mem_sdiff.mp hcI).1
  have hdP := (Finset.mem_sdiff.mp hdI).1
  have hR3 : 3 ≤ R.card :=
    three_le_hull_of_inner_nonempty (inner P)
      (gp_subset hgp Finset.sdiff_subset) ⟨c,hcII⟩
  have hne := third_edge_cap_nonempty P hgp c d hcd
  change C.Nonempty at hne
  by_contra hn
  have hC1 : C.card ≤ 1 := by change ¬ 2 ≤ C.card at hn; omega
  obtain ⟨v,hvC⟩ := hne
  obtain ⟨hvR,hvPos⟩ := Finset.mem_filter.mp hvC
  have hsingle : ∀ y ∈ C, y = v := fun y hy => Finset.card_le_one.mp hC1 y hy v hvC
  obtain ⟨u,huv⟩ := exists_boundaryEdge_to R hRc hRgp (by omega) v hvR
  obtain ⟨w,hvw⟩ := exists_boundaryEdge_from R hRc hRgp (by omega) v hvR
  have huw := boundary_neighbors_ne R hRgp hR3 u v w huv hvw
  have huI := hullVertices_subset (inner P) huv.1
  have hvI := hullVertices_subset (inner P) hvR
  have hwI := hullVertices_subset (inner P) hvw.2.1
  have huP := (Finset.mem_sdiff.mp huI).1
  have hvP := (Finset.mem_sdiff.mp hvI).1
  have hwP := (Finset.mem_sdiff.mp hwI).1
  have haway : ∀ z ∈ R, c ≠ z ∧ d ≠ z := by
    intro z hz
    constructor
    · intro he
      exact (Finset.mem_sdiff.mp hcII).2 (by simpa only [he] using hz)
    · intro he
      exact (Finset.mem_sdiff.mp hdII).2 (by simpa only [he] using hz)
  have hneg : ∀ z ∈ R, z ≠ v → orient c d z < 0 := by
    intro z hz hzv
    have hle : orient c d z ≤ 0 := by
      by_contra hp
      exact hzv (hsingle z (Finset.mem_filter.mpr ⟨hz,lt_of_not_ge hp⟩))
    have hnz := hgp c hcP d hdP z
      (Finset.mem_sdiff.mp (hullVertices_subset (inner P) hz)).1
      hcd.2.2.1 (haway z hz).1 (haway z hz).2
    exact lt_of_le_of_ne hle hnz
  have huNeg := hneg u huv.1 huv.2.2.1
  have hwNeg := hneg w hvw.2.1 hvw.2.2.1.symm
  have hbase := huv.strict hRgp hvw.2.1 huw.symm hvw.2.2.1.symm
  have hinner_uv : ∀ z ∈ inner P, orient u v z ≤ 0 := boundaryEdge_hull_support huv
  have hinner_vw : ∀ z ∈ inner P, orient v w z ≤ 0 := boundaryEdge_hull_support hvw
  have huc : orient u v c < 0 :=
    lt_of_le_of_ne (hinner_uv c hcI)
      (hgp u huP v hvP c hcP huv.2.2.1
        (haway u huv.1).1.symm (haway v hvR).1.symm)
  have hvc : orient v w c < 0 :=
    lt_of_le_of_ne (hinner_vw c hcI)
      (hgp v hvP w hwP c hcP hvw.2.2.1
        (haway v hvR).1.symm (haway w hvw.2.1).1.symm)
  have hud : orient u v d < 0 :=
    lt_of_le_of_ne (hinner_uv d hdI)
      (hgp u huP v hvP d hdP huv.2.2.1
        (haway u huv.1).2.symm (haway v hvR).2.symm)
  have hvd : orient v w d < 0 :=
    lt_of_le_of_ne (hinner_vw d hdI)
      (hgp v hvP w hwP d hdP hvw.2.2.1
        (haway v hvR).2.symm (haway w hvw.2.1).2.symm)
  obtain ⟨hcH,h2⟩ := point_on_isolating_line_in_ear u v w c d c hbase huc hvc
    hvPos huNeg hwNeg (by simp [orient, mul_comm])
  obtain ⟨hdH,h3⟩ := point_on_isolating_line_in_ear u v w c d d hbase hud hvd
    hvPos huNeg hwNeg (by simp [orient, mul_comm])
  have h1 : orient u c d < 0 := by rw [orient_rotate u c d]; exact huNeg
  have h4 : orient c d w < 0 := hwNeg
  let T : Finset Point := {u,c,d,w}
  let D : Finset Point := (hullVertices P).filter (fun x =>
    0 ≤ orient u c x ∨ 0 ≤ orient c d x ∨ 0 ≤ orient d w x)
  have hTsub : T ⊆ inner P := by
    intro z hz
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have hTP : T ⊆ P := hTsub.trans Finset.sdiff_subset
  have hTne : T.Nonempty := by exact ⟨u,by simp [T]⟩
  have hTdis : Disjoint T (hullVertices P) := by
    apply Finset.disjoint_left.mpr
    intro z hz hzH
    exact (Finset.mem_sdiff.mp (hTsub hz)).2 hzH
  have hDsub : D ⊆ hullVertices P := Finset.filter_subset _ _
  have hSides1 : ∀ z ∈ T, orient u c z ≤ 0 := by
    intro z hz
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · simp [orient, mul_comm]
    · simp [orient, mul_comm]
    · exact h1.le
    · exact h2.le
  have hSides2 : ∀ z ∈ T, orient d w z ≤ 0 := by
    intro z hz
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz | hz
    · subst z
      rw [orient_rotate d w u,orient_rotate w u d]
      exact h3.le
    · subst z
      rw [orient_rotate d w c,orient_rotate w c d]
      exact h4.le
    · subst z; simp [orient, mul_comm]
    · subst z; simp [orient, mul_comm]
  have hOut1 : ∀ z ∈ hullVertices P \ D, orient u c z < 0 := by
    intro z hz
    obtain ⟨hzH,hzD⟩ := Finset.mem_sdiff.mp hz
    apply lt_of_not_ge
    intro hle
    exact hzD (Finset.mem_filter.mpr ⟨hzH,Or.inl hle⟩)
  have hOut2 : ∀ z ∈ hullVertices P \ D, orient d w z < 0 := by
    intro z hz
    obtain ⟨hzH,hzD⟩ := Finset.mem_sdiff.mp hz
    apply lt_of_not_ge
    intro hle
    exact hzD (Finset.mem_filter.mpr ⟨hzH,Or.inr (Or.inr hle)⟩)
  have hreplace := replacement_card_lt P T D hgp hmin hTP hTne hTdis hDsub (by
    intro z hz
    have hcase : (z = u ∨ z = c) ∨ (z = d ∨ z = w) := by
      simp only [T,Finset.mem_insert,Finset.mem_singleton] at hz
      tauto
    rcases hcase with hc1 | hc2
    · exact ⟨u,by simp [T],c,by simp [T],(haway u huv.1).1.symm,
        hc1,hSides1,hOut1⟩
    · exact ⟨d,by simp [T],w,by simp [T],(haway w hvw.2.1).2,
        hc2,hSides2,hOut2⟩)
  have hT4 : T.card = 4 := by
    simp [T,(haway u huv.1).1.symm,(haway u huv.1).2.symm,huw,
      hcd.2.2.1,(haway w hvw.2.1).1,(haway w hvw.2.1).2]
  have hD5 : 5 ≤ D.card := by omega
  let K1 := outerFan P c (u,v)
  let K2 := outerFan P d (v,w)
  have hK1 : K1.card ≤ 2 := outerFan_card_le_two P hgp hno c hcI (u,v) huv
    (haway u huv.1).1 (haway v hvR).1
  have hK2 : K2.card ≤ 2 := outerFan_card_le_two P hgp hno d hdI (v,w) hvw
    (haway v hvR).2 (haway w hvw.2.1).2
  have hgenOut : ∀ a ∈ inner P, ∀ b ∈ inner P, a ≠ b →
      ∀ x ∈ hullVertices P, orient a b x ≠ 0 := by
    intro a ha b hb hab x hx
    have hax : a ≠ x := fun he =>
      (Finset.mem_sdiff.mp ha).2 (by simpa only [he] using hx)
    have hbx : b ≠ x := fun he =>
      (Finset.mem_sdiff.mp hb).2 (by simpa only [he] using hx)
    exact hgp a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1
      x (hullVertices_subset P hx) hab hax hbx
  have hCover : D ⊆ K1 ∪ K2 := by
    intro x hx
    obtain ⟨hxH,hxvis⟩ := Finset.mem_filter.mp hx
    have hvis : 0 < orient u c x ∨ 0 < orient c d x ∨ 0 < orient d w x := by
      rcases hxvis with h | h | h
      · exact Or.inl (lt_of_le_of_ne h (hgenOut u huI c hcI
          (haway u huv.1).1.symm x hxH).symm)
      · exact Or.inr (Or.inl (lt_of_le_of_ne h
          (hgenOut c hcI d hdI hcd.2.2.1 x hxH).symm))
      · exact Or.inr (Or.inr (lt_of_le_of_ne h
          (hgenOut d hdI w hwI (haway w hvw.2.1).2 x hxH).symm))
    have hh := ear_exterior_cover P hgp x u v w c d hxH huI hvI hwI hcI hdI
      (haway u huv.1).1 (haway v hvR).1 (haway w hvw.2.1).1
      (haway u huv.1).2 (haway v hvR).2 (haway w hvw.2.1).2
      hcH hdH h1 h2 h3 h4 hvis
    rcases hh with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxH,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxH,h⟩)
  have hDc := (Finset.card_le_card hCover).trans (Finset.card_union_le K1 K2)
  omega

/-- Theorem 3 in its unconditional disjunctive form. -/
theorem nicolas_theorem3
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P) :
    HasEmptySix P ∨
    ∀ c d : Point, BoundaryEdge (hullVertices (inner (inner P))) c d →
      2 ≤ ((hullVertices (inner P)).filter (fun x => 0 < orient c d x)).card := by
  by_cases h : HasEmptySix P
  · exact Or.inl h
  · exact Or.inr (fun c d he => third_edge_cap_card_ge_two P hgp hmin h c d he)

/-- Every actual sector vertex has a genuine left or right match. Each returned
quadrilateral is proved empty in the original point set, and each channel has
capacity at most one. No matching-existence assumption is present. -/
theorem actual_sector_match_exists
    (P : Finset Point) (hgp : GeneralPosition P)
    (hmin : MinimalOuter P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (r : ((hullVertices (inner P) : Finset Point) : Set Point)) :
    let c := (sectorEdge P hgp o ho r).val.1
    let d := (sectorEdge P hgp o ho r).val.2
    ∃ u w : Point,
      BoundaryEdge (hullVertices (inner P)) u r ∧
      BoundaryEdge (hullVertices (inner P)) r w ∧
      ((0 < orient c d u ∧ EmptyConvexPolygon P ({u,c,d,(r : Point)} : Finset Point) ∧
        (matchChannel P u r c d).card ≤ 1) ∨
       (0 < orient c d w ∧ EmptyConvexPolygon P ({(r : Point),c,d,w} : Finset Point) ∧
        (matchChannel P r w c d).card ≤ 1)) := by
  dsimp only
  let e := sectorEdge P hgp o ho r
  have he := mem_boundaryEdges.mp e.property
  have hrpos := sectorEdge_outward P hgp o ho r
  have hRgp := gp_subset hgp ((hullVertices_subset (inner P)).trans Finset.sdiff_subset)
  have hR3 : 3 ≤ (hullVertices (inner P)).card :=
    three_le_hull_of_inner_nonempty (inner P) (gp_subset hgp Finset.sdiff_subset)
      ⟨o,(Finset.mem_sdiff.mp ho).1⟩
  have hcII := hullVertices_subset (inner (inner P)) he.1
  have hdII := hullVertices_subset (inner (inner P)) he.2.1
  have hcI := (Finset.mem_sdiff.mp hcII).1
  have hdI := (Finset.mem_sdiff.mp hdII).1
  have hgen : ∀ z ∈ hullVertices (inner P), orient e.val.1 e.val.2 z ≠ 0 := by
    intro z hz
    have hcz : e.val.1 ≠ z := fun h =>
      (Finset.mem_sdiff.mp hcII).2 (by simpa only [h] using hz)
    have hdz : e.val.2 ≠ z := fun h =>
      (Finset.mem_sdiff.mp hdII).2 (by simpa only [h] using hz)
    exact hgp e.val.1 (Finset.mem_sdiff.mp hcI).1 e.val.2 (Finset.mem_sdiff.mp hdI).1
      z (Finset.mem_sdiff.mp (hullVertices_subset (inner P) hz)).1 he.2.2.1 hcz hdz
  obtain ⟨u,w,hur,hrw,hmatch⟩ := boundary_neighbor_in_cap
    (hullVertices (inner P)) (convexIndependent_hullVertices (inner P)) hRgp hR3
    e.val.1 e.val.2 r r.property hrpos hgen
    (third_edge_cap_card_ge_two P hgp hmin hno e.val.1 e.val.2 he)
  refine ⟨u,w,hur,hrw,?_⟩
  rcases hmatch with hu | hw
  · exact Or.inl ⟨hu,boundary_match_empty_quad P hgp u r e.val.1 e.val.2 hur he hu hrpos,
      boundary_match_channel_le_one P hgp hno u r e.val.1 e.val.2 hur he hu hrpos⟩
  · exact Or.inr ⟨hw,boundary_match_empty_quad P hgp r w e.val.1 e.val.2 hrw he hrpos hw,
      boundary_match_channel_le_one P hgp hno r w e.val.1 e.val.2 hrw he hrpos hw⟩

end JSP198.Nicolas

#print axioms JSP198.Nicolas.ear_exterior_cover
#print axioms JSP198.Nicolas.nicolas_theorem3
#print axioms JSP198.Nicolas.actual_sector_match_exists
