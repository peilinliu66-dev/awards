/-
Released under the MIT license.
One outer point in a double-sector channel yields an actual empty hexagon.
Mathematical route: Nicolas, The Empty Hexagon Theorem (2007).
-/
import JSP198NicolasGlobal

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

/-- The channel, together with its two sector vertices, forces the outer
point into the same sector. No additional convexity signs are assumed. -/
lemma channel_point_in_fan
    (c d w u v x : Point)
    (hw : orient c d w < 0)
    (hu : 0 < orient c d u) (hv : 0 < orient c d v)
    (hfu : InFan w c d u) (hfv : InFan w c d v)
    (hx : 0 < orient u c x ∧ 0 < orient c d x ∧ 0 < orient d v x) :
    InFan w c d x := by
  have hleft : orient c d u * orient c w x =
      orient c w u * orient c d x - orient c d w * orient u c x := by
    unfold orient
    ring
  have hright : orient c d v * orient w d x =
      orient w d v * orient c d x - orient c d w * orient d v x := by
    unfold orient
    ring
  constructor
  · have hp := mul_pos hfu.1 hx.2.1
    have hn := mul_neg_of_neg_of_pos hw hx.1
    by_contra h
    have hz := mul_nonpos_of_nonneg_of_nonpos hu.le (le_of_not_gt h)
    nlinarith
  · have hp := mul_pos hfv.2 hx.2.1
    have hn := mul_neg_of_neg_of_pos hw hx.2.2
    by_contra h
    have hz := mul_nonpos_of_nonneg_of_nonpos hv.le (le_of_not_gt h)
    nlinarith

/-- Glue an empty triangle to an empty annular quadrilateral, then the
actual outer channel point. The six supporting edges and ambient emptiness
are proved from the stated signs. -/
theorem empty_six_of_quad_triangle_channel
    (P : Finset Point) (hgp : GeneralPosition P)
    (u v c d z x : Point)
    (hu : u ∈ inner P) (hv : v ∈ inner P)
    (hc : c ∈ inner P) (hd : d ∈ inner P) (hz : z ∈ inner P)
    (hx : x ∈ hullVertices P)
    (hucd : 0 < orient u c d) (hucv : 0 < orient u c v)
    (hudv : 0 < orient u d v) (hcdv : 0 < orient c d v)
    (hzneg : orient c d z < 0)
    (hfu : InFan z c d u) (hfv : InFan z c d v)
    (hchannel : 0 < orient u c x ∧ 0 < orient c d x ∧ 0 < orient d v x)
    (hquad : EmptyConvexPolygon P {u,c,d,v})
    (htri : EmptyConvexPolygon P {c,z,d})
    (hinner : ∀ y ∈ inner P, orient u v y ≤ 0) : HasEmptySix P := by
  let A : Finset Point := {u,c,d,v}
  let Q : Finset Point := insert x (insert z A)
  have huP := (Finset.mem_sdiff.mp hu).1
  have hvP := (Finset.mem_sdiff.mp hv).1
  have hcP := (Finset.mem_sdiff.mp hc).1
  have hdP := (Finset.mem_sdiff.mp hd).1
  have hzP := (Finset.mem_sdiff.mp hz).1
  have hxP := hullVertices_subset P hx
  have hcdu : 0 < orient c d u := by rwa [← orient_rotate u c d]
  have hfx := channel_point_in_fan c d z u v x hzneg hcdu hcdv hfu hfv hchannel
  have hczd : 0 < orient c z d := by
    have he : orient c z d = -orient c d z := by unfold orient; ring
    rw [he]
    exact neg_pos.mpr hzneg
  have huc : u ≠ c := by intro h; subst c; simp [orient, mul_comm] at hucd
  have hud : u ≠ d := by intro h; subst d; rw [orient_refl_left] at hucd; linarith
  have huv : u ≠ v := by intro h; subst v; rw [orient_refl_left] at hucv; linarith
  have hcd : c ≠ d := by intro h; subst d; rw [orient_refl_right] at hucd; linarith
  have hcv : c ≠ v := by intro h; subst v; rw [orient_refl_right] at hucv; linarith
  have hdv : d ≠ v := by intro h; subst v; rw [orient_refl_right] at hcdv; linarith
  have hcz : c ≠ z := by intro h; subst z; rw [orient_refl_left] at hzneg; linarith
  have hzd : z ≠ d := by intro h; subst z; rw [orient_refl_right] at hzneg; linarith
  have hQP : Q ⊆ P := by
    intro y hy
    simp only [Q, A, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy | hy | hy <;> subst y <;> assumption
  have hQuc : ∀ y ∈ Q, 0 ≤ orient u c y := by
    intro y hy
    simp only [Q, A, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy | hy | hy <;> subst y
    · exact hchannel.1.le
    · rw [orient_rotate]
      exact hfu.1.le
    · simp [orient, mul_comm]
    · simp [orient, mul_comm]
    · exact hucd.le
    · exact hucv.le
  have hQcz : ∀ y ∈ Q, 0 ≤ orient c z y := by
    intro y hy
    simp only [Q, A, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy | hy | hy <;> subst y
    · exact hfx.1.le
    · simp [orient, mul_comm]
    · exact hfu.1.le
    · simp [orient, mul_comm]
    · exact hczd.le
    · exact hfv.1.le
  have hQzd : ∀ y ∈ Q, 0 ≤ orient z d y := by
    intro y hy
    simp only [Q, A, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy | hy | hy <;> subst y
    · exact hfx.2.le
    · simp [orient, mul_comm]
    · exact hfu.2.le
    · rw [← orient_rotate c z d]
      exact hczd.le
    · simp [orient, mul_comm]
    · exact hfv.2.le
  have hQdv : ∀ y ∈ Q, 0 ≤ orient d v y := by
    intro y hy
    simp only [Q, A, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy | hy | hy <;> subst y
    · exact hchannel.2.2.le
    · rw [← orient_rotate z d v]
      exact hfv.2.le
    · rw [← orient_rotate u d v]
      exact hudv.le
    · rw [← orient_rotate c d v]
      exact hcdv.le
    · simp [orient, mul_comm]
    · simp [orient, mul_comm]
  have hQC : InConvexPosition Q := by
    apply convex_position_outer_supported P Q hQP
    intro y hy hynot
    simp only [Q, A, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy | hy | hy <;> subst y
    · exact (hynot hx).elim
    · exact strictSupport_of_nonnegative_halfplane P Q hgp hQP c z z
        (by simp [Q,A]) (by simp [Q,A]) hcz (Or.inr rfl) hQcz
    · exact strictSupport_of_nonnegative_halfplane P Q hgp hQP u c u
        (by simp [Q,A]) (by simp [Q,A]) huc (Or.inl rfl) hQuc
    · exact strictSupport_of_nonnegative_halfplane P Q hgp hQP u c c
        (by simp [Q,A]) (by simp [Q,A]) huc (Or.inr rfl) hQuc
    · exact strictSupport_of_nonnegative_halfplane P Q hgp hQP z d d
        (by simp [Q,A]) (by simp [Q,A]) hzd (Or.inr rfl) hQzd
    · exact strictSupport_of_nonnegative_halfplane P Q hgp hQP d v v
        (by simp [Q,A]) (by simp [Q,A]) hdv (Or.inr rfl) hQdv
  have hQE : EmptyConvexPolygon P Q := by
    refine ⟨hQP,hQC,?_⟩
    intro y hyP hyQ hyint
    by_cases hyA : y ∈ hullVertices P
    · exact hull_vertex_not_mem_hull
        (fun a ha => subset_convexHull ℝ _ (hQP ha)) hyA hyQ (interior_subset hyint)
    have hyI : y ∈ inner P := Finset.mem_sdiff.mpr ⟨hyP,hyA⟩
    have hyu : y ≠ u := by intro h; exact hyQ (by simp [Q,A,h])
    have hyc : y ≠ c := by intro h; exact hyQ (by simp [Q,A,h])
    have hyd : y ≠ d := by intro h; exact hyQ (by simp [Q,A,h])
    have hyv : y ≠ v := by intro h; exact hyQ (by simp [Q,A,h])
    have h1 : 0 < orient u c y := by
      by_contra hn
      exact not_mem_interior_convexHull_of_halfplane Q u c y huc hQuc
        (not_lt.mp hn) hyint
    have h2 : 0 < orient c z y := by
      by_contra hn
      exact not_mem_interior_convexHull_of_halfplane Q c z y hcz hQcz
        (not_lt.mp hn) hyint
    have h3 : 0 < orient z d y := by
      by_contra hn
      exact not_mem_interior_convexHull_of_halfplane Q z d y hzd hQzd
        (not_lt.mp hn) hyint
    have h4 : 0 < orient d v y := by
      by_contra hn
      exact not_mem_interior_convexHull_of_halfplane Q d v y hdv hQdv
        (not_lt.mp hn) hyint
    have hbase := hgp c hcP d hdP y hyP hcd hyc.symm hyd.symm
    rcases lt_or_gt_of_ne hbase with hneg | hpos
    · have hdc : 0 < orient d c y := by rw [orient_reverse]; linarith
      have ht := mem_interior_triangle_of_orient_pos c z d y hczd h2 h3 hdc
      apply htri.2.2 y hyP
      · intro hyT
        apply hyQ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
        simp only [Q,A,Finset.mem_insert, Finset.mem_singleton]
        tauto
      · simpa only [Finset.coe_insert, Finset.coe_singleton] using ht
    · have hvu : 0 < orient v u y := by
        have hn := hgp u huP v hvP y hyP huv hyu.symm hyv.symm
        have hneg := lt_of_le_of_ne (hinner y hyI) hn
        rw [orient_reverse]
        exact neg_pos.mpr hneg
      have hyquad : y ∉ ({u,c,d,v} : Finset Point) := by
        intro hy
        exact hyQ (by simp only [Q,Finset.mem_insert]; exact Or.inr (Or.inr hy))
      have hdiag := hgp c hcP v hvP y hyP hcv hyc.symm hyv.symm
      rcases lt_or_gt_of_ne hdiag with hn | hp
      · have hvc : 0 < orient v c y := by rw [orient_reverse]; linarith
        have ht := mem_interior_triangle_of_orient_pos c d v y hcdv hpos h4 hvc
        apply hquad.2.2 y hyP hyquad
        apply interior_mono (convexHull_mono ?_) ht
        simp only [Finset.coe_insert, Finset.coe_singleton]
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        tauto
      · have ht := mem_interior_triangle_of_orient_pos u c v y hucv h1 hp hvu
        apply hquad.2.2 y hyP hyquad
        apply interior_mono (convexHull_mono ?_) ht
        simp only [Finset.coe_insert, Finset.coe_singleton]
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        tauto
  have hAcard : A.card = 4 := by simp [A,huc,hud,huv,hcd,hcv,hdv]
  have hzA : z ∉ A := by
    intro hh
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl | rfl
    · linarith
    · rw [orient_refl_left] at hzneg; linarith
    · rw [orient_refl_right] at hzneg; linarith
    · linarith
  have hzAI : insert z A ⊆ inner P := by
    intro y hy
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hxnot : x ∉ insert z A := fun hh => (Finset.mem_sdiff.mp (hzAI hh)).2 hx
  refine ⟨Q,?_,hQE⟩
  simp only [Q,Finset.card_insert_of_notMem hxnot,Finset.card_insert_of_notMem hzA,hAcard]

/-- Exact one-point/double-sector local target. The apex may be any actual
point of the third-layer remainder, including its interior. -/
theorem hasEmptySix_of_one_point_double_sector
    (P : Finset Point) (hgp : GeneralPosition P)
    (u v c d w x : Point)
    (huv : BoundaryEdge (hullVertices (inner P)) u v)
    (hcd : BoundaryEdge (hullVertices (inner (inner P))) c d)
    (hw : w ∈ inner (inner P)) (hwneg : orient c d w < 0)
    (hfu : InFan w c d u) (hfv : InFan w c d v)
    (hx : x ∈ hullVertices P)
    (hchannel : 0 < orient u c x ∧ 0 < orient c d x ∧ 0 < orient d v x) :
    HasEmptySix P := by
  have huI := hullVertices_subset (inner P) huv.1
  have hvI := hullVertices_subset (inner P) huv.2.1
  have hcII := hullVertices_subset (inner (inner P)) hcd.1
  have hdII := hullVertices_subset (inner (inner P)) hcd.2.1
  have hcI := (Finset.mem_sdiff.mp hcII).1
  have hdI := (Finset.mem_sdiff.mp hdII).1
  have hwI := (Finset.mem_sdiff.mp hw).1
  have hgpI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hcu := outer_cone_point_beyond_base (inner P) hgpI c d w u
    hcII hdII hw huv.1 hwneg hfu.1 hfu.2
  have hcv := outer_cone_point_beyond_base (inner P) hgpI c d w v
    hcII hdII hw huv.2.1 hwneg hfv.1 hfv.2
  obtain ⟨z,hzP,hztri,hzneg,hempty⟩ := exists_empty_triangle_with_base P hgp c d w
    (Finset.mem_sdiff.mp hcI).1 (Finset.mem_sdiff.mp hdI).1
    (Finset.mem_sdiff.mp hwI).1 hwneg
  have hzIH : z ∈ convexHull ℝ (inner P : Set Point) := by
    apply convexHull_mono ?_ hztri
    intro y hy
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have hzI : z ∈ inner P := by
    refine Finset.mem_sdiff.mpr ⟨hzP,?_⟩
    intro hzA
    exact outer_not_mem_inner_hull P hzA hzIH
  have hzu := cone_widens_under_triangle_shrink c d w z u hwneg hztri hzneg
    hcu.le hfu.1 hfu.2
  have hzv := cone_widens_under_triangle_shrink c d w z v hwneg hztri hzneg
    hcv.le hfv.1 hfv.2
  have heq : ({c,d,z} : Finset Point) = {c,z,d} := by ext y; simp [or_comm,or_left_comm]
  have hempty' : EmptyConvexPolygon P {c,z,d} := by rwa [heq] at hempty
  obtain ⟨h1,h2,h3,h4⟩ := boundary_match_four_signs P hgp u v c d huv hcd hcu hcv
  exact empty_six_of_quad_triangle_channel P hgp u v c d z x
    huI hvI hcI hdI hzI hx h1 h2 h3 h4 hzneg hzu hzv hchannel
    (boundary_match_empty_quad P hgp u v c d huv hcd hcu hcv) hempty'
    (boundaryEdge_hull_support huv)

end JSP198.Nicolas

#print axioms JSP198.Nicolas.channel_point_in_fan
#print axioms JSP198.Nicolas.empty_six_of_quad_triangle_channel
#print axioms JSP198.Nicolas.hasEmptySix_of_one_point_double_sector
