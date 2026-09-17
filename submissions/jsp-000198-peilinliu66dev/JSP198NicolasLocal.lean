/-
Copyright (c) 2026 JSP198 formalization contributors.
Released under the MIT license; see LICENSE in this distribution.

Mathematical source:
  C. M. Nicolas, The Empty Hexagon Theorem,
  Discrete & Computational Geometry 38 (2007), 389--397.
  DOI: 10.1007/s00454-007-1343-6.

Imported geometric infrastructure (MIT): CollinYuanjieRen/awards,
commit b8bb4f7803f921a7970abc880291ad9372111360,
submissions/jsp-000198-smallk-cyr/EmptyPentagon/{Hull,Certificate}.lean.
Definitions and topological emptiness are those of namespace Horton.

This file contains proved local geometric and minimality tools for Nicolas's
proof. It DOES NOT claim the global order-preserving-matching/covering theorem,
Nicolas Theorem 4, or the final empty-hexagon theorem. No such result is taken
as a hypothesis of a purported completed wrapper.

Target: Lean 4.33.1; mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Candidate source: not compiled in the generating environment.
-/
import Mathlib
import EmptyPentagon.Hull
import EmptyPentagon.Certificate

noncomputable section
open Classical
open Horton

namespace JSP198.Nicolas

abbrev InConvexPosition (S : Finset Point) : Prop :=
  ConvexIndependent ℝ (fun p : (S : Set Point) => (p : Point))

def hullCut (P S : Finset Point) : Finset Point :=
  P.filter (fun p => p ∈ convexHull ℝ (S : Set Point))

/-- Nicolas's actual minimality, including all competing convex cardinalities. -/
structure MinimalConvex (P S : Finset Point) : Prop where
  subset : S ⊆ P
  convex : InConvexPosition S
  smaller : ∀ T : Finset Point, T ⊆ P →
    (T : Set Point) ⊆ convexHull ℝ (S : Set Point) →
    InConvexPosition T → T ≠ S → T.card < S.card

abbrev MinimalOuter (P : Finset Point) : Prop :=
  MinimalConvex P (hullVertices P)

def HasEmptySix (P : Finset Point) : Prop :=
  ∃ S : Finset Point, S.card = 6 ∧ EmptyConvexPolygon P S

def cap (P : Finset Point) (u v : Point) : Finset Point :=
  (hullVertices P).filter (fun x => 0 ≤ orient u v x)

/-- The inner remaining points, not the second hull alone. -/
def inner (P : Finset Point) : Finset Point := P \ hullVertices P

/-- A support edge is encoded by actual strict determinant inequalities. -/
def StrictSupport (Q : Finset Point) (x : Point) : Prop :=
  ∃ u ∈ Q, ∃ v ∈ Q, u ≠ v ∧ (x = u ∨ x = v) ∧
    ∀ z ∈ Q, z ≠ u → z ≠ v → orient u v z < 0

lemma gp_subset {P Q : Finset Point} (h : GeneralPosition P) (hQP : Q ⊆ P) :
    GeneralPosition Q := by
  intro a ha b hb c hc hab hac hbc
  exact h a (hQP ha) b (hQP hb) c (hQP hc) hab hac hbc

lemma orient_refl_left (a b : Point) : orient a b a = 0 := by
  unfold orient
  ring

lemma orient_refl_right (a b : Point) : orient a b b = 0 := by
  unfold orient
  ring

lemma orient_reverse (a b c : Point) : orient b a c = -orient a b c := by
  unfold orient
  ring

lemma orient_rotate (a b c : Point) : orient a b c = orient b c a := by
  unfold orient
  ring

lemma subset_hullCut {P S : Finset Point} (h : S ⊆ P) : S ⊆ hullCut P S := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨h hx, subset_convexHull ℝ _ hx⟩

lemma hullCut_subset (P S : Finset Point) : hullCut P S ⊆ P :=
  Finset.filter_subset _ _

lemma hullCut_subset_hull (P S : Finset Point) :
    (hullCut P S : Set Point) ⊆ convexHull ℝ (S : Set Point) := by
  intro x hx
  exact (Finset.mem_filter.mp hx).2

lemma convexHull_hullCut {P S : Finset Point} (h : S ⊆ P) :
    convexHull ℝ (hullCut P S : Set Point) = convexHull ℝ (S : Set Point) := by
  apply Set.Subset.antisymm
  · exact convexHull_min (hullCut_subset_hull P S) (convex_convexHull ℝ _)
  · exact convexHull_mono (show (S : Set Point) ⊆ (hullCut P S : Set Point) from
      subset_hullCut h)

/-- Old hull vertices cannot be created by convex combinations omitting them,
even when arbitrary new points of the original hull are allowed. -/
lemma hull_vertex_not_mem_hull_sdiff
    {P Q : Finset Point} {p : Point}
    (hQ : (Q : Set Point) ⊆ convexHull ℝ (P : Set Point))
    (hp : p ∈ hullVertices P) :
    p ∉ convexHull ℝ ((Q : Set Point) \ {p}) := by
  intro hmem
  have hpE : p ∈ (convexHull ℝ (P : Set Point)).extremePoints ℝ := by
    have h : p ∈ ((hullVertices P : Finset Point) : Set Point) := hp
    rwa [coe_hullVertices] at h
  have hsub : convexHull ℝ ((Q : Set Point) \ {p}) ⊆
      convexHull ℝ (P : Set Point) :=
    convexHull_min (fun x hx => hQ hx.1) (convex_convexHull ℝ _)
  have hsmall : p ∈
      (convexHull ℝ ((Q : Set Point) \ {p})).extremePoints ℝ := by
    refine ⟨hmem, ?_⟩
    intro x hx y hy hseg
    exact hpE.2 (hsub hx) (hsub hy) hseg
  have hbad := extremePoints_convexHull_subset hsmall
  exact hbad.2 (Set.mem_singleton p)

lemma hull_vertex_not_mem_hull
    {P Q : Finset Point} {p : Point}
    (hQ : (Q : Set Point) ⊆ convexHull ℝ (P : Set Point))
    (hp : p ∈ hullVertices P) (hpQ : p ∉ Q) :
    p ∉ convexHull ℝ (Q : Set Point) := by
  intro hmem
  apply hull_vertex_not_mem_hull_sdiff hQ hp
  apply convexHull_mono ?_ hmem
  intro x hx
  exact ⟨hx, fun h => hpQ (h ▸ hx)⟩

lemma hullVertices_eq_self_of_convex (S : Finset Point) (hS : InConvexPosition S) :
    hullVertices S = S := by
  apply Finset.Subset.antisymm (hullVertices_subset S)
  intro p hp
  by_contra hnot
  have hCI := (convexIndependent_set_iff_notMem_convexHull_sdiff.mp hS) p hp
  apply hCI
  have hmem : p ∈ convexHull ℝ ((hullVertices S : Finset Point) : Set Point) := by
    rw [convexHull_hullVertices]
    exact subset_convexHull ℝ _ hp
  apply convexHull_mono ?_ hmem
  intro x hx
  exact ⟨hullVertices_subset S hx, fun h => hnot (h ▸ hx)⟩

lemma hullVertices_hullCut {P S : Finset Point}
    (hSP : S ⊆ P) (hS : InConvexPosition S) : hullVertices (hullCut P S) = S := by
  have hself := hullVertices_eq_self_of_convex S hS
  apply Finset.coe_injective
  rw [coe_hullVertices, convexHull_hullCut hSP, ← coe_hullVertices, hself]

/-- A competitor containing a convex set and contained in its hull equals it. -/
lemma convex_rigidity {S T : Finset Point}
    (hT : InConvexPosition T) (hST : S ⊆ T)
    (hTS : (T : Set Point) ⊆ convexHull ℝ (S : Set Point)) : T = S := by
  apply Finset.Subset.antisymm
  · intro x hx
    have hCI := convexIndependent_set_iff_inter_convexHull_subset.mp hT
    exact hCI (S : Set Point) hST ⟨hx, hTS hx⟩
  · exact hST

/-- Minimal convex k-sets are chosen by minimizing the actual number of ambient
points in their hull. This proves the minimum, rather than assuming it. -/
theorem exists_minimal_convex
    (P : Finset Point) (k : ℕ)
    (hex : ∃ S : Finset Point, S ⊆ P ∧ InConvexPosition S ∧ S.card = k) :
    ∃ S : Finset Point, S.card = k ∧ MinimalConvex P S := by
  let C : Finset (Finset Point) :=
    P.powerset.filter (fun S => InConvexPosition S ∧ S.card = k)
  have hC : C.Nonempty := by
    obtain ⟨S, hSP, hSC, hSk⟩ := hex
    refine ⟨S, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSP, hSC, hSk⟩
  obtain ⟨S, hSC, hmin⟩ :=
    Finset.exists_min_image C (fun T => (hullCut P T).card) hC
  obtain ⟨hSP0, hSconv, hSk⟩ := Finset.mem_filter.mp hSC
  have hSP : S ⊆ P := Finset.mem_powerset.mp hSP0
  refine ⟨S, hSk, hSP, hSconv, ?_⟩
  intro T hTP hThull hTconv hTSne
  by_contra hcard
  have hkT : k ≤ T.card := by omega
  obtain ⟨U, hUT, hUk⟩ := Finset.exists_subset_card_eq hkT
  have hUP : U ⊆ P := hUT.trans hTP
  have hUconv : InConvexPosition U := hTconv.mono hUT
  have hUhull : (U : Set Point) ⊆ convexHull ℝ (S : Set Point) :=
    fun x hx => hThull (hUT hx)
  have hUne : U ≠ S := by
    intro hUS
    have hST : S ⊆ T := by simpa [hUS] using hUT
    exact hTSne (convex_rigidity hTconv hST hThull)
  have hSUnot : ¬ S ⊆ U := by
    intro hSU
    apply hUne
    exact (Finset.eq_of_subset_of_card_le hSU (by omega)).symm
  obtain ⟨x, hxS, hxU⟩ := Finset.not_subset.mp hSUnot
  have hxHv : x ∈ hullVertices S := by
    rwa [hullVertices_eq_self_of_convex S hSconv]
  have hxCH : x ∉ convexHull ℝ (U : Set Point) :=
    hull_vertex_not_mem_hull hUhull hxHv hxU
  have hcutsub : hullCut P U ⊆ hullCut P S := by
    intro y hy
    obtain ⟨hyP, hyU⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hyP,
      (convexHull_min hUhull (convex_convexHull ℝ _)) hyU⟩
  have hxcut : x ∈ hullCut P S := subset_hullCut hSP hxS
  have hxcU : x ∉ hullCut P U := by
    intro hx
    exact hxCH (Finset.mem_filter.mp hx).2
  have herase : hullCut P U ⊆ (hullCut P S).erase x := by
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun h => hxcU (h ▸ hy), hcutsub hy⟩
  have hless := Finset.card_le_card herase
  have hce := Finset.card_erase_of_mem hxcut
  have hcutpos : 0 < (hullCut P S).card := Finset.card_pos.mpr ⟨x, hxcut⟩
  have hUC : U ∈ C :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hUP, hUconv, hUk⟩
  have hge := hmin U hUC
  omega

/-- Restricting the ambient set to the chosen convex hull gives a minimal first
layer, with exactly the original chosen vertices. -/
theorem minimal_outer_hullCut {P S : Finset Point} (h : MinimalConvex P S) :
    MinimalOuter (hullCut P S) := by
  change MinimalConvex (hullCut P S) (hullVertices (hullCut P S))
  rw [show hullVertices (hullCut P S) = S from hullVertices_hullCut h.subset h.convex]
  refine ⟨subset_hullCut h.subset, h.convex, ?_⟩
  intro T hTQ hTS hTC hne
  exact h.smaller T (hTQ.trans (hullCut_subset P S)) hTS hTC hne

/-- Empty polygons in an ambient hull-cut lift to the ORIGINAL point set. -/
theorem empty_polygon_hullCut_transfer
    {P S T : Finset Point} (h : EmptyConvexPolygon (hullCut P S) T) :
    EmptyConvexPolygon P T := by
  refine ⟨h.1.trans (hullCut_subset P S), h.2.1, ?_⟩
  intro p hpP hpT hpint
  have hThull : (T : Set Point) ⊆ convexHull ℝ (S : Set Point) :=
    fun x hx => hullCut_subset_hull P S (h.1 hx)
  have hpS : p ∈ convexHull ℝ (S : Set Point) :=
    (convexHull_min hThull (convex_convexHull ℝ _)) (interior_subset hpint)
  exact h.2.2 p (Finset.mem_filter.mpr ⟨hpP, hpS⟩) hpT hpint

/-- Deleting vertices of an empty convex polygon is safe; deleting arbitrary
ambient points is not used anywhere here. -/
theorem empty_polygon_vertex_subset
    {P S T : Finset Point} (h : EmptyConvexPolygon P S) (hTS : T ⊆ S) :
    EmptyConvexPolygon P T := by
  refine ⟨hTS.trans h.1, h.2.1.mono hTS, ?_⟩
  intro p hpP hpT hpint
  by_cases hpS : p ∈ S
  · have hCI := (convexIndependent_set_iff_notMem_convexHull_sdiff.mp h.2.1) p hpS
    apply hCI
    apply convexHull_mono ?_ (interior_subset hpint)
    intro x hx
    exact ⟨hTS hx, fun h => hpT (h ▸ hx)⟩
  · exact h.2.2 p hpP hpS (interior_mono (convexHull_mono hTS) hpint)

lemma hasEmptySix_of_large_empty {P S : Finset Point}
    (h : EmptyConvexPolygon P S) (h6 : 6 ≤ S.card) : HasEmptySix P := by
  obtain ⟨T, hTS, hT6⟩ := Finset.exists_subset_card_eq h6
  exact ⟨T, hT6, empty_polygon_vertex_subset h hTS⟩

/-! ## Supporting faces and the minimality replacement inequality -/

/-- A strict half-plane together with one point on its boundary is convex. -/
lemma convex_strict_halfplane_or_point (u v q : Point) (hq : orient u v q = 0) :
    Convex ℝ {x : Point | orient u v x < 0 ∨ x = q} := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hy
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hx
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · left
      rw [orient_smul_add u v x y a b hab]
      exact add_neg (mul_neg_of_pos_of_neg ha' hx) (mul_neg_of_pos_of_neg hb' hy)
    · subst y
      left
      rw [orient_smul_add u v x q a b hab, hq, mul_zero, add_zero]
      exact mul_neg_of_pos_of_neg ha' hx
  · subst x
    rcases hy with hy | hy
    · left
      rw [orient_smul_add u v q y a b hab, hq, mul_zero, zero_add]
      exact mul_neg_of_pos_of_neg hb' hy
    · subst y
      right
      rw [← add_smul, hab, one_smul]

lemma not_mem_hull_sdiff_of_face
    (Q : Finset Point) (u v x y : Point)
    (hx0 : orient u v x = 0) (hy0 : orient u v y = 0) (hxy : x ≠ y)
    (hside : ∀ z ∈ Q, z ≠ x → z ≠ y → orient u v z < 0) :
    x ∉ convexHull ℝ ((Q : Set Point) \ {x}) := by
  intro hx
  have hsub : convexHull ℝ ((Q : Set Point) \ {x}) ⊆
      {z : Point | orient u v z < 0 ∨ z = y} := by
    apply convexHull_min _ (convex_strict_halfplane_or_point u v y hy0)
    intro z hz
    by_cases hzy : z = y
    · exact Or.inr hzy
    · exact Or.inl (hside z hz.1 hz.2 hzy)
  rcases hsub hx with hneg | heq
  · rw [hx0] at hneg
    exact lt_irrefl _ hneg
  · exact hxy heq

lemma not_mem_hull_sdiff_of_support {Q : Finset Point} {x : Point}
    (h : StrictSupport Q x) :
    x ∉ convexHull ℝ ((Q : Set Point) \ {x}) := by
  obtain ⟨u, hu, v, hv, huv, hxu | hxv, hside⟩ := h
  · subst x
    exact not_mem_hull_sdiff_of_face Q u v u v
      (orient_refl_left u v) (orient_refl_right u v) huv hside
  · subst x
    apply not_mem_hull_sdiff_of_face Q u v v u
      (orient_refl_right u v) (orient_refl_left u v) huv.symm
    intro z hz hzv hzu
    exact hside z hz hzu hzv

lemma convex_position_of_supported (Q : Finset Point)
    (h : ∀ x ∈ Q, StrictSupport Q x) : InConvexPosition Q := by
  apply convexIndependent_set_iff_notMem_convexHull_sdiff.mpr
  intro x hx
  exact not_mem_hull_sdiff_of_support (h x hx)

/-- The old outer vertices remain extreme automatically. Only the inserted
points need actual supporting-line certificates. -/
theorem convex_position_outer_supported
    (P Q : Finset Point) (hQP : Q ⊆ P)
    (hs : ∀ x ∈ Q, x ∉ hullVertices P → StrictSupport Q x) :
    InConvexPosition Q := by
  apply convexIndependent_set_iff_notMem_convexHull_sdiff.mpr
  intro x hx
  by_cases houter : x ∈ hullVertices P
  · apply hull_vertex_not_mem_hull_sdiff
      (show (Q : Set Point) ⊆ convexHull ℝ (P : Set Point) from
        fun y hy => subset_convexHull ℝ _ (hQP hy)) houter
  · exact not_mem_hull_sdiff_of_support (hs x hx houter)

/-- The finite support-chain replacement inequality. All geometric hypotheses
are determinant inequalities on specified points, not an assumed replacement
or an assumed empty-polygon theorem. -/
theorem replacement_card_lt
    (P T D : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (hTP : T ⊆ P) (hT : T.Nonempty) (hdis : Disjoint T (hullVertices P))
    (hD : D ⊆ hullVertices P)
    (hs : ∀ x ∈ T, ∃ u ∈ T, ∃ v ∈ T,
      u ≠ v ∧ (x = u ∨ x = v) ∧
      (∀ z ∈ T, orient u v z ≤ 0) ∧
      (∀ z ∈ hullVertices P \ D, orient u v z < 0)) :
    T.card < D.card := by
  let Q := T ∪ (hullVertices P \ D)
  have hQP : Q ⊆ P := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hTP hx
    · exact hullVertices_subset P (Finset.mem_sdiff.mp hx).1
  have hQC : InConvexPosition Q := by
    apply convex_position_outer_supported P Q hQP
    intro x hx hxout
    have hxT : x ∈ T := by
      rcases Finset.mem_union.mp hx with hxT | hxA
      · exact hxT
      · exact (hxout (Finset.mem_sdiff.mp hxA).1).elim
    obtain ⟨u, hu, v, hv, huv, hxuv, hTside, hAside⟩ := hs x hxT
    refine ⟨u, Finset.mem_union_left _ hu, v, Finset.mem_union_left _ hv,
      huv, hxuv, ?_⟩
    intro z hz hzu hzv
    rcases Finset.mem_union.mp hz with hzT | hzA
    · have hne : orient u v z ≠ 0 :=
        hgp u (hTP hu) v (hTP hv) z (hTP hzT) huv hzu.symm hzv.symm
      exact lt_of_le_of_ne (hTside z hzT) hne
    · exact hAside z hzA
  have hQA : Q ≠ hullVertices P := by
    obtain ⟨x, hx⟩ := hT
    intro hEq
    have hxA : x ∈ hullVertices P := hEq ▸ Finset.mem_union_left _ hx
    exact (Finset.disjoint_left.mp hdis) hx hxA
  have hsmall := hmin.smaller Q hQP
    (by intro x hx; rw [convexHull_hullVertices];
        exact subset_convexHull ℝ _ (hQP hx)) hQC hQA
  have hd : Disjoint T (hullVertices P \ D) :=
    hdis.mono_right Finset.sdiff_subset
  have hcardQ : Q.card = T.card + (hullVertices P \ D).card :=
    Finset.card_union_of_disjoint hd
  have hcardD := Finset.card_sdiff_add_card_eq_card hD
  omega

/-- Nicolas Theorem 1, strengthened to ANY two distinct inner points. -/
theorem three_le_outer_cap
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (u v : Point) (hu : u ∈ inner P) (hv : v ∈ inner P) (huv : u ≠ v) :
    3 ≤ (cap P u v).card := by
  have huP := (Finset.mem_sdiff.mp hu).1
  have hvP := (Finset.mem_sdiff.mp hv).1
  have huA := (Finset.mem_sdiff.mp hu).2
  have hvA := (Finset.mem_sdiff.mp hv).2
  have hlt := replacement_card_lt P {u, v} (cap P u v) hgp hmin
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx;
        rcases hx with hx | hx <;> subst x <;> assumption)
    (by simp)
    (by apply Finset.disjoint_left.mpr; intro x hx hxA;
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx;
        rcases hx with hx | hx <;> subst x
        · exact huA hxA
        · exact hvA hxA)
    (Finset.filter_subset _ _)
    (by
      intro x hx
      refine ⟨u, by simp, v, by simp, huv, ?_, ?_, ?_⟩
      · simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz | hz <;> subst z
        · exact (orient_refl_left u v).le
        · exact (orient_refl_right u v).le
      · intro z hz
        obtain ⟨hzA, hzD⟩ := Finset.mem_sdiff.mp hz
        have hnot : ¬ 0 ≤ orient u v z := by
          intro h
          exact hzD (Finset.mem_filter.mpr ⟨hzA, h⟩)
        exact lt_of_not_ge hnot)
  have hc : ({u, v} : Finset Point).card = 2 := by simp [huv]
  omega

/-! ## Empty cap gluing; actual topological emptiness is proved -/

/-- A support edge of the inner remainder plus ANY selected outer cap vertices
forms an empty convex polygon. No consecutiveness of the selected outer points
is assumed or needed. -/
theorem empty_polygon_edge_cap
    (P K : Finset Point) (u v : Point)
    (hu : u ∈ inner P) (hv : v ∈ inner P) (huv : u ≠ v)
    (hK : K ⊆ hullVertices P)
    (hKside : ∀ x ∈ K, 0 < orient u v x)
    (hinner : ∀ x ∈ inner P, orient u v x ≤ 0) :
    EmptyConvexPolygon P (K ∪ {u, v}) := by
  let Q := K ∪ {u, v}
  have huP := (Finset.mem_sdiff.mp hu).1
  have hvP := (Finset.mem_sdiff.mp hv).1
  have hQP : Q ⊆ P := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxK | hxuv
    · exact hullVertices_subset P (hK hxK)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxuv
      rcases hxuv with hxuv | hxuv <;> subst x <;> assumption
  have hQhalf : ∀ x ∈ Q, 0 ≤ orient u v x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxK | hxuv
    · exact (hKside x hxK).le
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxuv
      rcases hxuv with hxuv | hxuv <;> subst x
      · exact (orient_refl_left u v).ge
      · exact (orient_refl_right u v).ge
  refine ⟨hQP, convex_position_outer_supported P Q hQP ?_, ?_⟩
  · intro x hx hxA
    have hxuv : x = u ∨ x = v := by
      rcases Finset.mem_union.mp hx with hxK | hxuv
      · exact (hxA (hK hxK)).elim
      · simpa only [Finset.mem_insert, Finset.mem_singleton] using hxuv
    refine ⟨v, by simp [Q], u, by simp [Q], huv.symm, hxuv.symm, ?_⟩
    intro z hz hzv hzu
    have hzK : z ∈ K := by
      rcases Finset.mem_union.mp hz with hzK | hzuv
      · exact hzK
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hzuv
        exact (hzuv.elim hzu hzv).elim
    rw [orient_reverse]
    exact neg_lt_zero.mpr (hKside z hzK)
  · intro x hxP hxQ hxint
    by_cases hxA : x ∈ hullVertices P
    · exact hull_vertex_not_mem_hull
        (fun y hy => subset_convexHull ℝ _ (hQP hy)) hxA hxQ
        (interior_subset hxint)
    · exact not_mem_interior_convexHull_of_halfplane Q u v x huv hQhalf
        (hinner x (Finset.mem_sdiff.mpr ⟨hxP, hxA⟩)) hxint

/-- In a minimal, hexagon-free set, every inner supporting edge sees exactly
three outer vertices. This combines the replacement and emptiness arguments. -/
theorem outer_cap_card_eq_three
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (hno : ¬ HasEmptySix P) (u v : Point)
    (hu : u ∈ inner P) (hv : v ∈ inner P) (huv : u ≠ v)
    (hinner : ∀ x ∈ inner P, orient u v x ≤ 0) :
    (cap P u v).card = 3 := by
  have hlow := three_le_outer_cap P hgp hmin u v hu hv huv
  have hupper : (cap P u v).card ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ (cap P u v).card := by omega
    obtain ⟨K, hKcap, hK4⟩ := Finset.exists_subset_card_eq h4
    have hKA : K ⊆ hullVertices P := hKcap.trans (Finset.filter_subset _ _)
    have hside : ∀ x ∈ K, 0 < orient u v x := by
      intro x hx
      obtain ⟨hxA, hxnonneg⟩ := Finset.mem_filter.mp (hKcap hx)
      have hux : u ≠ x := by
        intro hEq
        exact (Finset.mem_sdiff.mp hu).2 (hEq.symm ▸ hxA)
      have hvx : v ≠ x := by
        intro hEq
        exact (Finset.mem_sdiff.mp hv).2 (hEq.symm ▸ hxA)
      have hne := hgp u (Finset.mem_sdiff.mp hu).1 v (Finset.mem_sdiff.mp hv).1
        x (hullVertices_subset P hxA) huv hux hvx
      exact lt_of_le_of_ne hxnonneg hne.symm
    have hempty := empty_polygon_edge_cap P K u v hu hv huv hKA hside hinner
    have hd : Disjoint K ({u, v} : Finset Point) := by
      apply Finset.disjoint_left.mpr
      intro x hxK hxuv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxuv
      rcases hxuv with hxuv | hxuv <;> subst x
      · exact (Finset.mem_sdiff.mp hu).2 (hKA hxK)
      · exact (Finset.mem_sdiff.mp hv).2 (hKA hxK)
    apply hno
    refine ⟨K ∪ {u, v}, ?_, hempty⟩
    rw [Finset.card_union_of_disjoint hd]
    simp [hK4, huv]
  omega

end JSP198.Nicolas

namespace JSP198.Nicolas

/-! ## Empty-triangle selection and the two local six-gon gluing rules -/

lemma triangle_convex_of_negative_orientation (u v z : Point)
    (hneg : orient u v z < 0) : InConvexPosition ({u, v, z} : Finset Point) := by
  have huv : u ≠ v := by
    intro h
    subst v
    simp [orient] at hneg
  have huz : u ≠ z := by
    intro h
    subst z
    rw [orient_refl_left] at hneg
    exact lt_irrefl _ hneg
  have hvz : v ≠ z := by
    intro h
    subst z
    rw [orient_refl_right] at hneg
    exact lt_irrefl _ hneg
  apply convex_position_of_supported
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx <;> subst x
  · refine ⟨u, by simp, v, by simp, huv, Or.inl rfl, ?_⟩
    intro w hw hwu hwv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw <;> subst w
    · exact (hwu rfl).elim
    · exact (hwv rfl).elim
    · exact hneg
  · refine ⟨u, by simp, v, by simp, huv, Or.inr rfl, ?_⟩
    intro w hw hwu hwv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw <;> subst w
    · exact (hwu rfl).elim
    · exact (hwv rfl).elim
    · exact hneg
  · refine ⟨v, by simp, z, by simp, hvz, Or.inr rfl, ?_⟩
    intro w hw hwv hwz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw <;> subst w
    · rw [← orient_rotate u v z]
      exact hneg
    · exact (hwv rfl).elim
    · exact (hwz rfl).elim

/-- Choose the closest ambient point to a fixed base inside a specified triangle.
The resulting triangle is genuinely empty in P, not just in a selected layer. -/
theorem exists_empty_triangle_with_base
    (P : Finset Point) (hgp : GeneralPosition P)
    (u v w : Point) (hu : u ∈ P) (hv : v ∈ P) (hw : w ∈ P)
    (hwneg : orient u v w < 0) :
    ∃ z ∈ P, z ∈ convexHull ℝ ({u, v, w} : Set Point) ∧
      orient u v z < 0 ∧ EmptyConvexPolygon P {u, v, z} := by
  let C := P.filter (fun z =>
    z ∈ convexHull ℝ ({u, v, w} : Set Point) ∧ orient u v z < 0)
  have hC : C.Nonempty := by
    refine ⟨w, Finset.mem_filter.mpr ⟨hw, ?_, hwneg⟩⟩
    exact subset_convexHull ℝ _ (by simp)
  obtain ⟨z, hzC, hmax⟩ := Finset.exists_max_image C (orient u v) hC
  obtain ⟨hzP, hzhull, hzneg⟩ := Finset.mem_filter.mp hzC
  have huv : u ≠ v := by
    intro h
    subst v
    simp [orient] at hzneg
  have hTsub : ({u, v, z} : Finset Point) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> subst x <;> assumption
  have hThull : ({u, v, z} : Set Point) ⊆
      convexHull ℝ ({u, v, w} : Set Point) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx <;> subst x
    · exact subset_convexHull ℝ _ (by simp)
    · exact subset_convexHull ℝ _ (by simp)
    · exact hzhull
  refine ⟨z, hzP, hzhull, hzneg, hTsub,
    triangle_convex_of_negative_orientation u v z hzneg, ?_⟩
  intro x hxP hxT hxint
  have hxu : x ≠ u := by intro h; exact hxT (by simp [h])
  have hxv : x ≠ v := by intro h; exact hxT (by simp [h])
  have hxz : x ≠ z := by intro h; exact hxT (by simp [h])
  have hxtriangle : x ∈ convexHull ℝ ({u, v, z} : Set Point) := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using interior_subset hxint
  obtain ⟨a, b, c, ha, hb, hc, habc, hxrep⟩ :=
    exists_barycentric_of_mem_convexHull_triangle u v z x hxtriangle
  have hcle : c ≤ 1 := by linarith
  have hclt : c < 1 := by
    by_contra h
    have hc1 : c = 1 := by linarith
    have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    apply hxz
    simpa [ha0, hb0, hc1] using hxrep
  have hxeq : orient u v x = c * orient u v z := by
    rw [hxrep, orient_affine_comb u v u v z a b c habc,
      orient_refl_left, orient_refl_right]
    ring
  have hxne : orient u v x ≠ 0 := hgp u hu v hv x hxP huv hxu.symm hxv.symm
  have hxle : orient u v x ≤ 0 := by
    rw [hxeq]
    exact mul_nonpos_of_nonneg_of_nonpos hc hzneg.le
  have hxneg : orient u v x < 0 := lt_of_le_of_ne hxle hxne
  have hxorig : x ∈ convexHull ℝ ({u, v, w} : Set Point) :=
    (convexHull_min hThull (convex_convexHull ℝ _)) hxtriangle
  have hxC : x ∈ C := Finset.mem_filter.mpr ⟨hxP, hxorig, hxneg⟩
  have hbound := hmax x hxC
  have hstrict : orient u v z < orient u v x := by
    rw [hxeq]
    simpa only [one_mul] using mul_lt_mul_of_neg_right hclt hzneg
  exact (not_lt_of_ge hbound) hstrict

lemma strictSupport_of_nonnegative_halfplane
    (P Q : Finset Point) (hgp : GeneralPosition P) (hQP : Q ⊆ P)
    (u v x : Point) (hu : u ∈ Q) (hv : v ∈ Q) (huv : u ≠ v)
    (hx : x = u ∨ x = v) (hside : ∀ z ∈ Q, 0 ≤ orient u v z) :
    StrictSupport Q x := by
  refine ⟨v, hv, u, hu, huv.symm, hx.symm, ?_⟩
  intro z hz hzv hzu
  have hne := hgp u (hQP hu) v (hQP hv) z (hQP hz) huv hzu.symm hzv.symm
  have hpos : 0 < orient u v z := lt_of_le_of_ne (hside z hz) hne.symm
  rw [orient_reverse]
  exact neg_lt_zero.mpr hpos

/-- Exact cone gluing. u,v form a supporting edge of the inner remainder;
z is an inner point giving an empty triangle. Outer vertices in the two
specified positive half-planes can all be glued to that triangle. -/
theorem empty_polygon_triangle_cone
    (P K : Finset Point) (hgp : GeneralPosition P)
    (u z v : Point) (hu : u ∈ inner P) (hz : z ∈ inner P) (hv : v ∈ inner P)
    (huzv : 0 < orient u z v)
    (hempty : EmptyConvexPolygon P {u, z, v})
    (hinner : ∀ x ∈ inner P, orient u v x ≤ 0)
    (hK : K ⊆ hullVertices P)
    (hcone : ∀ x ∈ K, 0 < orient u z x ∧ 0 < orient z v x) :
    EmptyConvexPolygon P (K ∪ {u, z, v}) := by
  let Q := K ∪ ({u, z, v} : Finset Point)
  have huP := (Finset.mem_sdiff.mp hu).1
  have hzP := (Finset.mem_sdiff.mp hz).1
  have hvP := (Finset.mem_sdiff.mp hv).1
  have huz : u ≠ z := by intro h; subst z; simp [orient] at huzv
  have huv : u ≠ v := by
    intro h
    subst v
    rw [orient_refl_left] at huzv
    exact lt_irrefl _ huzv
  have hzv : z ≠ v := by
    intro h
    subst v
    rw [orient_refl_right] at huzv
    exact lt_irrefl _ huzv
  have hQP : Q ⊆ P := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxK | hxT
    · exact hullVertices_subset P (hK hxK)
    · exact hempty.1 hxT
  have hQ1 : ∀ x ∈ Q, 0 ≤ orient u z x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxK | hxT
    · exact (hcone x hxK).1.le
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with hxT | hxT | hxT <;> subst x
      · exact (orient_refl_left u z).ge
      · exact (orient_refl_right u z).ge
      · exact huzv.le
  have hQ2 : ∀ x ∈ Q, 0 ≤ orient z v x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxK | hxT
    · exact (hcone x hxK).2.le
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with hxT | hxT | hxT <;> subst x
      · rw [← orient_rotate u z v]
        exact huzv.le
      · exact (orient_refl_left z v).ge
      · exact (orient_refl_right z v).ge
  have hQC : InConvexPosition Q := by
    apply convex_position_outer_supported P Q hQP
    intro x hx hxA
    have hxT : x ∈ ({u, z, v} : Finset Point) := by
      rcases Finset.mem_union.mp hx with hxK | hxT
      · exact (hxA (hK hxK)).elim
      · exact hxT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
    rcases hxT with hxT | hxT | hxT <;> subst x
    · exact strictSupport_of_nonnegative_halfplane P Q hgp hQP u z u
        (by simp [Q]) (by simp [Q]) huz (Or.inl rfl) hQ1
    · exact strictSupport_of_nonnegative_halfplane P Q hgp hQP u z z
        (by simp [Q]) (by simp [Q]) huz (Or.inr rfl) hQ1
    · exact strictSupport_of_nonnegative_halfplane P Q hgp hQP z v v
        (by simp [Q]) (by simp [Q]) hzv (Or.inr rfl) hQ2
  refine ⟨hQP, hQC, ?_⟩
  intro x hxP hxQ hxint
  by_cases hxA : x ∈ hullVertices P
  · exact hull_vertex_not_mem_hull
      (fun y hy => subset_convexHull ℝ _ (hQP hy)) hxA hxQ
      (interior_subset hxint)
  have hxI : x ∈ inner P := Finset.mem_sdiff.mpr ⟨hxP, hxA⟩
  have hxu : x ≠ u := by intro h; exact hxQ (by simp [Q, h])
  have hxz : x ≠ z := by intro h; exact hxQ (by simp [Q, h])
  have hxv : x ≠ v := by intro h; exact hxQ (by simp [Q, h])
  have h1 : 0 < orient u z x := by
    by_contra h
    exact not_mem_interior_convexHull_of_halfplane Q u z x huz hQ1
      (not_lt.mp h) hxint
  have h2 : 0 < orient z v x := by
    by_contra h
    exact not_mem_interior_convexHull_of_halfplane Q z v x hzv hQ2
      (not_lt.mp h) hxint
  have h3 : 0 < orient v u x := by
    have hne := hgp u huP v hvP x hxP huv hxu.symm hxv.symm
    have hneg := lt_of_le_of_ne (hinner x hxI) hne
    rw [orient_reverse]
    exact neg_pos.mpr hneg
  have hint := mem_interior_triangle_of_orient_pos u z v x huzv h1 h2 h3
  apply hempty.2.2 x hxP
  · intro hxT
    exact hxQ (Finset.mem_union_right _ hxT)
  · simpa only [Finset.coe_insert, Finset.coe_singleton] using hint

/-- In particular, three actual outer cone points give a six-gon. -/
theorem hasEmptySix_of_triangle_cone
    (P K : Finset Point) (hgp : GeneralPosition P)
    (u z v : Point) (hu : u ∈ inner P) (hz : z ∈ inner P) (hv : v ∈ inner P)
    (huzv : 0 < orient u z v)
    (hempty : EmptyConvexPolygon P {u, z, v})
    (hinner : ∀ x ∈ inner P, orient u v x ≤ 0)
    (hK : K ⊆ hullVertices P)
    (hcone : ∀ x ∈ K, 0 < orient u z x ∧ 0 < orient z v x)
    (hK3 : 3 ≤ K.card) : HasEmptySix P := by
  have h := empty_polygon_triangle_cone P K hgp u z v hu hz hv huzv
    hempty hinner hK hcone
  have huz : u ≠ z := by intro h; subst z; simp [orient] at huzv
  have huv : u ≠ v := by
    intro h
    subst v
    rw [orient_refl_left] at huzv
    exact lt_irrefl _ huzv
  have hzv : z ≠ v := by
    intro h
    subst v
    rw [orient_refl_right] at huzv
    exact lt_irrefl _ huzv
  have hd : Disjoint K ({u, z, v} : Finset Point) := by
    apply Finset.disjoint_left.mpr
    intro x hxK hxT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
    rcases hxT with hxT | hxT | hxT <;> subst x
    · exact (Finset.mem_sdiff.mp hu).2 (hK hxK)
    · exact (Finset.mem_sdiff.mp hz).2 (hK hxK)
    · exact (Finset.mem_sdiff.mp hv).2 (hK hxK)
  apply hasEmptySix_of_large_empty h
  rw [Finset.card_union_of_disjoint hd]
  have hT3 : ({u, z, v} : Finset Point).card = 3 := by simp [huz, huv, hzv]
  omega

/-- Exact four-point channel gluing. The hypotheses specify a strictly convex
u,p,q,v quadrilateral by all four ordered triple signs, its actual emptiness,
and the three open half-planes of the outer channel. -/
theorem empty_polygon_quad_channel
    (P K : Finset Point) (hgp : GeneralPosition P)
    (u p q v : Point)
    (hu : u ∈ inner P) (hp : p ∈ inner P)
    (hq : q ∈ inner P) (hv : v ∈ inner P)
    (hupq : 0 < orient u p q) (hupv : 0 < orient u p v)
    (huqv : 0 < orient u q v) (hpqv : 0 < orient p q v)
    (hempty : EmptyConvexPolygon P {u, p, q, v})
    (hinner : ∀ x ∈ inner P, orient u v x ≤ 0)
    (hK : K ⊆ hullVertices P)
    (hchannel : ∀ x ∈ K,
      0 < orient u p x ∧ 0 < orient p q x ∧ 0 < orient q v x) :
    EmptyConvexPolygon P (K ∪ {u, p, q, v}) := by
  let Q := K ∪ ({u, p, q, v} : Finset Point)
  have huP := (Finset.mem_sdiff.mp hu).1
  have hpP := (Finset.mem_sdiff.mp hp).1
  have hqP := (Finset.mem_sdiff.mp hq).1
  have hvP := (Finset.mem_sdiff.mp hv).1
  have hup : u ≠ p := by intro h; subst p; simp [orient] at hupq
  have hpq : p ≠ q := by
    intro h
    subst q
    rw [orient_refl_right] at hupq
    exact lt_irrefl _ hupq
  have hqv : q ≠ v := by
    intro h
    subst v
    rw [orient_refl_right] at hpqv
    exact lt_irrefl _ hpqv
  have huv : u ≠ v := by
    intro h
    subst v
    rw [orient_refl_left] at hupv
    exact lt_irrefl _ hupv
  have hpv : p ≠ v := by
    intro h
    subst v
    rw [orient_refl_right] at hupv
    exact lt_irrefl _ hupv
  have hQP : Q ⊆ P := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxK | hxT
    · exact hullVertices_subset P (hK hxK)
    · exact hempty.1 hxT
  have hQ1 : ∀ x ∈ Q, 0 ≤ orient u p x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxK | hxT
    · exact (hchannel x hxK).1.le
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with hxT | hxT | hxT | hxT <;> subst x
      · exact (orient_refl_left u p).ge
      · exact (orient_refl_right u p).ge
      · exact hupq.le
      · exact hupv.le
  have hQ2 : ∀ x ∈ Q, 0 ≤ orient p q x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxK | hxT
    · exact (hchannel x hxK).2.1.le
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with hxT | hxT | hxT | hxT <;> subst x
      · rw [← orient_rotate u p q]
        exact hupq.le
      · exact (orient_refl_left p q).ge
      · exact (orient_refl_right p q).ge
      · exact hpqv.le
  have hQ3 : ∀ x ∈ Q, 0 ≤ orient q v x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxK | hxT
    · exact (hchannel x hxK).2.2.le
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with hxT | hxT | hxT | hxT <;> subst x
      · rw [← orient_rotate u q v]
        exact huqv.le
      · rw [← orient_rotate p q v]
        exact hpqv.le
      · exact (orient_refl_left q v).ge
      · exact (orient_refl_right q v).ge
  have hQC : InConvexPosition Q := by
    apply convex_position_outer_supported P Q hQP
    intro x hx hxA
    have hxT : x ∈ ({u, p, q, v} : Finset Point) := by
      rcases Finset.mem_union.mp hx with hxK | hxT
      · exact (hxA (hK hxK)).elim
      · exact hxT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
    rcases hxT with hxT | hxT | hxT | hxT <;> subst x
    · exact strictSupport_of_nonnegative_halfplane P Q hgp hQP u p u
        (by simp [Q]) (by simp [Q]) hup (Or.inl rfl) hQ1
    · exact strictSupport_of_nonnegative_halfplane P Q hgp hQP u p p
        (by simp [Q]) (by simp [Q]) hup (Or.inr rfl) hQ1
    · exact strictSupport_of_nonnegative_halfplane P Q hgp hQP p q q
        (by simp [Q]) (by simp [Q]) hpq (Or.inr rfl) hQ2
    · exact strictSupport_of_nonnegative_halfplane P Q hgp hQP q v v
        (by simp [Q]) (by simp [Q]) hqv (Or.inr rfl) hQ3
  refine ⟨hQP, hQC, ?_⟩
  intro x hxP hxQ hxint
  by_cases hxA : x ∈ hullVertices P
  · exact hull_vertex_not_mem_hull
      (fun y hy => subset_convexHull ℝ _ (hQP hy)) hxA hxQ
      (interior_subset hxint)
  have hxI : x ∈ inner P := Finset.mem_sdiff.mpr ⟨hxP, hxA⟩
  have hxu : x ≠ u := by intro h; exact hxQ (by simp [Q, h])
  have hxp : x ≠ p := by intro h; exact hxQ (by simp [Q, h])
  have hxv : x ≠ v := by intro h; exact hxQ (by simp [Q, h])
  have h1 : 0 < orient u p x := by
    by_contra h
    exact not_mem_interior_convexHull_of_halfplane Q u p x hup hQ1
      (not_lt.mp h) hxint
  have h2 : 0 < orient p q x := by
    by_contra h
    exact not_mem_interior_convexHull_of_halfplane Q p q x hpq hQ2
      (not_lt.mp h) hxint
  have h3 : 0 < orient q v x := by
    by_contra h
    exact not_mem_interior_convexHull_of_halfplane Q q v x hqv hQ3
      (not_lt.mp h) hxint
  have h4 : 0 < orient v u x := by
    have hne := hgp u huP v hvP x hxP huv hxu.symm hxv.symm
    have hneg := lt_of_le_of_ne (hinner x hxI) hne
    rw [orient_reverse]
    exact neg_pos.mpr hneg
  have hxnotT : x ∉ ({u, p, q, v} : Finset Point) := by
    intro hx
    exact hxQ (Finset.mem_union_right _ hx)
  have hpvx := hgp p hpP v hvP x hxP hpv hxp.symm hxv.symm
  rcases lt_or_gt_of_ne hpvx with hneg | hpos
  · have h5 : 0 < orient v p x := by
      rw [orient_reverse]
      exact neg_pos.mpr hneg
    have ht := mem_interior_triangle_of_orient_pos p q v x hpqv h2 h3 h5
    apply hempty.2.2 x hxP hxnotT
    apply interior_mono (convexHull_mono ?_) ht
    simp only [Finset.coe_insert, Finset.coe_singleton]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    aesop
  · have ht := mem_interior_triangle_of_orient_pos u p v x hupv h1 hpos h4
    apply hempty.2.2 x hxP hxnotT
    apply interior_mono (convexHull_mono ?_) ht
    simp only [Finset.coe_insert, Finset.coe_singleton]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    aesop

/-- Two outer channel points turn an actually empty matched quadrilateral into
an empty six-gon of the original ambient set. -/
theorem hasEmptySix_of_quad_channel
    (P K : Finset Point) (hgp : GeneralPosition P)
    (u p q v : Point)
    (hu : u ∈ inner P) (hp : p ∈ inner P)
    (hq : q ∈ inner P) (hv : v ∈ inner P)
    (hupq : 0 < orient u p q) (hupv : 0 < orient u p v)
    (huqv : 0 < orient u q v) (hpqv : 0 < orient p q v)
    (hempty : EmptyConvexPolygon P {u, p, q, v})
    (hinner : ∀ x ∈ inner P, orient u v x ≤ 0)
    (hK : K ⊆ hullVertices P)
    (hchannel : ∀ x ∈ K,
      0 < orient u p x ∧ 0 < orient p q x ∧ 0 < orient q v x)
    (hK2 : 2 ≤ K.card) : HasEmptySix P := by
  have he := empty_polygon_quad_channel P K hgp u p q v hu hp hq hv
    hupq hupv huqv hpqv hempty hinner hK hchannel
  have hup : u ≠ p := by intro h; subst p; simp [orient] at hupq
  have huq : u ≠ q := by
    intro h; subst q; rw [orient_refl_left] at hupq; exact lt_irrefl _ hupq
  have huv : u ≠ v := by
    intro h; subst v; rw [orient_refl_left] at hupv; exact lt_irrefl _ hupv
  have hpq : p ≠ q := by
    intro h; subst q; rw [orient_refl_right] at hupq; exact lt_irrefl _ hupq
  have hpv : p ≠ v := by
    intro h; subst v; rw [orient_refl_right] at hupv; exact lt_irrefl _ hupv
  have hqv : q ≠ v := by
    intro h; subst v; rw [orient_refl_right] at hpqv; exact lt_irrefl _ hpqv
  have hd : Disjoint K ({u, p, q, v} : Finset Point) := by
    apply Finset.disjoint_left.mpr
    intro x hxK hxT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
    rcases hxT with hxT | hxT | hxT | hxT <;> subst x
    · exact (Finset.mem_sdiff.mp hu).2 (hK hxK)
    · exact (Finset.mem_sdiff.mp hp).2 (hK hxK)
    · exact (Finset.mem_sdiff.mp hq).2 (hK hxK)
    · exact (Finset.mem_sdiff.mp hv).2 (hK hxK)
  apply hasEmptySix_of_large_empty he
  rw [Finset.card_union_of_disjoint hd]
  have hT4 : ({u, p, q, v} : Finset Point).card = 4 := by
    simp [hup, huq, huv, hpq, hpv, hqv]
  omega

/-! ## Matching really implies ambient emptiness -/

/-- A polygon in the second-layer hull whose interior avoids the third-layer
hull is empty in P. This discharges the emptiness part of Nicolas's annular
matching definition using the actual convex hulls. -/
theorem empty_polygon_of_annular_interior
    (P Q : Finset Point) (hQI : Q ⊆ inner P) (hQC : InConvexPosition Q)
    (havoid : Disjoint
      (interior (convexHull ℝ (Q : Set Point)))
      (convexHull ℝ ((hullVertices (inner (inner P)) : Finset Point) : Set Point))) :
    EmptyConvexPolygon P Q := by
  have hQP : Q ⊆ P := hQI.trans Finset.sdiff_subset
  refine ⟨hQP, hQC, ?_⟩
  intro x hxP hxQ hxint
  by_cases hxA : x ∈ hullVertices P
  · exact hull_vertex_not_mem_hull
      (fun y hy => subset_convexHull ℝ _ (hQP hy)) hxA hxQ
      (interior_subset hxint)
  have hxI : x ∈ inner P := Finset.mem_sdiff.mpr ⟨hxP, hxA⟩
  by_cases hxB : x ∈ hullVertices (inner P)
  · exact hull_vertex_not_mem_hull
      (fun y hy => subset_convexHull ℝ _ (hQI hy)) hxB hxQ
      (interior_subset hxint)
  have hxII : x ∈ inner (inner P) := Finset.mem_sdiff.mpr ⟨hxI, hxB⟩
  have hxC : x ∈ convexHull ℝ
      ((hullVertices (inner (inner P)) : Finset Point) : Set Point) := by
    rw [convexHull_hullVertices]
    exact subset_convexHull ℝ _ hxII
  exact Set.disjoint_left.mp havoid hxint hxC

end JSP198.Nicolas

namespace JSP198.Nicolas

/-! ## Transport after shrinking a triangle; no hidden empty-triangle premise -/

lemma orient_affine_second (u a b c x : Point) (s t r : ℝ) (hsum : s + t + r = 1) :
    orient u (s • a + t • b + r • c) x =
      s * orient u a x + t * orient u b x + r * orient u c x := by
  have hr : r = 1 - s - t := by linarith
  subst r
  simp only [orient, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  ring

lemma orient_affine_first (a b c v x : Point) (s t r : ℝ) (hsum : s + t + r = 1) :
    orient (s • a + t • b + r • c) v x =
      s * orient a v x + t * orient b v x + r * orient c v x := by
  have hr : r = 1 - s - t := by linarith
  subst r
  simp only [orient, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  ring

lemma cone_widens_under_triangle_shrink
    (u v w z x : Point)
    (hw : orient u v w < 0)
    (hz : z ∈ convexHull ℝ ({u, v, w} : Set Point))
    (hzneg : orient u v z < 0)
    (hxbase : 0 ≤ orient u v x)
    (hx1 : 0 < orient u w x) (hx2 : 0 < orient w v x) :
    0 < orient u z x ∧ 0 < orient z v x := by
  obtain ⟨a, b, c, ha, hb, hc, hsum, hzrep⟩ :=
    exists_barycentric_of_mem_convexHull_triangle u v w z hz
  have hzbase : orient u v z = c * orient u v w := by
    rw [hzrep, orient_affine_comb u v u v w a b c hsum,
      orient_refl_left, orient_refl_right]
    ring
  have hcpos : 0 < c := by
    by_contra h
    have hc0 : c = 0 := by linarith
    rw [hc0, zero_mul] at hzbase
    linarith
  constructor
  · rw [hzrep, orient_affine_second u u v w x a b c hsum]
    have he : orient u u x = 0 := by unfold orient; ring
    rw [he, mul_zero, zero_add]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hb hxbase) (mul_pos hcpos hx1)
  · rw [hzrep, orient_affine_first u v w v x a b c hsum]
    have he : orient v v x = 0 := by unfold orient; ring
    rw [he, mul_zero, add_zero]
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha hxbase) (mul_pos hcpos hx2)

lemma outer_cone_point_beyond_base
    (P : Finset Point) (hgp : GeneralPosition P)
    (u v w x : Point) (hu : u ∈ inner P) (hv : v ∈ inner P)
    (hw : w ∈ inner P) (hx : x ∈ hullVertices P)
    (hwneg : orient u v w < 0)
    (hx1 : 0 < orient u w x) (hx2 : 0 < orient w v x) :
    0 < orient u v x := by
  have huv : u ≠ v := by intro h; subst v; simp [orient] at hwneg
  have hxu : x ≠ u := by
    intro h
    exact (Finset.mem_sdiff.mp hu).2 (h ▸ hx)
  have hxv : x ≠ v := by
    intro h
    exact (Finset.mem_sdiff.mp hv).2 (h ▸ hx)
  by_contra h
  have hnonpos : orient u v x ≤ 0 := not_lt.mp h
  have hne := hgp u (Finset.mem_sdiff.mp hu).1 v (Finset.mem_sdiff.mp hv).1
    x (hullVertices_subset P hx) huv hxu.symm hxv.symm
  have hneg : orient u v x < 0 := lt_of_le_of_ne hnonpos hne
  have htri : 0 < orient u w v := by
    have he : orient u w v = -orient u v w := by unfold orient; ring
    rw [he]
    exact neg_pos.mpr hwneg
  have hx3 : 0 < orient v u x := by
    rw [orient_reverse]
    exact neg_pos.mpr hneg
  have hxtri := mem_interior_triangle_of_orient_pos u w v x htri hx1 hx2 hx3
  have hxIH : x ∈ convexHull ℝ (inner P : Set Point) := by
    apply convexHull_mono ?_ (interior_subset hxtri)
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> subst y <;> assumption
  have hxnotI : x ∉ inner P := by
    intro hi
    exact (Finset.mem_sdiff.mp hi).2 hx
  exact hull_vertex_not_mem_hull
    (fun y hy => subset_convexHull ℝ _ (Finset.mem_sdiff.mp hy).1)
    hx hxnotI hxIH

/-- The three-points-in-a-cone rule used in Theorem 3 and Theorem 4.
The initially supplied triangle need not be empty: the proof selects an actual
empty one and transports all cone inequalities to it. -/
theorem hasEmptySix_of_three_in_cone
    (P K : Finset Point) (hgp : GeneralPosition P)
    (u v w : Point) (hu : u ∈ inner P) (hv : v ∈ inner P) (hw : w ∈ inner P)
    (hwneg : orient u v w < 0)
    (hinner : ∀ x ∈ inner P, orient u v x ≤ 0)
    (hK : K ⊆ hullVertices P)
    (hcone : ∀ x ∈ K, 0 < orient u w x ∧ 0 < orient w v x)
    (hK3 : 3 ≤ K.card) : HasEmptySix P := by
  obtain ⟨z, hzP, hztri, hzneg, hempty⟩ :=
    exists_empty_triangle_with_base P hgp u v w
      (Finset.mem_sdiff.mp hu).1 (Finset.mem_sdiff.mp hv).1
      (Finset.mem_sdiff.mp hw).1 hwneg
  have hzIH : z ∈ convexHull ℝ (inner P : Set Point) := by
    apply convexHull_mono ?_ hztri
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> subst y <;> assumption
  have hzI : z ∈ inner P := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hzP, ?_⟩
    intro hzA
    have hznotI : z ∉ inner P := by
      intro hzI
      exact (Finset.mem_sdiff.mp hzI).2 hzA
    exact hull_vertex_not_mem_hull
      (fun y hy => subset_convexHull ℝ _ (Finset.mem_sdiff.mp hy).1)
      hzA hznotI hzIH
  have heq : ({u, v, z} : Finset Point) = {u, z, v} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hempty' : EmptyConvexPolygon P {u, z, v} := by rwa [heq] at hempty
  have hpos : 0 < orient u z v := by
    have he : orient u z v = -orient u v z := by unfold orient; ring
    rw [he]
    exact neg_pos.mpr hzneg
  apply hasEmptySix_of_triangle_cone P K hgp u z v hu hzI hv
    hpos hempty' hinner hK _ hK3
  intro x hxK
  obtain ⟨hx1, hx2⟩ := hcone x hxK
  have hbase := outer_cone_point_beyond_base P hgp u v w x hu hv hw
    (hK hxK) hwneg hx1 hx2
  exact cone_widens_under_triangle_shrink u v w z x hwneg hztri hzneg hbase.le hx1 hx2

/-- Removing the entire outer layer cannot create a false ambient hole. -/
theorem empty_polygon_inner_transfer {P Q : Finset Point}
    (h : EmptyConvexPolygon (inner P) Q) : EmptyConvexPolygon P Q := by
  have hQP : Q ⊆ P := h.1.trans Finset.sdiff_subset
  refine ⟨hQP, h.2.1, ?_⟩
  intro x hxP hxQ hxint
  by_cases hxA : x ∈ hullVertices P
  · exact hull_vertex_not_mem_hull
      (fun y hy => subset_convexHull ℝ _ (hQP hy)) hxA hxQ
      (interior_subset hxint)
  · exact h.2.2 x (Finset.mem_sdiff.mpr ⟨hxP, hxA⟩) hxQ hxint

lemma hasEmptySix_inner_transfer {P : Finset Point}
    (h : HasEmptySix (inner P)) : HasEmptySix P := by
  obtain ⟨Q, hQ6, hQ⟩ := h
  exact ⟨Q, hQ6, empty_polygon_inner_transfer hQ⟩

/-- The exact, proved input-normalization interface for the separately supplied
ES(25) result. No empty-hexagon assertion is included among the hypotheses. -/
theorem convex25_minimal_setup
    (P : Finset Point) (hgp : GeneralPosition P)
    (hex : ∃ S : Finset Point, S ⊆ P ∧ InConvexPosition S ∧ S.card = 25) :
    ∃ S : Finset Point,
      S ⊆ P ∧ S.card = 25 ∧ InConvexPosition S ∧
      MinimalOuter (hullCut P S) ∧
      GeneralPosition (hullCut P S) ∧
      hullVertices (hullCut P S) = S ∧
      (∀ T : Finset Point, EmptyConvexPolygon (hullCut P S) T →
        EmptyConvexPolygon P T) := by
  obtain ⟨S, hS25, hmin⟩ := exists_minimal_convex P 25 hex
  exact ⟨S, hmin.subset, hS25, hmin.convex,
    minimal_outer_hullCut hmin,
    gp_subset hgp (hullCut_subset P S),
    hullVertices_hullCut hmin.subset hmin.convex,
    fun _ h => empty_polygon_hullCut_transfer h⟩

end JSP198.Nicolas

namespace JSP198.Nicolas

/-- The strict four-triple determinant test supplies the quadrilateral's convexity;
it is not an input called `isConvexQuadrilateral`. -/
theorem quad_convex_of_four_signs
    (P : Finset Point) (hgp : GeneralPosition P)
    (u p q v : Point) (hu : u ∈ P) (hp : p ∈ P) (hq : q ∈ P) (hv : v ∈ P)
    (hupq : 0 < orient u p q) (hupv : 0 < orient u p v)
    (huqv : 0 < orient u q v) (hpqv : 0 < orient p q v) :
    InConvexPosition ({u, p, q, v} : Finset Point) := by
  let T : Finset Point := {u, p, q, v}
  have hTP : T ⊆ P := by
    intro x hx
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx <;> subst x <;> assumption
  have hup : u ≠ p := by intro h; subst p; simp [orient] at hupq
  have hpq : p ≠ q := by
    intro h; subst q; rw [orient_refl_right] at hupq; exact lt_irrefl _ hupq
  have hqv : q ≠ v := by
    intro h; subst v; rw [orient_refl_right] at hpqv; exact lt_irrefl _ hpqv
  have h1 : ∀ x ∈ T, 0 ≤ orient u p x := by
    intro x hx
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx <;> subst x
    · exact (orient_refl_left u p).ge
    · exact (orient_refl_right u p).ge
    · exact hupq.le
    · exact hupv.le
  have h2 : ∀ x ∈ T, 0 ≤ orient p q x := by
    intro x hx
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx <;> subst x
    · rw [← orient_rotate u p q]
      exact hupq.le
    · exact (orient_refl_left p q).ge
    · exact (orient_refl_right p q).ge
    · exact hpqv.le
  have h3 : ∀ x ∈ T, 0 ≤ orient q v x := by
    intro x hx
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx <;> subst x
    · rw [← orient_rotate u q v]
      exact huqv.le
    · rw [← orient_rotate p q v]
      exact hpqv.le
    · exact (orient_refl_left q v).ge
    · exact (orient_refl_right q v).ge
  apply convex_position_of_supported T
  intro x hx
  simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx <;> subst x
  · exact strictSupport_of_nonnegative_halfplane P T hgp hTP u p u
      (by simp [T]) (by simp [T]) hup (Or.inl rfl) h1
  · exact strictSupport_of_nonnegative_halfplane P T hgp hTP u p p
      (by simp [T]) (by simp [T]) hup (Or.inr rfl) h1
  · exact strictSupport_of_nonnegative_halfplane P T hgp hTP p q q
      (by simp [T]) (by simp [T]) hpq (Or.inr rfl) h2
  · exact strictSupport_of_nonnegative_halfplane P T hgp hTP q v v
      (by simp [T]) (by simp [T]) hqv (Or.inr rfl) h3

/-- The complete LOCAL edge-to-edge matching rule. Its remaining geometric
premise is precisely the annular-interior condition in Nicolas's definition
of a matching; neither emptiness nor convexity is postulated. -/
theorem hasEmptySix_of_matched_quad_channel
    (P K : Finset Point) (hgp : GeneralPosition P)
    (u p q v : Point)
    (hu : u ∈ inner P) (hp : p ∈ inner P)
    (hq : q ∈ inner P) (hv : v ∈ inner P)
    (hupq : 0 < orient u p q) (hupv : 0 < orient u p v)
    (huqv : 0 < orient u q v) (hpqv : 0 < orient p q v)
    (havoid : Disjoint
      (interior (convexHull ℝ ({u, p, q, v} : Set Point)))
      (convexHull ℝ ((hullVertices (inner (inner P)) : Finset Point) : Set Point)))
    (hinner : ∀ x ∈ inner P, orient u v x ≤ 0)
    (hK : K ⊆ hullVertices P)
    (hchannel : ∀ x ∈ K,
      0 < orient u p x ∧ 0 < orient p q x ∧ 0 < orient q v x)
    (hK2 : 2 ≤ K.card) : HasEmptySix P := by
  have hTsub : ({u, p, q, v} : Finset Point) ⊆ inner P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx <;> subst x <;> assumption
  have hTC := quad_convex_of_four_signs P hgp u p q v
    (Finset.mem_sdiff.mp hu).1 (Finset.mem_sdiff.mp hp).1
    (Finset.mem_sdiff.mp hq).1 (Finset.mem_sdiff.mp hv).1
    hupq hupv huqv hpqv
  have he := empty_polygon_of_annular_interior P {u, p, q, v} hTsub hTC
    (by simpa only [Finset.coe_insert, Finset.coe_singleton] using havoid)
  exact hasEmptySix_of_quad_channel P K hgp u p q v hu hp hq hv
    hupq hupv huqv hpqv he hinner hK hchannel hK2

end JSP198.Nicolas
