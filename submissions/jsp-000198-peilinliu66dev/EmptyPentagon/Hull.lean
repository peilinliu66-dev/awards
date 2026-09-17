/-
Ported from CollinYuanjieRen/awards, PR #283, commit
b8bb4f7803f921a7970abc880291ad9372111360,
submissions/jsp-000198-smallk-cyr/EmptyPentagon/.
Original Lean formalization: CollinYuanjieRen, with disclosed Claude Code assistance.
Copyright (c) 2026 The Justin Sun Prize contributors.
MIT license: see LICENSE in this directory. Changes for Lean 4.33.1 are
recorded in PORT_STATUS.md; theorem statements and mathematical meaning are retained.
Triangle-interior material also credits the MIT-licensed Horton campaign;
see LICENSE-HORTON and the original source comment.
-/

import EmptyPentagon.Definitions
import EmptyPentagon.Interp
import EmptyPentagon.TriangleInterior
import EmptyPentagon.Comparators

noncomputable section
open Classical
namespace Horton

/-- The hull vertices of a finite point set: its points that are extreme in its convex hull. -/
def hullVertices (S : Finset Point) : Finset Point :=
  S.filter (fun p => p ∈ (convexHull ℝ (S : Set Point)).extremePoints ℝ)

theorem hullVertices_subset (S : Finset Point) : hullVertices S ⊆ S :=
  Finset.filter_subset _ _

/-- As a set, the hull vertices are exactly the extreme points of the hull. -/
theorem coe_hullVertices (S : Finset Point) :
    ((hullVertices S : Finset Point) : Set Point) =
      (convexHull ℝ (S : Set Point)).extremePoints ℝ := by
  ext p
  simp only [Finset.mem_coe, hullVertices, Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨Finset.mem_coe.mp (extremePoints_convexHull_subset h), h⟩

/-- Finite Krein–Milman: the hull vertices span the same convex hull. -/
theorem convexHull_hullVertices (S : Finset Point) :
    convexHull ℝ ((hullVertices S : Finset Point) : Set Point) = convexHull ℝ (S : Set Point) := by
  rw [coe_hullVertices]
  have hcomp : IsCompact (convexHull ℝ (S : Set Point)) :=
    S.finite_toSet.isCompact_convexHull ℝ
  have hKM := closure_convexHull_extremePoints hcomp (convex_convexHull ℝ _)
  have hclosed :
      IsClosed (convexHull ℝ ((convexHull ℝ (S : Set Point)).extremePoints ℝ)) :=
    Set.Finite.isClosed_convexHull ℝ (S.finite_toSet.subset extremePoints_convexHull_subset)
  calc convexHull ℝ ((convexHull ℝ (S : Set Point)).extremePoints ℝ)
      = closure (convexHull ℝ ((convexHull ℝ (S : Set Point)).extremePoints ℝ)) :=
        hclosed.closure_eq.symm
    _ = convexHull ℝ (S : Set Point) := hKM

/-- Hull vertices are in convex position. -/
theorem convexIndependent_hullVertices (S : Finset Point) :
    ConvexIndependent ℝ (fun x : ((hullVertices S : Finset Point) : Set Point) => (x : Point)) := by
  have h := (convex_convexHull ℝ (S : Set Point)).convexIndependent_extremePoints
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at h ⊢
  rw [coe_hullVertices]
  exact h

/-- Three points of a segment have vanishing orientation. -/
theorem orient_eq_zero_of_mem_segment (a b x y z : Point) (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) (hz : z ∈ segment ℝ a b) : orient x y z = 0 := by
  rw [segment_eq_image'] at hx hy hz
  obtain ⟨s, -, rfl⟩ := hx
  obtain ⟨t, -, rfl⟩ := hy
  obtain ⟨u, -, rfl⟩ := hz
  simp only [orient, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub, smul_eq_mul]
  ring

/-- In general position, a point of `S` distinct from `x, y ∈ S` is not in the segment `[x, y]`. -/
theorem not_mem_convexHull_pair_of_generalPosition (S : Finset Point) (hgp : GeneralPosition S)
    (x y p : Point) (hx : x ∈ S) (hy : y ∈ S) (hp : p ∈ S) (hpx : p ≠ x) (hpy : p ≠ y)
    (h : p ∈ convexHull ℝ ({x, y} : Set Point)) : False := by
  rw [convexHull_pair] at h
  by_cases hxy : x = y
  · subst hxy
    rw [segment_same] at h
    exact hpx (Set.mem_singleton_iff.mp h)
  · exact hgp x hx y hy p hp hxy hpx.symm hpy.symm
      (orient_eq_zero_of_mem_segment x y x y p (left_mem_segment ℝ x y)
        (right_mem_segment ℝ x y) h)

/-- Carathéodory in the plane: a point of the hull of a finite set lies in a triangle of it. -/
theorem exists_triangle_of_mem_convexHull (T : Finset Point) (p : Point)
    (hp : p ∈ convexHull ℝ (T : Set Point)) :
    ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, p ∈ convexHull ℝ ({a, b, c} : Set Point) := by
  rw [convexHull_eq_union] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨t, ht, hai, hpt⟩ := hp
  have hcard : t.card ≤ 3 := by
    have h1 := hai.card_le_finrank_succ
    simp only [Fintype.card_coe] at h1
    have h2 := h1.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    have h3 : Module.finrank ℝ Point = 2 := by
      show Module.finrank ℝ (ℝ × ℝ) = 2
      simp [Module.finrank_prod, Module.finrank_self]
    omega
  have hpos : 1 ≤ t.card := by
    rcases t.eq_empty_or_nonempty with rfl | h
    · simp at hpt
    · exact h.card_pos
  obtain h1 | h2 | h3 : t.card = 1 ∨ t.card = 2 ∨ t.card = 3 := by omega
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    exact ⟨a, ht (by simp), a, ht (by simp), a, ht (by simp), convexHull_mono (by simp) hpt⟩
  · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h2
    exact ⟨a, ht (by simp), a, ht (by simp), b, ht (by simp),
      convexHull_mono (by simp) hpt⟩
  · obtain ⟨a, b, c, -, -, -, rfl⟩ := Finset.card_eq_three.mp h3
    exact ⟨a, ht (by simp), b, ht (by simp), c, ht (by simp),
      convexHull_mono (by simp) hpt⟩

/-- A point of `S` in a positively oriented triangle of `S`, distinct from its vertices, is
strictly inside it (general position). -/
theorem mem_interior_triangle_of_generalPosition (S : Finset Point) (hgp : GeneralPosition S)
    (a b c p : Point) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hp : p ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c)
    (habc : 0 < orient a b c) (hpabc : p ∈ convexHull ℝ ({a, b, c} : Set Point)) :
    p ∈ interior (convexHull ℝ ({a, b, c} : Set Point)) := by
  have h1 : orient a b p ≠ 0 := hgp a ha b hb p hp hab hpa.symm hpb.symm
  have h2 : orient b c p ≠ 0 := hgp b hb c hc p hp hbc hpb.symm hpc.symm
  have h3 : orient c a p ≠ 0 := hgp c hc a ha p hp hac.symm hpc.symm hpa.symm
  obtain ⟨g1, g2, g3⟩ := orient_pos_of_mem_convexHull_triangle a b c p habc hpabc h1 h2 h3
  exact mem_interior_triangle_of_orient_pos a b c p habc g1 g2 g3

/-- In general position, every non-vertex point of `S` is strictly inside the hull of the
vertices. -/
theorem mem_interior_hullVertices_of_not_mem (S : Finset Point) (hgp : GeneralPosition S)
    (p : Point) (hp : p ∈ S) (hnot : p ∉ hullVertices S) :
    p ∈ interior (convexHull ℝ ((hullVertices S : Finset Point) : Set Point)) := by
  have hsub : hullVertices S ⊆ S := hullVertices_subset S
  have hpH : p ∈ convexHull ℝ ((hullVertices S : Finset Point) : Set Point) := by
    rw [convexHull_hullVertices]
    exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hp)
  obtain ⟨a, ha, b, hb, c, hc, hpabc⟩ := exists_triangle_of_mem_convexHull (hullVertices S) p hpH
  have hpa : p ≠ a := fun h => hnot (h ▸ ha)
  have hpb : p ≠ b := fun h => hnot (h ▸ hb)
  have hpc : p ≠ c := fun h => hnot (h ▸ hc)
  have haS := hsub ha
  have hbS := hsub hb
  have hcS := hsub hc
  -- Degenerate triangles put `p` on a segment between points of `S`, impossible.
  by_cases hab : a = b
  · subst hab
    exact (not_mem_convexHull_pair_of_generalPosition S hgp a c p haS hcS hp hpa hpc
      (convexHull_mono (by simp) hpabc)).elim
  by_cases hac : a = c
  · subst hac
    exact (not_mem_convexHull_pair_of_generalPosition S hgp a b p haS hbS hp hpa hpb
      (convexHull_mono (by simp [Set.insert_subset_iff]) hpabc)).elim
  by_cases hbc : b = c
  · subst hbc
    exact (not_mem_convexHull_pair_of_generalPosition S hgp a b p haS hbS hp hpa hpb
      (convexHull_mono (by simp) hpabc)).elim
  have habc : orient a b c ≠ 0 := hgp a haS b hbS c hcS hab hac hbc
  have hint : p ∈ interior (convexHull ℝ ({a, b, c} : Set Point)) := by
    rcases lt_or_gt_of_ne habc with hneg | hpos
    · have hpos' : 0 < orient a c b := by
        have : orient a c b = -orient a b c := by unfold orient; ring
        linarith
      have hcomm : ({a, b, c} : Set Point) = {a, c, b} := by rw [Set.pair_comm]
      rw [hcomm] at hpabc ⊢
      exact mem_interior_triangle_of_generalPosition S hgp a c b p haS hcS hbS hp hac hab
        (Ne.symm hbc) hpa hpc hpb hpos' hpabc
    · exact mem_interior_triangle_of_generalPosition S hgp a b c p haS hbS hcS hp hab hac hbc
        hpa hpb hpc hpos hpabc
  exact interior_mono (convexHull_mono (by simp [Set.insert_subset_iff, ha, hb, hc])) hint

/-- In general position a set of at least three points has at least three hull vertices. -/
theorem three_le_card_hullVertices (S : Finset Point) (hgp : GeneralPosition S)
    (h3 : 3 ≤ S.card) : 3 ≤ (hullVertices S).card := by
  by_contra hlt
  have hlt' := Nat.lt_of_not_le hlt
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp (by omega : 2 < S.card)
  have hmem : ∀ q ∈ S, q ∈ convexHull ℝ ((hullVertices S : Finset Point) : Set Point) := by
    intro q hq
    rw [convexHull_hullVertices]
    exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hq)
  have hx' := hmem x hx
  have hy' := hmem y hy
  have hz' := hmem z hz
  obtain h0 | h1 | h2 :
      (hullVertices S).card = 0 ∨ (hullVertices S).card = 1 ∨ (hullVertices S).card = 2 := by
    omega
  · rw [Finset.card_eq_zero] at h0
    rw [h0] at hx'
    simp at hx'
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    rw [ha, Finset.coe_singleton, convexHull_singleton] at hx' hy'
    exact hxy ((Set.mem_singleton_iff.mp hx').trans (Set.mem_singleton_iff.mp hy').symm)
  · obtain ⟨a, b, -, hab⟩ := Finset.card_eq_two.mp h2
    rw [hab, Finset.coe_pair, convexHull_pair] at hx' hy' hz'
    exact hgp x hx y hy z hz hxy hxz hyz (orient_eq_zero_of_mem_segment a b x y z hx' hy' hz')

end Horton

#print axioms Horton.coe_hullVertices
#print axioms Horton.convexHull_hullVertices
#print axioms Horton.convexIndependent_hullVertices
#print axioms Horton.mem_interior_hullVertices_of_not_mem
#print axioms Horton.three_le_card_hullVertices
