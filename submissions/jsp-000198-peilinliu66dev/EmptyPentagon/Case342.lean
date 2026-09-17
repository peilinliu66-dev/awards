/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Case342.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Beam
import EmptyPentagon.Quad
import EmptyPentagon.Cover342
import EmptyPentagon.Chord
import EmptyPentagon.Interp
import EmptyPentagon.FourOuter

noncomputable section
namespace Horton

/-- The vertices of a counterclockwise convex quadrilateral are in convex position. -/
theorem convexIndependent_quad (w1 w2 w3 w4 : Point) (h1 : 0 < orient w1 w2 w3)
    (h2 : 0 < orient w2 w3 w4) (h3 : 0 < orient w3 w4 w1) (h4 : 0 < orient w4 w1 w2) :
    ConvexIndependent ℝ
      (fun x : (({w1, w2, w3, w4} : Finset Point) : Set Point) => (x : Point)) := by
  obtain ⟨-, h13, -⟩ := ne_of_orient_ne_zero w1 w2 w3 h1.ne'
  obtain ⟨-, h24, -⟩ := ne_of_orient_ne_zero w2 w3 w4 h2.ne'
  obtain ⟨-, h31, -⟩ := ne_of_orient_ne_zero w3 w4 w1 h3.ne'
  refine convexIndependent_of_separated _ ?_
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · refine ⟨w4, by simp, w2, by simp, h24.symm, by rw [orient_swap_right]; linarith, ?_⟩
    intro x hx hxv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact absurd rfl hxv
    · exact (orient_right_self _ _).ge
    · rw [orient_cyc]; exact h2.le
    · exact (orient_left_self _ _).ge
  · refine ⟨w1, by simp, w3, by simp, h13, by rw [orient_swap_right]; linarith, ?_⟩
    intro x hx hxv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (orient_left_self _ _).ge
    · exact absurd rfl hxv
    · exact (orient_right_self _ _).ge
    · rw [orient_cyc]; exact h3.le
  · refine ⟨w2, by simp, w4, by simp, h24, by rw [orient_swap_right]; linarith, ?_⟩
    intro x hx hxv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [orient_cyc]; exact h4.le
    · exact (orient_left_self _ _).ge
    · exact absurd rfl hxv
    · exact (orient_right_self _ _).ge
  · refine ⟨w3, by simp, w1, by simp, h31, by rw [orient_swap_right]; linarith, ?_⟩
    intro x hx hxv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (orient_right_self _ _).ge
    · rw [orient_cyc]; exact h1.le
    · exact (orient_left_self _ _).ge
    · exact absurd rfl hxv

/-- A point strictly inside a counterclockwise convex quadrilateral and off the diagonal line
`w1 w3` lies in the closed quadrilateral. -/
theorem mem_convexHull_quad (w1 w2 w3 w4 z : Point) (h1 : 0 < orient w1 w2 w3)
    (h3 : 0 < orient w3 w4 w1) (hd : orient w1 w3 z ≠ 0) (k1 : 0 < orient w1 w2 z)
    (k2 : 0 < orient w2 w3 z) (k3 : 0 < orient w3 w4 z) (k4 : 0 < orient w4 w1 z) :
    z ∈ convexHull ℝ ({w1, w2, w3, w4} : Set Point) := by
  rcases hd.lt_or_gt with h | h
  · have h31 : 0 < orient w3 w1 z := by rw [orient_swap_left]; linarith
    refine convexHull_mono ?_
      (interior_subset (mem_interior_triangle_of_orient_pos w1 w2 w3 z h1 k1 k2 h31))
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  · have hT : 0 < orient w1 w3 w4 := by rw [orient_cyc]; exact h3
    refine convexHull_mono ?_
      (interior_subset (mem_interior_triangle_of_orient_pos w1 w3 w4 z hT h k3 k4))
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto

/-- The `1–3` split: the first three vertices of a counterclockwise convex quadrilateral lie
strictly left of the line `p → q` through two points of the closed quadrilateral. -/
theorem five_of_line_split (S : Finset Point) (v1 v2 v3 v4 p q : Point)
    (h1 : 0 < orient v1 v2 v3) (h2 : 0 < orient v2 v3 v4) (h3 : 0 < orient v3 v4 v1)
    (h4 : 0 < orient v4 v1 v2) (hv1 : v1 ∈ S) (hv2 : v2 ∈ S) (hv3 : v3 ∈ S) (hpS : p ∈ S)
    (hqS : q ∈ S) (h1p : v1 ≠ p) (h2p : v2 ≠ p) (h3p : v3 ≠ p) (h1q : v1 ≠ q) (h2q : v2 ≠ q)
    (h3q : v3 ≠ q) (hpq : p ≠ q) (hph : p ∈ convexHull ℝ ({v1, v2, v3, v4} : Set Point))
    (hqh : q ∈ convexHull ℝ ({v1, v2, v3, v4} : Set Point)) (k1 : 0 < orient p q v1)
    (k2 : 0 < orient p q v2) (k3 : 0 < orient p q v3) :
    ∃ V : Finset Point, V ⊆ S ∧ V.card = 5 ∧
      ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)) := by
  classical
  obtain ⟨h12, h13, h23⟩ := ne_of_orient_ne_zero v1 v2 v3 h1.ne'
  have hcoe : ((({v1, v2, v3, v4} : Finset Point)) : Set Point) = ({v1, v2, v3, v4} : Set Point) :=
    by simp
  have hph' : p ∈ convexHull ℝ ((({v1, v2, v3, v4} : Finset Point)) : Set Point) := by
    rw [hcoe]; exact hph
  have hqh' : q ∈ convexHull ℝ ((({v1, v2, v3, v4} : Finset Point)) : Set Point) := by
    rw [hcoe]; exact hqh
  refine ⟨{v1, v2, v3, p, q}, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [Finset.card_insert_of_notMem (by simp [h12, h13, h1p, h1q]),
      Finset.card_insert_of_notMem (by simp [h23, h2p, h2q]),
      Finset.card_insert_of_notMem (by simp [h3p, h3q]),
      Finset.card_insert_of_notMem (by simp [hpq]), Finset.card_singleton]
  · exact convexIndependent_line_five {v1, v2, v3, v4}
      (convexIndependent_quad v1 v2 v3 v4 h1 h2 h3 h4) v1 v2 v3 p q (by simp) (by simp) (by simp)
      h12 h13 h23 hph' hqh' hpq k1 k2 k3

/-- Normalised form of Bonnice's `(3,4,2)` case: the line `z1 → z2` has the vertices `w1, w2`
strictly on its right and `w3, w4` strictly on its left. -/
theorem case_342_core (S : Finset Point) (hgp : GeneralPosition S) (H : Finset Point)
    (hHS : H ⊆ S) (hH : ConvexIndependent ℝ (fun x : (H : Set Point) => (x : Point)))
    (h3 : 3 ≤ H.card) (w1 w2 w3 w4 z1 z2 : Point) (hw1 : w1 ∈ S) (hw2 : w2 ∈ S) (hw3 : w3 ∈ S)
    (hw4 : w4 ∈ S) (hz1S : z1 ∈ S) (hz2S : z2 ∈ S)
    (hq1 : 0 < orient w1 w2 w3) (hq2 : 0 < orient w2 w3 w4) (hq3 : 0 < orient w3 w4 w1)
    (hq4 : 0 < orient w4 w1 w2)
    (hz11 : 0 < orient w1 w2 z1) (hz12 : 0 < orient w2 w3 z1) (hz13 : 0 < orient w3 w4 z1)
    (hz14 : 0 < orient w4 w1 z1) (hz21 : 0 < orient w1 w2 z2) (hz22 : 0 < orient w2 w3 z2)
    (hz23 : 0 < orient w3 w4 z2) (hz24 : 0 < orient w4 w1 z2)
    (hl1 : orient z1 z2 w1 < 0) (hl2 : orient z1 z2 w2 < 0) (hl3 : 0 < orient z1 z2 w3)
    (hl4 : 0 < orient z1 z2 w4)
    (hy : ∀ y ∈ H, orient w1 w2 y < 0 ∨ orient w2 w3 y < 0 ∨ orient w3 w4 y < 0 ∨
      orient w4 w1 y < 0)
    (hw1H : w1 ∈ convexHull ℝ (H : Set Point)) (hw2H : w2 ∈ convexHull ℝ (H : Set Point))
    (hw3H : w3 ∈ convexHull ℝ (H : Set Point)) (hw4H : w4 ∈ convexHull ℝ (H : Set Point))
    (hz1H : z1 ∈ convexHull ℝ (H : Set Point)) (hz2H : z2 ∈ convexHull ℝ (H : Set Point)) :
    ∃ V : Finset Point, V ⊆ S ∧ V.card = 5 ∧
      ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)) := by
  classical
  obtain ⟨h12, -, -⟩ := ne_of_orient_ne_zero w1 w2 w3 hq1.ne'
  obtain ⟨-, -, h34⟩ := ne_of_orient_ne_zero w2 w3 w4 hq2.ne'
  obtain ⟨-, h1z1, h2z1⟩ := ne_of_orient_ne_zero w1 w2 z1 hz11.ne'
  obtain ⟨-, h3z1, h4z1⟩ := ne_of_orient_ne_zero w3 w4 z1 hz13.ne'
  obtain ⟨-, h1z2, h2z2⟩ := ne_of_orient_ne_zero w1 w2 z2 hz21.ne'
  obtain ⟨-, h3z2, h4z2⟩ := ne_of_orient_ne_zero w3 w4 z2 hz23.ne'
  obtain ⟨hzz, -, -⟩ := ne_of_orient_ne_zero z1 z2 w1 hl1.ne
  have hyne : ∀ y ∈ H, w1 ≠ y ∧ w2 ≠ y ∧ w3 ≠ y ∧ w4 ≠ y ∧ z1 ≠ y ∧ z2 ≠ y := by
    intro y hyH
    have hy' := hy y hyH
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> rcases hy' with k | k | k | k <;>
      unfold orient at k hq1 hq2 hq3 hq4 hz11 hz12 hz13 hz14 hz21 hz22 hz23 hz24 <;> linarith
  have hcov : ∀ y ∈ H,
      (0 < orient z2 w2 y ∧ 0 < orient z2 y w3 ∧ orient w2 w3 y < 0) ∨
      (0 < orient z1 w4 y ∧ 0 < orient z1 y w1 ∧ orient w4 w1 y < 0) ∨
      (orient w3 w4 y < 0 ∧ orient z1 w4 y < 0 ∧ 0 < orient z2 w3 y) ∨
      (orient w1 w2 y < 0 ∧ orient z2 w2 y < 0 ∧ 0 < orient z1 w1 y) := by
    intro y hyH
    have hyS : y ∈ S := hHS hyH
    have hsub : ({w1, w2, w3, w4, z1, z2, y} : Finset Point) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    exact cover_342 w1 w2 w3 w4 z1 z2 y
      (fun a ha b hb c hc => hgp a (hsub ha) b (hsub hb) c (hsub hc)) hq1 hq2 hq3 hq4
      ⟨hz11, hz12, hz13, hz14⟩ ⟨hz21, hz22, hz23, hz24⟩ hl1 hl2 hl3 hl4 (hy y hyH)
  by_cases hs3 : ∃ y ∈ H, orient w3 w4 y < 0 ∧ orient z1 w4 y < 0 ∧ 0 < orient z2 w3 y
  · -- a hull vertex lands in the strip beyond `w3 w4`: `z1, z2, w3, y, w4` is a convex pentagon
    obtain ⟨y, hyH, k1, k2, k3⟩ := hs3
    obtain ⟨-, -, hw3y, hw4y, hz1y, hz2y⟩ := hyne y hyH
    have hyS : y ∈ S := hHS hyH
    have hinj : Function.Injective ![z1, z2, w3, w4, y] :=
      injective_vec5 z1 z2 w3 w4 y hzz h3z1.symm h4z1.symm hz1y h3z2.symm h4z2.symm hz2y h34
        hw3y hw4y
    have hpS : ∀ i : Fin 5, ![z1, z2, w3, w4, y] i ∈ S := by
      intro i
      fin_cases i
      · exact hz1S
      · exact hz2S
      · exact hw3
      · exact hw4
      · exact hyS
    refine ⟨Finset.univ.image ![z1, z2, w3, w4, y], ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact hpS i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · exact convexIndependent_strip _ (indexedGP_of_injective S hgp _ hpS hinj) hinj hl3 hl4
        hz13 hz23 k1 k2 k3
  by_cases hs1 : ∃ y ∈ H, orient w1 w2 y < 0 ∧ orient z2 w2 y < 0 ∧ 0 < orient z1 w1 y
  · -- a hull vertex lands in the strip beyond `w1 w2`: `z2, z1, w1, y, w2` is a convex pentagon
    obtain ⟨y, hyH, k1, k2, k3⟩ := hs1
    obtain ⟨hw1y, hw2y, -, -, hz1y, hz2y⟩ := hyne y hyH
    have hyS : y ∈ S := hHS hyH
    have sl1 : 0 < orient z2 z1 w1 := by rw [orient_swap_left]; linarith
    have sl2 : 0 < orient z2 z1 w2 := by rw [orient_swap_left]; linarith
    have hinj : Function.Injective ![z2, z1, w1, w2, y] :=
      injective_vec5 z2 z1 w1 w2 y hzz.symm h1z2.symm h2z2.symm hz2y h1z1.symm h2z1.symm hz1y h12
        hw1y hw2y
    have hpS : ∀ i : Fin 5, ![z2, z1, w1, w2, y] i ∈ S := by
      intro i
      fin_cases i
      · exact hz2S
      · exact hz1S
      · exact hw1
      · exact hw2
      · exact hyS
    refine ⟨Finset.univ.image ![z2, z1, w1, w2, y], ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact hpS i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · exact convexIndependent_strip _ (indexedGP_of_injective S hgp _ hpS hinj) hinj sl1 sl2
        hz21 hz11 k1 k2 k3
  -- every hull vertex sits in one of the two cones; pigeonhole and run the beam argument
  push Not at hs3 hs1
  have hcov2 : ∀ y ∈ H,
      (0 < orient z2 w2 y ∧ 0 < orient z2 y w3 ∧ orient w2 w3 y < 0) ∨
      (0 < orient z1 w4 y ∧ 0 < orient z1 y w1 ∧ orient w4 w1 y < 0) := by
    intro y hyH
    rcases hcov y hyH with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h.2.2 (not_lt.2 (hs3 y hyH h.1 h.2.1))
    · exact absurd h.2.2 (not_lt.2 (hs1 y hyH h.1 h.2.1))
  have hc : (Finset.univ : Finset (Fin 2)).card < H.card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨ya, hya, yb, hyb, hneab, hf⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc
      (f := fun y : Point ↦
        if 0 < orient z2 w2 y ∧ 0 < orient z2 y w3 ∧ orient w2 w3 y < 0 then (0 : Fin 2) else 1)
      (fun a _ ↦ Finset.mem_univ _)
  by_cases c1 : 0 < orient z2 w2 ya ∧ 0 < orient z2 ya w3 ∧ orient w2 w3 ya < 0
  · by_cases d1 : 0 < orient z2 w2 yb ∧ 0 < orient z2 yb w3 ∧ orient w2 w3 yb < 0
    · exact beam_of_same_cone S hgp H hHS hH w2 w3 z2 ya yb hw2 hw3 hz2S hya hyb hneab hz22
        hw2H hw3H hz2H c1 d1
    · exfalso
      rw [if_pos c1, if_neg d1] at hf
      exact absurd hf (by decide)
  · by_cases d1 : 0 < orient z2 w2 yb ∧ 0 < orient z2 yb w3 ∧ orient w2 w3 yb < 0
    · exfalso
      rw [if_neg c1, if_pos d1] at hf
      exact absurd hf (by decide)
    · exact beam_of_same_cone S hgp H hHS hH w4 w1 z1 ya yb hw4 hw1 hz1S hya hyb hneab hz14
        hw4H hw1H hz1H ((hcov2 ya hya).resolve_left c1) ((hcov2 yb hyb).resolve_left d1)

/-- Bonnice's `(3,4,2)` case: at least three hull vertices `H`, an inner counterclockwise convex
quadrilateral with two points strictly inside, everything inside the hull of `H`, no vertex of `H`
in the closed inner quadrilateral. Then `S` contains five points in convex position. -/
theorem case_342 (S : Finset Point) (hgp : GeneralPosition S)
    (H : Finset Point) (hHS : H ⊆ S)
    (hH : ConvexIndependent ℝ (fun x : (H : Set Point) => (x : Point))) (h3 : 3 ≤ H.card)
    (w1 w2 w3 w4 z1 z2 : Point) (hw1 : w1 ∈ S) (hw2 : w2 ∈ S) (hw3 : w3 ∈ S) (hw4 : w4 ∈ S)
    (hz1S : z1 ∈ S) (hz2S : z2 ∈ S) (hne : z1 ≠ z2)
    (hq1 : 0 < orient w1 w2 w3) (hq2 : 0 < orient w2 w3 w4) (hq3 : 0 < orient w3 w4 w1)
    (hq4 : 0 < orient w4 w1 w2)
    (hz1 : 0 < orient w1 w2 z1 ∧ 0 < orient w2 w3 z1 ∧ 0 < orient w3 w4 z1 ∧ 0 < orient w4 w1 z1)
    (hz2 : 0 < orient w1 w2 z2 ∧ 0 < orient w2 w3 z2 ∧ 0 < orient w3 w4 z2 ∧ 0 < orient w4 w1 z2)
    (hout : ∀ y ∈ H, y ∉ convexHull ℝ ({w1, w2, w3, w4} : Set Point))
    (hin : ({w1, w2, w3, w4, z1, z2} : Set Point) ⊆ convexHull ℝ (H : Set Point)) :
    ∃ V : Finset Point, V ⊆ S ∧ V.card = 5 ∧
      ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)) := by
  classical
  obtain ⟨hz11, hz12, hz13, hz14⟩ := hz1
  obtain ⟨hz21, hz22, hz23, hz24⟩ := hz2
  obtain ⟨h12, h13, h23⟩ := ne_of_orient_ne_zero w1 w2 w3 hq1.ne'
  obtain ⟨-, -, h34⟩ := ne_of_orient_ne_zero w2 w3 w4 hq2.ne'
  obtain ⟨-, -, h41⟩ := ne_of_orient_ne_zero w3 w4 w1 hq3.ne'
  obtain ⟨-, h1z1, h2z1⟩ := ne_of_orient_ne_zero w1 w2 z1 hz11.ne'
  obtain ⟨-, h3z1, h4z1⟩ := ne_of_orient_ne_zero w3 w4 z1 hz13.ne'
  obtain ⟨-, h1z2, h2z2⟩ := ne_of_orient_ne_zero w1 w2 z2 hz21.ne'
  obtain ⟨-, h3z2, h4z2⟩ := ne_of_orient_ne_zero w3 w4 z2 hz23.ne'
  have hw1H : w1 ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have hw2H : w2 ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have hw3H : w3 ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have hw4H : w4 ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have hz1H : z1 ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have hz2H : z2 ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have hz1Q : z1 ∈ convexHull ℝ ({w1, w2, w3, w4} : Set Point) :=
    mem_convexHull_quad w1 w2 w3 w4 z1 hq1 hq3 (hgp w1 hw1 w3 hw3 z1 hz1S h13 h1z1 h3z1) hz11
      hz12 hz13 hz14
  have hz2Q : z2 ∈ convexHull ℝ ({w1, w2, w3, w4} : Set Point) :=
    mem_convexHull_quad w1 w2 w3 w4 z2 hq1 hq3 (hgp w1 hw1 w3 hw3 z2 hz2S h13 h1z2 h3z2) hz21
      hz22 hz23 hz24
  have hr2 : ({w2, w3, w4, w1} : Set Point) = {w1, w2, w3, w4} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hr3 : ({w3, w4, w1, w2} : Set Point) = {w1, w2, w3, w4} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hr4 : ({w4, w1, w2, w3} : Set Point) = {w1, w2, w3, w4} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hz1Q2 : z1 ∈ convexHull ℝ ({w2, w3, w4, w1} : Set Point) := by rw [hr2]; exact hz1Q
  have hz2Q2 : z2 ∈ convexHull ℝ ({w2, w3, w4, w1} : Set Point) := by rw [hr2]; exact hz2Q
  have hz1Q3 : z1 ∈ convexHull ℝ ({w3, w4, w1, w2} : Set Point) := by rw [hr3]; exact hz1Q
  have hz2Q3 : z2 ∈ convexHull ℝ ({w3, w4, w1, w2} : Set Point) := by rw [hr3]; exact hz2Q
  have hz1Q4 : z1 ∈ convexHull ℝ ({w4, w1, w2, w3} : Set Point) := by rw [hr4]; exact hz1Q
  have hz2Q4 : z2 ∈ convexHull ℝ ({w4, w1, w2, w3} : Set Point) := by rw [hr4]; exact hz2Q
  -- every hull vertex lies strictly beyond one of the four sides
  have hycov : ∀ y ∈ H, orient w1 w2 y < 0 ∨ orient w2 w3 y < 0 ∨ orient w3 w4 y < 0 ∨
      orient w4 w1 y < 0 := by
    intro y hyH
    by_contra hcon
    push Not at hcon
    obtain ⟨c1, c2, c3, c4⟩ := hcon
    have hyS : y ∈ S := hHS hyH
    have e1 : w1 ≠ y := fun h ↦ hout y hyH (h ▸ subset_convexHull ℝ _ (by simp : w1 ∈ _))
    have e2 : w2 ≠ y := fun h ↦ hout y hyH (h ▸ subset_convexHull ℝ _ (by simp : w2 ∈ _))
    have e3 : w3 ≠ y := fun h ↦ hout y hyH (h ▸ subset_convexHull ℝ _ (by simp : w3 ∈ _))
    have e4 : w4 ≠ y := fun h ↦ hout y hyH (h ▸ subset_convexHull ℝ _ (by simp : w4 ∈ _))
    exact hout y hyH (mem_convexHull_quad w1 w2 w3 w4 y hq1 hq3
      (hgp w1 hw1 w3 hw3 y hyS h13 e1 e3)
      (lt_of_le_of_ne c1 (hgp w1 hw1 w2 hw2 y hyS h12 e1 e2).symm)
      (lt_of_le_of_ne c2 (hgp w2 hw2 w3 hw3 y hyS h23 e2 e3).symm)
      (lt_of_le_of_ne c3 (hgp w3 hw3 w4 hw4 y hyS h34 e3 e4).symm)
      (lt_of_le_of_ne c4 (hgp w4 hw4 w1 hw1 y hyS h41 e4 e1).symm))
  -- an interior point of the quadrilateral cannot see all four vertices strictly on one side
  have key : ∀ u v : Point, u ∈ convexHull ℝ ({w1, w2, w3, w4} : Set Point) →
      0 < orient u v w1 → 0 < orient u v w2 → 0 < orient u v w3 → 0 < orient u v w4 → False := by
    intro u v hu k1 k2 k3 k4
    have hsub : convexHull ℝ ({w1, w2, w3, w4} : Set Point) ⊆ {x : Point | 0 < orient u v x} := by
      refine convexHull_min ?_ (convex_strict_halfplane u v)
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact k1
      · exact k2
      · exact k3
      · exact k4
    have hcon := hsub hu
    simp only [Set.mem_ofPred_eq, orient_left_self] at hcon
    exact lt_irrefl 0 hcon
  have sw : ∀ w : Point, orient z2 z1 w = -orient z1 z2 w := fun w ↦ orient_swap_left z1 z2 w
  have s1 : orient z1 z2 w1 ≠ 0 := hgp z1 hz1S z2 hz2S w1 hw1 hne h1z1.symm h1z2.symm
  have s2 : orient z1 z2 w2 ≠ 0 := hgp z1 hz1S z2 hz2S w2 hw2 hne h2z1.symm h2z2.symm
  have s3 : orient z1 z2 w3 ≠ 0 := hgp z1 hz1S z2 hz2S w3 hw3 hne h3z1.symm h3z2.symm
  have s4 : orient z1 z2 w4 ≠ 0 := hgp z1 hz1S z2 hz2S w4 hw4 hne h4z1.symm h4z2.symm
  rcases Ne.lt_or_gt s1 with a1 | a1 <;> rcases Ne.lt_or_gt s2 with a2 | a2 <;>
    rcases Ne.lt_or_gt s3 with a3 | a3 <;> rcases Ne.lt_or_gt s4 with a4 | a4
  · -- all four vertices right of `z1 → z2`: impossible
    exact (key z2 z1 hz2Q (by rw [sw]; linarith) (by rw [sw]; linarith) (by rw [sw]; linarith)
      (by rw [sw]; linarith)).elim
  · -- `w1, w2, w3` left of `z2 → z1`
    exact five_of_line_split S w1 w2 w3 w4 z2 z1 hq1 hq2 hq3 hq4 hw1 hw2 hw3 hz2S hz1S h1z2 h2z2
      h3z2 h1z1 h2z1 h3z1 hne.symm hz2Q hz1Q (by rw [sw]; linarith) (by rw [sw]; linarith)
      (by rw [sw]; linarith)
  · -- `w4, w1, w2` left of `z2 → z1`
    exact five_of_line_split S w4 w1 w2 w3 z2 z1 hq4 hq1 hq2 hq3 hw4 hw1 hw2 hz2S hz1S h4z2 h1z2
      h2z2 h4z1 h1z1 h2z1 hne.symm hz2Q4 hz1Q4 (by rw [sw]; linarith) (by rw [sw]; linarith)
      (by rw [sw]; linarith)
  · -- `2–2` split, already normalised
    exact case_342_core S hgp H hHS hH h3 w1 w2 w3 w4 z1 z2 hw1 hw2 hw3 hw4 hz1S hz2S hq1 hq2 hq3
      hq4 hz11 hz12 hz13 hz14 hz21 hz22 hz23 hz24 a1 a2 a3 a4 hycov hw1H hw2H hw3H hw4H hz1H hz2H
  · -- `w3, w4, w1` left of `z2 → z1`
    exact five_of_line_split S w3 w4 w1 w2 z2 z1 hq3 hq4 hq1 hq2 hw3 hw4 hw1 hz2S hz1S h3z2 h4z2
      h1z2 h3z1 h4z1 h1z1 hne.symm hz2Q3 hz1Q3 (by rw [sw]; linarith) (by rw [sw]; linarith)
      (by rw [sw]; linarith)
  · -- alternating signs: impossible
    exact (not_alternating w1 w2 w3 w4 z1 z2 hq1 hq2 hq3 hq4 ⟨a1, a2, a3, a4⟩).elim
  · -- `2–2` split after one rotation
    exact case_342_core S hgp H hHS hH h3 w4 w1 w2 w3 z1 z2 hw4 hw1 hw2 hw3 hz1S hz2S hq4 hq1 hq2
      hq3 hz14 hz11 hz12 hz13 hz24 hz21 hz22 hz23 a4 a1 a2 a3
      (fun y hyH ↦ by have h := hycov y hyH; tauto) hw4H hw1H hw2H hw3H hz1H hz2H
  · -- `w2, w3, w4` left of `z1 → z2`
    exact five_of_line_split S w2 w3 w4 w1 z1 z2 hq2 hq3 hq4 hq1 hw2 hw3 hw4 hz1S hz2S h2z1 h3z1
      h4z1 h2z2 h3z2 h4z2 hne hz1Q2 hz2Q2 a2 a3 a4
  · -- `w2, w3, w4` left of `z2 → z1`
    exact five_of_line_split S w2 w3 w4 w1 z2 z1 hq2 hq3 hq4 hq1 hw2 hw3 hw4 hz2S hz1S h2z2 h3z2
      h4z2 h2z1 h3z1 h4z1 hne.symm hz2Q2 hz1Q2 (by rw [sw]; linarith) (by rw [sw]; linarith)
      (by rw [sw]; linarith)
  · -- `2–2` split after one rotation
    exact case_342_core S hgp H hHS hH h3 w2 w3 w4 w1 z1 z2 hw2 hw3 hw4 hw1 hz1S hz2S hq2 hq3 hq4
      hq1 hz12 hz13 hz14 hz11 hz22 hz23 hz24 hz21 a2 a3 a4 a1
      (fun y hyH ↦ by have h := hycov y hyH; tauto) hw2H hw3H hw4H hw1H hz1H hz2H
  · -- alternating signs after swapping `z1, z2`: impossible
    exact (not_alternating w1 w2 w3 w4 z2 z1 hq1 hq2 hq3 hq4
      ⟨by rw [sw]; linarith, by rw [sw]; linarith, by rw [sw]; linarith,
        by rw [sw]; linarith⟩).elim
  · -- `w3, w4, w1` left of `z1 → z2`
    exact five_of_line_split S w3 w4 w1 w2 z1 z2 hq3 hq4 hq1 hq2 hw3 hw4 hw1 hz1S hz2S h3z1 h4z1
      h1z1 h3z2 h4z2 h1z2 hne hz1Q3 hz2Q3 a3 a4 a1
  · -- `2–2` split after two rotations
    exact case_342_core S hgp H hHS hH h3 w3 w4 w1 w2 z1 z2 hw3 hw4 hw1 hw2 hz1S hz2S hq3 hq4 hq1
      hq2 hz13 hz14 hz11 hz12 hz23 hz24 hz21 hz22 a3 a4 a1 a2
      (fun y hyH ↦ by have h := hycov y hyH; tauto) hw3H hw4H hw1H hw2H hz1H hz2H
  · -- `w4, w1, w2` left of `z1 → z2`
    exact five_of_line_split S w4 w1 w2 w3 z1 z2 hq4 hq1 hq2 hq3 hw4 hw1 hw2 hz1S hz2S h4z1 h1z1
      h2z1 h4z2 h1z2 h2z2 hne hz1Q4 hz2Q4 a4 a1 a2
  · -- `w1, w2, w3` left of `z1 → z2`
    exact five_of_line_split S w1 w2 w3 w4 z1 z2 hq1 hq2 hq3 hq4 hw1 hw2 hw3 hz1S hz2S h1z1 h2z1
      h3z1 h1z2 h2z2 h3z2 hne hz1Q hz2Q a1 a2 a3
  · -- all four vertices left of `z1 → z2`: impossible
    exact (key z1 z2 hz1Q a1 a2 a3 a4).elim

end Horton
