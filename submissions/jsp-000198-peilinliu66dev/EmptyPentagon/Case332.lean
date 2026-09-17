/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Case332.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Beam
import EmptyPentagon.Cover332
import EmptyPentagon.Chord
import EmptyPentagon.Interp
import EmptyPentagon.FourOuter

noncomputable section
namespace Horton

/-- Normalised form of Bonnice's `(3,3,2)` case: the line `z1 → z2` has the vertex `v1` strictly
on its right and the two vertices `v2, v3` strictly on its left. -/
theorem case_332_core (S : Finset Point) (hgp : GeneralPosition S)
    (H : Finset Point) (hHS : H ⊆ S)
    (hH : ConvexIndependent ℝ (fun x : (H : Set Point) => (x : Point))) (h3 : 3 ≤ H.card)
    (v1 v2 v3 z1 z2 : Point) (hv1 : v1 ∈ S) (hv2 : v2 ∈ S) (hv3 : v3 ∈ S)
    (hz1S : z1 ∈ S) (hz2S : z2 ∈ S) (ht : 0 < orient v1 v2 v3)
    (hz1 : 0 < orient v1 v2 z1 ∧ 0 < orient v2 v3 z1 ∧ 0 < orient v3 v1 z1)
    (hz2 : 0 < orient v1 v2 z2 ∧ 0 < orient v2 v3 z2 ∧ 0 < orient v3 v1 z2)
    (hl1 : orient z1 z2 v1 < 0) (hl2 : 0 < orient z1 z2 v2) (hl3 : 0 < orient z1 z2 v3)
    (hout : ∀ y ∈ H, y ∉ convexHull ℝ ({v1, v2, v3} : Set Point))
    (hv1H : v1 ∈ convexHull ℝ (H : Set Point)) (hv2H : v2 ∈ convexHull ℝ (H : Set Point))
    (hv3H : v3 ∈ convexHull ℝ (H : Set Point)) (hz1H : z1 ∈ convexHull ℝ (H : Set Point))
    (hz2H : z2 ∈ convexHull ℝ (H : Set Point)) :
    ∃ V : Finset Point, V ⊆ S ∧ V.card = 5 ∧
      ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)) := by
  classical
  obtain ⟨h12, h13, h23⟩ := ne_of_orient_ne_zero v1 v2 v3 ht.ne'
  obtain ⟨-, h1z1, h2z1⟩ := ne_of_orient_ne_zero v1 v2 z1 hz1.1.ne'
  obtain ⟨-, -, h3z1⟩ := ne_of_orient_ne_zero v2 v3 z1 hz1.2.1.ne'
  obtain ⟨-, h1z2, h2z2⟩ := ne_of_orient_ne_zero v1 v2 z2 hz2.1.ne'
  obtain ⟨-, -, h3z2⟩ := ne_of_orient_ne_zero v2 v3 z2 hz2.2.1.ne'
  obtain ⟨hzz, -, -⟩ := ne_of_orient_ne_zero z1 z2 v1 hl1.ne
  have hv1T : v1 ∈ convexHull ℝ ({v1, v2, v3} : Set Point) := subset_convexHull ℝ _ (by simp)
  have hv2T : v2 ∈ convexHull ℝ ({v1, v2, v3} : Set Point) := subset_convexHull ℝ _ (by simp)
  have hv3T : v3 ∈ convexHull ℝ ({v1, v2, v3} : Set Point) := subset_convexHull ℝ _ (by simp)
  have hz1T : z1 ∈ convexHull ℝ ({v1, v2, v3} : Set Point) :=
    interior_subset (mem_interior_triangle_of_orient_pos v1 v2 v3 z1 ht hz1.1 hz1.2.1 hz1.2.2)
  have hz2T : z2 ∈ convexHull ℝ ({v1, v2, v3} : Set Point) :=
    interior_subset (mem_interior_triangle_of_orient_pos v1 v2 v3 z2 ht hz2.1 hz2.2.1 hz2.2.2)
  have hcov : ∀ y ∈ H,
      (0 < orient z1 v3 y ∧ 0 < orient z1 y v1 ∧ orient v3 v1 y < 0) ∨
      (0 < orient z2 v1 y ∧ 0 < orient z2 y v2 ∧ orient v1 v2 y < 0) ∨
      (orient v2 v3 y < 0 ∧ orient z1 v3 y < 0 ∧ 0 < orient z2 v2 y) := by
    intro y hy
    have hyS : y ∈ S := hHS hy
    have hy1 : v1 ≠ y := fun h ↦ hout y hy (h ▸ hv1T)
    have hy2 : v2 ≠ y := fun h ↦ hout y hy (h ▸ hv2T)
    have hy3 : v3 ≠ y := fun h ↦ hout y hy (h ▸ hv3T)
    have hyz1 : z1 ≠ y := fun h ↦ hout y hy (h ▸ hz1T)
    have hyz2 : z2 ≠ y := fun h ↦ hout y hy (h ▸ hz2T)
    have hinj1 : Function.Injective ![v1, v2, v3, z1, y] :=
      injective_vec5 v1 v2 v3 z1 y h12 h13 h1z1 hy1 h23 h2z1 hy2 h3z1 hy3 hyz1
    have hinj2 : Function.Injective ![v1, v2, v3, z2, y] :=
      injective_vec5 v1 v2 v3 z2 y h12 h13 h1z2 hy1 h23 h2z2 hy2 h3z2 hy3 hyz2
    have hpS1 : ∀ i : Fin 5, ![v1, v2, v3, z1, y] i ∈ S := by
      intro i
      fin_cases i
      · exact hv1
      · exact hv2
      · exact hv3
      · exact hz1S
      · exact hyS
    have hpS2 : ∀ i : Fin 5, ![v1, v2, v3, z2, y] i ∈ S := by
      intro i
      fin_cases i
      · exact hv1
      · exact hv2
      · exact hv3
      · exact hz2S
      · exact hyS
    have hgp1 : IndexedGP ![v1, v2, v3, z1, y] := indexedGP_of_injective S hgp _ hpS1 hinj1
    have hgp2 : IndexedGP ![v1, v2, v3, z2, y] := indexedGP_of_injective S hgp _ hpS2 hinj2
    have hy' : orient v1 v2 y < 0 ∨ orient v2 v3 y < 0 ∨ orient v3 v1 y < 0 := by
      by_contra hcon
      push Not at hcon
      have e1 : 0 < orient v1 v2 y :=
        lt_of_le_of_ne hcon.1 (hgp v1 hv1 v2 hv2 y hyS h12 hy1 hy2).symm
      have e2 : 0 < orient v2 v3 y :=
        lt_of_le_of_ne hcon.2.1 (hgp v2 hv2 v3 hv3 y hyS h23 hy2 hy3).symm
      have e3 : 0 < orient v3 v1 y :=
        lt_of_le_of_ne hcon.2.2 (hgp v3 hv3 v1 hv1 y hyS h13.symm hy3 hy1).symm
      exact hout y hy
        (interior_subset (mem_interior_triangle_of_orient_pos v1 v2 v3 y ht e1 e2 e3))
    exact cover_332 v1 v2 v3 z1 z2 y hgp1 hgp2 ht hz1 hz2 hl1 hl2 hl3 hy'
  by_cases hstrip : ∃ y ∈ H, orient v2 v3 y < 0 ∧ orient z1 v3 y < 0 ∧ 0 < orient z2 v2 y
  · -- A hull vertex lands in the strip: `z1, z2, v2, y, v3` is a convex pentagon.
    obtain ⟨y, hy, hy1, hy2, hy3⟩ := hstrip
    have hyS : y ∈ S := hHS hy
    have e2 : v2 ≠ y := fun h ↦ hout y hy (h ▸ hv2T)
    have e3 : v3 ≠ y := fun h ↦ hout y hy (h ▸ hv3T)
    have e4 : z1 ≠ y := fun h ↦ hout y hy (h ▸ hz1T)
    have e5 : z2 ≠ y := fun h ↦ hout y hy (h ▸ hz2T)
    have hinj : Function.Injective ![z1, z2, v2, v3, y] :=
      injective_vec5 z1 z2 v2 v3 y hzz h2z1.symm h3z1.symm e4 h2z2.symm h3z2.symm e5 h23 e2 e3
    have hpS : ∀ i : Fin 5, ![z1, z2, v2, v3, y] i ∈ S := by
      intro i
      fin_cases i
      · exact hz1S
      · exact hz2S
      · exact hv2
      · exact hv3
      · exact hyS
    have hgp' : IndexedGP ![z1, z2, v2, v3, y] := indexedGP_of_injective S hgp _ hpS hinj
    refine ⟨Finset.univ.image ![z1, z2, v2, v3, y], ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact hpS i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · exact convexIndependent_strip _ hgp' hinj hl2 hl3 hz1.2.1 hz2.2.1 hy1 hy2 hy3
  · -- Every hull vertex sits in one of the two cones; pigeonhole and run the beam argument.
    push Not at hstrip
    have hcov2 : ∀ y ∈ H,
        (0 < orient z1 v3 y ∧ 0 < orient z1 y v1 ∧ orient v3 v1 y < 0) ∨
        (0 < orient z2 v1 y ∧ 0 < orient z2 y v2 ∧ orient v1 v2 y < 0) := by
      intro y hy
      rcases hcov y hy with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h.2.2 (not_lt.2 (hstrip y hy h.1 h.2.1))
    have hc : (Finset.univ : Finset (Fin 2)).card < H.card := by
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨ya, hya, yb, hyb, hneab, hf⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc
        (f := fun y : Point ↦
          if 0 < orient z1 v3 y ∧ 0 < orient z1 y v1 ∧ orient v3 v1 y < 0 then (0 : Fin 2) else 1)
        (fun a _ ↦ Finset.mem_univ _)
    by_cases c1 : 0 < orient z1 v3 ya ∧ 0 < orient z1 ya v1 ∧ orient v3 v1 ya < 0
    · by_cases d1 : 0 < orient z1 v3 yb ∧ 0 < orient z1 yb v1 ∧ orient v3 v1 yb < 0
      · exact beam_of_same_cone S hgp H hHS hH v3 v1 z1 ya yb hv3 hv1 hz1S hya hyb hneab
          hz1.2.2 hv3H hv1H hz1H c1 d1
      · exfalso
        rw [if_pos c1, if_neg d1] at hf
        exact absurd hf (by decide)
    · by_cases d1 : 0 < orient z1 v3 yb ∧ 0 < orient z1 yb v1 ∧ orient v3 v1 yb < 0
      · exfalso
        rw [if_neg c1, if_pos d1] at hf
        exact absurd hf (by decide)
      · exact beam_of_same_cone S hgp H hHS hH v1 v2 z2 ya yb hv1 hv2 hz2S hya hyb hneab
          hz2.1 hv1H hv2H hz2H ((hcov2 ya hya).resolve_left c1) ((hcov2 yb hyb).resolve_left d1)

/-- Bonnice's `(3,3,2)` case: at least three hull vertices `H`, an inner counterclockwise triangle
with two points strictly inside, everything inside the hull of `H`, no vertex of `H` in the closed
inner triangle. Then `S` contains five points in convex position. -/
theorem case_332 (S : Finset Point) (hgp : GeneralPosition S)
    (H : Finset Point) (hHS : H ⊆ S)
    (hH : ConvexIndependent ℝ (fun x : (H : Set Point) => (x : Point))) (h3 : 3 ≤ H.card)
    (v1 v2 v3 z1 z2 : Point) (hv1 : v1 ∈ S) (hv2 : v2 ∈ S) (hv3 : v3 ∈ S)
    (hz1S : z1 ∈ S) (hz2S : z2 ∈ S) (hne : z1 ≠ z2) (ht : 0 < orient v1 v2 v3)
    (hz1 : 0 < orient v1 v2 z1 ∧ 0 < orient v2 v3 z1 ∧ 0 < orient v3 v1 z1)
    (hz2 : 0 < orient v1 v2 z2 ∧ 0 < orient v2 v3 z2 ∧ 0 < orient v3 v1 z2)
    (hout : ∀ y ∈ H, y ∉ convexHull ℝ ({v1, v2, v3} : Set Point))
    (hin : ({v1, v2, v3, z1, z2} : Set Point) ⊆ convexHull ℝ (H : Set Point)) :
    ∃ V : Finset Point, V ⊆ S ∧ V.card = 5 ∧
      ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)) := by
  classical
  obtain ⟨-, h1z1, h2z1⟩ := ne_of_orient_ne_zero v1 v2 z1 hz1.1.ne'
  obtain ⟨-, -, h3z1⟩ := ne_of_orient_ne_zero v2 v3 z1 hz1.2.1.ne'
  obtain ⟨-, h1z2, h2z2⟩ := ne_of_orient_ne_zero v1 v2 z2 hz2.1.ne'
  obtain ⟨-, -, h3z2⟩ := ne_of_orient_ne_zero v2 v3 z2 hz2.2.1.ne'
  have hv1H : v1 ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have hv2H : v2 ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have hv3H : v3 ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have hz1H : z1 ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have hz2H : z2 ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have t2 : 0 < orient v2 v3 v1 := by unfold orient at ht ⊢; linarith
  have t3 : 0 < orient v3 v1 v2 := by unfold orient at ht ⊢; linarith
  have hout2 : ∀ y ∈ H, y ∉ convexHull ℝ ({v2, v3, v1} : Set Point) := by
    have hs : ({v2, v3, v1} : Set Point) = {v1, v2, v3} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hs]
    exact hout
  have hout3 : ∀ y ∈ H, y ∉ convexHull ℝ ({v3, v1, v2} : Set Point) := by
    have hs : ({v3, v1, v2} : Set Point) = {v1, v2, v3} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hs]
    exact hout
  have sw1 : orient z2 z1 v1 = -orient z1 z2 v1 := by unfold orient; ring
  have sw2 : orient z2 z1 v2 = -orient z1 z2 v2 := by unfold orient; ring
  have sw3 : orient z2 z1 v3 = -orient z1 z2 v3 := by unfold orient; ring
  have s1 : orient z1 z2 v1 ≠ 0 := hgp z1 hz1S z2 hz2S v1 hv1 hne h1z1.symm h1z2.symm
  have s2 : orient z1 z2 v2 ≠ 0 := hgp z1 hz1S z2 hz2S v2 hv2 hne h2z1.symm h2z2.symm
  have s3 : orient z1 z2 v3 ≠ 0 := hgp z1 hz1S z2 hz2S v3 hv3 hne h3z1.symm h3z2.symm
  -- A point strictly inside the triangle cannot have all three vertices strictly on one side
  -- of a line through it.
  have key : ∀ w1 w2 : Point, 0 < orient v1 v2 w1 → 0 < orient v2 v3 w1 → 0 < orient v3 v1 w1 →
      0 < orient w1 w2 v1 → 0 < orient w1 w2 v2 → 0 < orient w1 w2 v3 → False := by
    intro w1 w2 k1 k2 k3 g1 g2 g3
    obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hw⟩ := barycentric_of_orient_pos v1 v2 v3 w1 ht k1 k2 k3
    have h0 : orient w1 w2 (α • v1 + β • v2 + γ • v3) = 0 := by
      rw [← hw]
      exact orient_left_self w1 w2
    rw [orient_affine_comb w1 w2 v1 v2 v3 α β γ hsum] at h0
    nlinarith [mul_pos hα g1, mul_pos hβ g2, mul_pos hγ g3]
  rcases Ne.lt_or_gt s1 with a1 | a1 <;> rcases Ne.lt_or_gt s2 with a2 | a2 <;>
    rcases Ne.lt_or_gt s3 with a3 | a3
  · -- all three vertices right of `z1 → z2`: impossible
    exact absurd (key z2 z1 hz2.1 hz2.2.1 hz2.2.2 (by rw [sw1]; linarith) (by rw [sw2]; linarith)
      (by rw [sw3]; linarith)) not_false
  · -- `v3` isolated on the left: relabel to `(v3, v1, v2)` and swap `z1, z2`
    exact case_332_core S hgp H hHS hH h3 v3 v1 v2 z2 z1 hv3 hv1 hv2 hz2S hz1S t3
      ⟨hz2.2.2, hz2.1, hz2.2.1⟩ ⟨hz1.2.2, hz1.1, hz1.2.1⟩ (by rw [sw3]; linarith)
      (by rw [sw1]; linarith) (by rw [sw2]; linarith) hout3 hv3H hv1H hv2H hz2H hz1H
  · -- `v2` isolated on the left: relabel to `(v2, v3, v1)` and swap `z1, z2`
    exact case_332_core S hgp H hHS hH h3 v2 v3 v1 z2 z1 hv2 hv3 hv1 hz2S hz1S t2
      ⟨hz2.2.1, hz2.2.2, hz2.1⟩ ⟨hz1.2.1, hz1.2.2, hz1.1⟩ (by rw [sw2]; linarith)
      (by rw [sw3]; linarith) (by rw [sw1]; linarith) hout2 hv2H hv3H hv1H hz2H hz1H
  · -- `v1` isolated on the right: already normalised
    exact case_332_core S hgp H hHS hH h3 v1 v2 v3 z1 z2 hv1 hv2 hv3 hz1S hz2S ht hz1 hz2 a1 a2 a3
      hout hv1H hv2H hv3H hz1H hz2H
  · -- `v1` isolated on the left: swap `z1, z2`
    exact case_332_core S hgp H hHS hH h3 v1 v2 v3 z2 z1 hv1 hv2 hv3 hz2S hz1S ht hz2 hz1
      (by rw [sw1]; linarith) (by rw [sw2]; linarith) (by rw [sw3]; linarith) hout hv1H hv2H hv3H
      hz2H hz1H
  · -- `v2` isolated on the right: relabel to `(v2, v3, v1)`
    exact case_332_core S hgp H hHS hH h3 v2 v3 v1 z1 z2 hv2 hv3 hv1 hz1S hz2S t2
      ⟨hz1.2.1, hz1.2.2, hz1.1⟩ ⟨hz2.2.1, hz2.2.2, hz2.1⟩ a2 a3 a1 hout2 hv2H hv3H hv1H hz1H hz2H
  · -- `v3` isolated on the right: relabel to `(v3, v1, v2)`
    exact case_332_core S hgp H hHS hH h3 v3 v1 v2 z1 z2 hv3 hv1 hv2 hz1S hz2S t3
      ⟨hz1.2.2, hz1.1, hz1.2.1⟩ ⟨hz2.2.2, hz2.1, hz2.2.1⟩ a3 a1 a2 hout3 hv3H hv1H hv2H hz1H hz2H
  · -- all three vertices left of `z1 → z2`: impossible
    exact absurd (key z1 z2 hz1.1 hz1.2.1 hz1.2.2 a1 a2 a3) not_false

end Horton
