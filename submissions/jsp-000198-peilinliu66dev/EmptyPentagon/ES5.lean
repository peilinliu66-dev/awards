/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/ES5.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Certificate
import EmptyPentagon.Hull
import EmptyPentagon.ExtremeHull
import EmptyPentagon.Interp
import EmptyPentagon.Label4
import EmptyPentagon.FourOuter
import EmptyPentagon.Case332
import EmptyPentagon.Case342

noncomputable section
namespace Horton

/-- Convex independence is inherited by subsets. -/
theorem convexIndependent_of_subset (V W : Finset Point) (hWV : W ⊆ V)
    (hV : ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point))) :
    ConvexIndependent ℝ (fun x : (W : Set Point) => (x : Point)) := by
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hV ⊢
  have hc : (W : Set Point) ⊆ (V : Set Point) := Finset.coe_subset.mpr hWV
  intro x hx hmem
  exact hV x (hc hx) (convexHull_mono (Set.sdiff_subset_sdiff_left hc) hmem)

/-- A point strictly inside the hull of `Q` is strictly left of every line through two points
that supports `Q` on its left. -/
theorem orient_pos_of_mem_interior (Q : Finset Point) (u v z : Point) (huv : u ≠ v)
    (hQ : ∀ x ∈ Q, 0 ≤ orient u v x)
    (hz : z ∈ interior (convexHull ℝ (Q : Set Point))) :
    0 < orient u v z := by
  by_contra h
  exact not_mem_interior_convexHull_of_halfplane Q u v z huv hQ (not_lt.mp h) hz

/-- Erdős–Szekeres for pentagons (Kalbfleisch–Kalbfleisch–Stanton 1970, Bonnice 1974): any nine
points in general position contain five in convex position. -/
theorem exists_convex_pentagon (S : Finset Point) (h9 : 9 ≤ S.card) (hgp : GeneralPosition S) :
    ∃ V : Finset Point, V ⊆ S ∧ V.card = 5 ∧
      ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)) := by
  classical
  have oz1 : ∀ a b : Point, orient a b a = 0 := by
    intro a b
    unfold orient
    ring
  have oz2 : ∀ a b : Point, orient a b b = 0 := by
    intro a b
    unfold orient
    ring
  have ocyc : ∀ a b c : Point, orient a b c = orient b c a := by
    intro a b c
    unfold orient
    ring
  have osw : ∀ a b c : Point, orient a c b = -orient a b c := by
    intro a b c
    unfold orient
    ring
  have hne3 : ∀ a b c : Point, orient a b c ≠ 0 → a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    intro a b c h
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact h (by unfold orient; ring)
  have hmono : ∀ T : Finset Point, T ⊆ S → GeneralPosition T :=
    fun T hT a ha b hb c hc => hgp a (hT ha) b (hT hb) c (hT hc)
  have hfive : ∀ K : Finset Point, K ⊆ S →
      ConvexIndependent ℝ (fun x : (K : Set Point) => (x : Point)) → 5 ≤ K.card →
      ∃ V : Finset Point, V ⊆ S ∧ V.card = 5 ∧
        ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)) := by
    intro K hKS hK h5
    obtain ⟨V, hVK, hVcard⟩ := Finset.exists_subset_card_eq h5
    exact ⟨V, hVK.trans hKS, hVcard, convexIndependent_of_subset K V hVK hK⟩
  set H : Finset Point := hullVertices S with hHdef
  have hHS : H ⊆ S := hullVertices_subset S
  have hH : ConvexIndependent ℝ (fun x : (H : Set Point) => (x : Point)) :=
    convexIndependent_hullVertices S
  have h3H : 3 ≤ H.card := three_le_card_hullVertices S hgp (by omega)
  by_cases hA : 5 ≤ H.card
  · exact hfive H hHS hH hA
  have hH4 : H.card ≤ 4 := by omega
  set S1 : Finset Point := S \ H with hS1def
  have hS1S : S1 ⊆ S := Finset.sdiff_subset
  have hS1card : S1.card = S.card - H.card := by
    rw [hS1def, Finset.card_sdiff_of_subset hHS]
  have hgp1 : GeneralPosition S1 := hmono S1 hS1S
  have hS1H : ∀ x ∈ S1, x ∈ convexHull ℝ (H : Set Point) := by
    intro x hx
    rw [hS1def, Finset.mem_sdiff] at hx
    exact interior_subset (mem_interior_hullVertices_of_not_mem S hgp x hx.1 hx.2)
  have houtT : ∀ T : Finset Point, (∀ x ∈ T, x ∈ S1) →
      ∀ y ∈ H, y ∉ convexHull ℝ (T : Set Point) := by
    intro T hT y hy
    refine not_mem_convexHull_of_convexIndependent H hH y hy T ?_ ?_
    · exact fun x hx => hS1H x (hT x (Finset.mem_coe.mp hx))
    · intro hyT
      have hmem := hT y hyT
      rw [hS1def, Finset.mem_sdiff] at hmem
      exact hmem.2 hy
  set H1 : Finset Point := hullVertices S1 with hH1def
  have hH1S1 : H1 ⊆ S1 := hullVertices_subset S1
  have hH1S : H1 ⊆ S := hH1S1.trans hS1S
  have hH1 : ConvexIndependent ℝ (fun x : (H1 : Set Point) => (x : Point)) :=
    convexIndependent_hullVertices S1
  have h3H1 : 3 ≤ H1.card := three_le_card_hullVertices S1 hgp1 (by omega)
  by_cases hB : 5 ≤ H1.card
  · exact hfive H1 hH1S hH1 hB
  have hH14 : H1.card ≤ 4 := by omega
  have hgpH1 : GeneralPosition H1 := hmono H1 hH1S
  set S2 : Finset Point := S1 \ H1 with hS2def
  have hS2S1 : S2 ⊆ S1 := Finset.sdiff_subset
  have hS2card : S2.card = S1.card - H1.card := by
    rw [hS2def, Finset.card_sdiff_of_subset hH1S1]
  have hS2H1 : ∀ z ∈ S2, z ∉ H1 := by
    intro z hz
    rw [hS2def, Finset.mem_sdiff] at hz
    exact hz.2
  have hkey : ∀ u v : Point, u ≠ v → (∀ x ∈ H1, 0 ≤ orient u v x) →
      ∀ z ∈ S2, 0 < orient u v z := by
    intro u v huv hQ z hz
    rw [hS2def, Finset.mem_sdiff] at hz
    exact orient_pos_of_mem_interior H1 u v z huv hQ
      (mem_interior_hullVertices_of_not_mem S1 hgp1 z hz.1 hz.2)
  by_cases hc3 : H1.card = 3
  · obtain ⟨v1, v2, v3, hVeq, ht⟩ := exists_ccw_triangle H1 hc3 hgpH1
    obtain ⟨h12, h13, h23⟩ := hne3 v1 v2 v3 ht.ne'
    have hv1 : v1 ∈ H1 := by rw [← hVeq]; simp
    have hv2 : v2 ∈ H1 := by rw [← hVeq]; simp
    have hv3 : v3 ∈ H1 := by rw [← hVeq]; simp
    have hv1S1 : v1 ∈ S1 := hH1S1 hv1
    have hv2S1 : v2 ∈ S1 := hH1S1 hv2
    have hv3S1 : v3 ∈ S1 := hH1S1 hv3
    have hside : ∀ x ∈ H1,
        0 ≤ orient v1 v2 x ∧ 0 ≤ orient v2 v3 x ∧ 0 ≤ orient v3 v1 x := by
      rw [← hVeq]
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      and_intros <;>
        linarith [oz1 v1 v2, oz2 v1 v2, oz1 v2 v3, oz2 v2 v3, oz1 v3 v1, oz2 v3 v1,
          ocyc v1 v2 v3, ocyc v2 v3 v1, ht]
    have hcert : ∀ z ∈ S2,
        0 < orient v1 v2 z ∧ 0 < orient v2 v3 z ∧ 0 < orient v3 v1 z := by
      intro z hz
      exact ⟨hkey v1 v2 h12 (fun x hx => (hside x hx).1) z hz,
        hkey v2 v3 h23 (fun x hx => (hside x hx).2.1) z hz,
        hkey v3 v1 h13.symm (fun x hx => (hside x hx).2.2) z hz⟩
    have hout : ∀ y ∈ H, y ∉ convexHull ℝ ({v1, v2, v3} : Set Point) := by
      have hsub : ∀ x ∈ ({v1, v2, v3} : Finset Point), x ∈ S1 := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hv1S1
        · exact hv2S1
        · exact hv3S1
      simpa using houtT ({v1, v2, v3} : Finset Point) hsub
    by_cases h4 : 4 ≤ H.card
    · obtain ⟨z, hz⟩ : S2.Nonempty := Finset.card_pos.mp (by omega)
      have hzS1 : z ∈ S1 := hS2S1 hz
      refine convex_pentagon_of_four_outer S hgp H hHS hH h4 v1 v2 v3 z (hS1S hv1S1)
        (hS1S hv2S1) (hS1S hv3S1) (hS1S hzS1) ht (hcert z hz) hout ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hS1H _ hv1S1
      · exact hS1H _ hv2S1
      · exact hS1H _ hv3S1
      · exact hS1H _ hzS1
    · obtain ⟨z1, hz1, z2, hz2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < S2.card)
      have hz1S1 : z1 ∈ S1 := hS2S1 hz1
      have hz2S1 : z2 ∈ S1 := hS2S1 hz2
      refine case_332 S hgp H hHS hH h3H v1 v2 v3 z1 z2 (hS1S hv1S1) (hS1S hv2S1)
        (hS1S hv3S1) (hS1S hz1S1) (hS1S hz2S1) hne ht (hcert z1 hz1) (hcert z2 hz2) hout ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact hS1H _ hv1S1
      · exact hS1H _ hv2S1
      · exact hS1H _ hv3S1
      · exact hS1H _ hz1S1
      · exact hS1H _ hz2S1
  · have hc4 : H1.card = 4 := by omega
    obtain ⟨w1, w2, w3, w4, hVeq, hq1, hq2, hq3, hq4⟩ :=
      exists_cyclic_labeling4 H1 hc4 hgpH1 hH1
    obtain ⟨h12, h13, h23⟩ := hne3 w1 w2 w3 hq1.ne'
    obtain ⟨-, h24, h34⟩ := hne3 w2 w3 w4 hq2.ne'
    obtain ⟨-, h31, h41⟩ := hne3 w3 w4 w1 hq3.ne'
    have hw1 : w1 ∈ H1 := by rw [← hVeq]; simp
    have hw2 : w2 ∈ H1 := by rw [← hVeq]; simp
    have hw3 : w3 ∈ H1 := by rw [← hVeq]; simp
    have hw4 : w4 ∈ H1 := by rw [← hVeq]; simp
    have hw1S1 : w1 ∈ S1 := hH1S1 hw1
    have hw2S1 : w2 ∈ S1 := hH1S1 hw2
    have hw3S1 : w3 ∈ S1 := hH1S1 hw3
    have hw4S1 : w4 ∈ S1 := hH1S1 hw4
    have hside : ∀ x ∈ H1, 0 ≤ orient w1 w2 x ∧ 0 ≤ orient w2 w3 x ∧
        0 ≤ orient w3 w4 x ∧ 0 ≤ orient w4 w1 x := by
      rw [← hVeq]
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      and_intros <;>
        linarith [oz1 w1 w2, oz2 w1 w2, oz1 w2 w3, oz2 w2 w3, oz1 w3 w4, oz2 w3 w4,
          oz1 w4 w1, oz2 w4 w1, ocyc w1 w2 w3, ocyc w2 w3 w4, ocyc w3 w4 w1,
          ocyc w4 w1 w2, hq1, hq2, hq3, hq4]
    have hcert : ∀ z ∈ S2, 0 < orient w1 w2 z ∧ 0 < orient w2 w3 z ∧
        0 < orient w3 w4 z ∧ 0 < orient w4 w1 z := by
      intro z hz
      exact ⟨hkey w1 w2 h12 (fun x hx => (hside x hx).1) z hz,
        hkey w2 w3 h23 (fun x hx => (hside x hx).2.1) z hz,
        hkey w3 w4 h34 (fun x hx => (hside x hx).2.2.1) z hz,
        hkey w4 w1 h41 (fun x hx => (hside x hx).2.2.2) z hz⟩
    by_cases h4 : 4 ≤ H.card
    · obtain ⟨z, hz⟩ : S2.Nonempty := Finset.card_pos.mp (by omega)
      have hzS1 : z ∈ S1 := hS2S1 hz
      have hzw1 : w1 ≠ z := fun h => hS2H1 z hz (h ▸ hw1)
      have hzw3 : w3 ≠ z := fun h => hS2H1 z hz (h ▸ hw3)
      have hdiag : orient w1 w3 z ≠ 0 :=
        hgp w1 (hS1S hw1S1) w3 (hS1S hw3S1) z (hS1S hzS1) h13 hzw1 hzw3
      obtain ⟨c1, c2, c3, c4⟩ := hcert z hz
      rcases lt_or_gt_of_ne hdiag with hneg | hpos
      · refine convex_pentagon_of_four_outer S hgp H hHS hH h4 w1 w2 w3 z (hS1S hw1S1)
          (hS1S hw2S1) (hS1S hw3S1) (hS1S hzS1) hq1 ⟨c1, c2, ?_⟩ ?_ ?_
        · linarith [ocyc w3 w1 z, osw w1 w3 z]
        · have hsub : ∀ x ∈ ({w1, w2, w3} : Finset Point), x ∈ S1 := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact hw1S1
            · exact hw2S1
            · exact hw3S1
          simpa using houtT ({w1, w2, w3} : Finset Point) hsub
        · intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact hS1H _ hw1S1
          · exact hS1H _ hw2S1
          · exact hS1H _ hw3S1
          · exact hS1H _ hzS1
      · refine convex_pentagon_of_four_outer S hgp H hHS hH h4 w1 w3 w4 z (hS1S hw1S1)
          (hS1S hw3S1) (hS1S hw4S1) (hS1S hzS1) ?_ ⟨hpos, c3, c4⟩ ?_ ?_
        · linarith [ocyc w3 w4 w1, ocyc w4 w1 w3]
        · have hsub : ∀ x ∈ ({w1, w3, w4} : Finset Point), x ∈ S1 := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact hw1S1
            · exact hw3S1
            · exact hw4S1
          simpa using houtT ({w1, w3, w4} : Finset Point) hsub
        · intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact hS1H _ hw1S1
          · exact hS1H _ hw3S1
          · exact hS1H _ hw4S1
          · exact hS1H _ hzS1
    · obtain ⟨z1, hz1, z2, hz2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < S2.card)
      have hz1S1 : z1 ∈ S1 := hS2S1 hz1
      have hz2S1 : z2 ∈ S1 := hS2S1 hz2
      refine case_342 S hgp H hHS hH h3H w1 w2 w3 w4 z1 z2 (hS1S hw1S1) (hS1S hw2S1)
        (hS1S hw3S1) (hS1S hw4S1) (hS1S hz1S1) (hS1S hz2S1) hne hq1 hq2 hq3 hq4
        (hcert z1 hz1) (hcert z2 hz2) ?_ ?_
      · have hsub : ∀ x ∈ ({w1, w2, w3, w4} : Finset Point), x ∈ S1 := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact hw1S1
          · exact hw2S1
          · exact hw3S1
          · exact hw4S1
        simpa using houtT ({w1, w2, w3, w4} : Finset Point) hsub
      · intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hS1H _ hw1S1
        · exact hS1H _ hw2S1
        · exact hS1H _ hw3S1
        · exact hS1H _ hw4S1
        · exact hS1H _ hz1S1
        · exact hS1H _ hz2S1

end Horton
