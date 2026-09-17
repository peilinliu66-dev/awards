/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Descent.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.ExtremeHull
import EmptyPentagon.Certificate

noncomputable section
open Classical
namespace Horton

/-- Points of `S` strictly inside the hull of `V`. -/
def interiorPoints (S V : Finset Point) : Finset Point :=
  S.filter (fun p => p ∈ interior (convexHull ℝ (V : Set Point)))

/-- Reversing the directed line negates the orientation. -/
theorem orient_swap_line (u v x : Point) : orient v u x = -orient u v x := by
  unfold orient; ring

/-- A convex-independent vertex is never strictly inside the hull of the vertex set. -/
theorem not_mem_interior_of_convexIndependent (V : Finset Point)
    (hV : ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)))
    (a : Point) (ha : a ∈ V) : a ∉ interior (convexHull ℝ (V : Set Point)) :=
  fun h => Set.disjoint_left.mp (disjoint_interior_extremePoints _) h
    (mem_extremePoints_of_convexIndependent V hV a ha)

/-- The open half-plane to the left of the directed line through `u` and `v` is convex. -/
theorem convex_open_halfplane (u v : Point) : Convex ℝ {q : Point | 0 < orient u v q} := by
  intro x hx y hy a b ha hb hab
  have hx' : 0 < orient u v x := hx
  have hy' : 0 < orient u v y := hy
  show 0 < orient u v (a • x + b • y)
  rw [orient_smul_add u v x y a b hab]
  rcases ha.lt_or_eq with ha' | ha'
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx') (mul_nonneg hb hy'.le)
  · subst ha'
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hy'

/-- Lemma A: if every point of `T` is strictly left of the line `p q` and `z` is on the line, then
the only point of the hull of `insert z T` on the line is `z` itself. -/
theorem eq_of_mem_convexHull_insert_of_orient_eq_zero (p q z : Point) (hz : orient p q z = 0)
    (T : Set Point) (hT : ∀ x ∈ T, 0 < orient p q x) (r : Point)
    (hr : r ∈ convexHull ℝ (insert z T)) (h0 : orient p q r = 0) : r = z := by
  by_cases hne : T.Nonempty
  · rw [convexHull_insert hne, mem_convexJoin] at hr
    obtain ⟨z', hz', y, hy, s, t, hs, ht, hst, rfl⟩ := hr
    rw [Set.mem_singleton_iff] at hz'
    subst hz'
    have hy' : 0 < orient p q y :=
      convexHull_min (fun x hx => hT x hx) (convex_open_halfplane p q) hy
    rw [orient_smul_add p q _ y s t hst, hz] at h0
    have ht0 : t = 0 := by
      rcases ht.lt_or_eq with ht' | ht'
      · exact absurd h0 (by nlinarith [mul_pos ht' hy'])
      · exact ht'.symm
    subst ht0
    have hs1 : s = 1 := by linarith
    subst hs1
    simp
  · have hT0 : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst hT0
    simpa using hr

/-- Lemma C (descent step): two interior points `p ≠ q` with three vertices strictly left of the
line `p q` yield a convex pentagon with at least two fewer interior points. -/
theorem descent_step (S : Finset Point) (V : Finset Point)
    (hVS : V ⊆ S) (hV : ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)))
    (p q : Point) (hp : p ∈ interiorPoints S V) (hq : q ∈ interiorPoints S V) (hpq : p ≠ q)
    (h3 : 3 ≤ (V.filter (fun v => 0 < orient p q v)).card) :
    ∃ V' : Finset Point, V' ⊆ S ∧ V'.card = 5 ∧
      ConvexIndependent ℝ (fun x : (V' : Set Point) => (x : Point)) ∧
      (interiorPoints S V').card + 2 ≤ (interiorPoints S V).card := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h3
  simp only [Finset.mem_filter] at ha hb hc
  obtain ⟨ha, hpa⟩ := ha
  obtain ⟨hb, hpb⟩ := hb
  obtain ⟨hc, hpc⟩ := hc
  rw [interiorPoints, Finset.mem_filter] at hp hq
  obtain ⟨hpS, hpI⟩ := hp
  obtain ⟨hqS, hqI⟩ := hq
  have hpV : p ∉ V := fun h => not_mem_interior_of_convexIndependent V hV p h hpI
  have hqV : q ∉ V := fun h => not_mem_interior_of_convexIndependent V hV q h hqI
  have hpa' : p ≠ a := fun h => hpV (h ▸ ha)
  have hpb' : p ≠ b := fun h => hpV (h ▸ hb)
  have hpc' : p ≠ c := fun h => hpV (h ▸ hc)
  have hqa' : q ≠ a := fun h => hqV (h ▸ ha)
  have hqb' : q ≠ b := fun h => hqV (h ▸ hb)
  have hqc' : q ≠ c := fun h => hqV (h ▸ hc)
  set V' : Finset Point := {a, b, c, p, q} with hV'
  have hpp : orient p q p = 0 := by unfold orient; ring
  have hqq : orient p q q = 0 := by unfold orient; ring
  -- every point of `V'` lies in the hull of `V`, and in the closed half-plane
  have hV'hull : ∀ x ∈ V', x ∈ convexHull ℝ (V : Set Point) := by
    intro x hx
    simp only [hV', Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr ha)
    · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hb)
    · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hc)
    · exact interior_subset hpI
    · exact interior_subset hqI
  have hV'half : ∀ x ∈ V', 0 ≤ orient p q x := by
    intro x hx
    simp only [hV', Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hpa.le
    · exact hpb.le
    · exact hpc.le
    · exact hpp.ge
    · exact hqq.ge
  refine ⟨V', ?_, ?_, ?_, ?_⟩
  · -- subset of `S`
    intro x hx
    simp only [hV', Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hVS ha
    · exact hVS hb
    · exact hVS hc
    · exact hpS
    · exact hqS
  · -- cardinality
    simp only [hV']
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_pair hpq]
    · simp [hqc'.symm, hpc'.symm]
    · simp [hbc, hqb'.symm, hpb'.symm]
    · simp [hab, hac, hpa'.symm, hqa'.symm]
  · -- convex independence
    rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
    intro v hv
    rw [Finset.mem_coe] at hv
    rw [← Finset.coe_erase]
    by_cases hvV : v ∈ V
    · refine not_mem_convexHull_of_convexIndependent V hV v hvV (V'.erase v) ?_
        (Finset.notMem_erase v V')
      intro x hx
      exact hV'hull x (Finset.mem_of_mem_erase (Finset.mem_coe.mp hx))
    · have hv' : v = p ∨ v = q := by
        simp only [hV', Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · exact absurd ha hvV
        · exact absurd hb hvV
        · exact absurd hc hvV
        · exact Or.inl rfl
        · exact Or.inr rfl
      intro hmem
      rcases hv' with rfl | rfl
      · -- `v = p`: the hull of the others meets the line only at `q`
        have hsub : ((V'.erase v : Finset Point) : Set Point) ⊆
            insert q {x : Point | 0 < orient v q x} := by
          intro x hx
          rw [Finset.mem_coe, Finset.mem_erase] at hx
          obtain ⟨hxv, hx⟩ := hx
          simp only [hV', Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl
          · exact Or.inr hpa
          · exact Or.inr hpb
          · exact Or.inr hpc
          · exact absurd rfl hxv
          · exact Or.inl rfl
        exact hpq (eq_of_mem_convexHull_insert_of_orient_eq_zero v q q hqq _
          (fun x hx => hx) v (convexHull_mono hsub hmem) hpp)
      · -- `v = q`: the hull of the others meets the line only at `p`
        have hsub : ((V'.erase v : Finset Point) : Set Point) ⊆
            insert p {x : Point | 0 < orient p v x} := by
          intro x hx
          rw [Finset.mem_coe, Finset.mem_erase] at hx
          obtain ⟨hxv, hx⟩ := hx
          simp only [hV', Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl
          · exact Or.inr hpa
          · exact Or.inr hpb
          · exact Or.inr hpc
          · exact Or.inl rfl
          · exact absurd rfl hxv
        exact hpq (eq_of_mem_convexHull_insert_of_orient_eq_zero p v p hpp _
          (fun x hx => hx) v (convexHull_mono hsub hmem) hqq).symm
  · -- interior count drops by at least two
    have hsub : interiorPoints S V' ⊆ ((interiorPoints S V).erase p).erase q := by
      intro x hx
      rw [interiorPoints, Finset.mem_filter] at hx
      obtain ⟨hxS, hxI⟩ := hx
      have hxV : x ∈ interior (convexHull ℝ (V : Set Point)) :=
        interior_mono (convexHull_min (fun y hy => hV'hull y (Finset.mem_coe.mp hy))
          (convex_convexHull ℝ _)) hxI
      have hxpos : 0 < orient p q x := by
        by_contra hle
        exact not_mem_interior_convexHull_of_halfplane V' p q x hpq hV'half (not_lt.mp hle) hxI
      rw [Finset.mem_erase, Finset.mem_erase, interiorPoints, Finset.mem_filter]
      refine ⟨fun h => ?_, fun h => ?_, hxS, hxV⟩
      · subst h; exact absurd hqq hxpos.ne'
      · subst h; exact absurd hpp hxpos.ne'
    have hpmem : p ∈ interiorPoints S V := by
      rw [interiorPoints, Finset.mem_filter]; exact ⟨hpS, hpI⟩
    have hqmem : q ∈ (interiorPoints S V).erase p := by
      rw [Finset.mem_erase, interiorPoints, Finset.mem_filter]; exact ⟨hpq.symm, hqS, hqI⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hqmem, Finset.card_erase_of_mem hpmem] at h1
    have h2 := Finset.card_pos.mpr ⟨p, hpmem⟩
    have h3 := Finset.card_pos.mpr ⟨q, hqmem⟩
    rw [Finset.card_erase_of_mem hpmem] at h3
    omega

/-- Harborth's descent: if `S` (in general position) contains a convex pentagon, it contains one
with at most one point of `S` strictly inside. -/
theorem exists_convex_pentagon_few_interior (S : Finset Point) (hgp : GeneralPosition S)
    (hex : ∃ V : Finset Point, V ⊆ S ∧ V.card = 5 ∧
      ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point))) :
    ∃ V : Finset Point, V ⊆ S ∧ V.card = 5 ∧
      ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)) ∧
      (interiorPoints S V).card ≤ 1 := by
  set 𝒱 : Finset (Finset Point) := (S.powersetCard 5).filter
    (fun V => ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point))) with h𝒱
  have hmem : ∀ V, V ∈ 𝒱 ↔ V ⊆ S ∧ V.card = 5 ∧
      ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)) := by
    intro V
    simp only [h𝒱, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]
  obtain ⟨V₀, hV₀⟩ := hex
  obtain ⟨V, hV, hmin⟩ := Finset.exists_min_image 𝒱 (fun V => (interiorPoints S V).card)
    ⟨V₀, (hmem V₀).mpr hV₀⟩
  obtain ⟨hVS, hVcard, hVci⟩ := (hmem V).mp hV
  refine ⟨V, hVS, hVcard, hVci, ?_⟩
  by_contra hlt
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (not_le.mp hlt)
  have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
  have hqS : q ∈ S := (Finset.mem_filter.mp hq).1
  have hpI := (Finset.mem_filter.mp hp).2
  have hqI := (Finset.mem_filter.mp hq).2
  -- no vertex is on the line `p q`
  have hne : ∀ v ∈ V, orient p q v ≠ 0 := by
    intro v hv
    have hpv : p ≠ v := fun h => not_mem_interior_of_convexIndependent V hVci v hv (h ▸ hpI)
    have hqv : q ≠ v := fun h => not_mem_interior_of_convexIndependent V hVci v hv (h ▸ hqI)
    exact hgp p hpS q hqS v (hVS hv) hpq hpv hqv
  -- pigeonhole: three vertices strictly on one side
  have hsplit := Finset.card_filter_add_card_filter_not (s := V) (fun v => 0 < orient p q v)
  rw [hVcard] at hsplit
  have hdesc : ∀ V' : Finset Point, V' ∈ 𝒱 →
      (interiorPoints S V').card + 2 ≤ (interiorPoints S V).card → False := by
    intro V' hV' hle
    have := hmin V' hV'
    omega
  by_cases h3 : 3 ≤ (V.filter (fun v => 0 < orient p q v)).card
  · obtain ⟨V', hV'S, hV'card, hV'ci, hle⟩ :=
      descent_step S V hVS hVci p q hp hq hpq h3
    exact hdesc V' ((hmem V').mpr ⟨hV'S, hV'card, hV'ci⟩) hle
  · have h3' : 3 ≤ (V.filter (fun v => 0 < orient q p v)).card := by
      have hsub : V.filter (fun v => ¬ 0 < orient p q v) ⊆
          V.filter (fun v => 0 < orient q p v) := by
        intro v hv
        rw [Finset.mem_filter] at hv ⊢
        refine ⟨hv.1, ?_⟩
        rw [orient_swap_line]
        exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp hv.2) (hne v hv.1))
      have := Finset.card_le_card hsub
      omega
    obtain ⟨V', hV'S, hV'card, hV'ci, hle⟩ :=
      descent_step S V hVS hVci q p hq hp hpq.symm h3'
    exact hdesc V' ((hmem V').mpr ⟨hV'S, hV'card, hV'ci⟩) hle

end Horton
