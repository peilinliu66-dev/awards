import Mathlib

/-! Finite edge bounds for noncomplete degree-sum-closed graphs. -/

namespace JSP842

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Remove a set of vertices, charging every removed edge to an incident vertex. -/
theorem edge_bound_remove (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    G.edgeFinset.card ≤ (Fintype.card V - S.card).choose 2 + ∑ v ∈ S, G.degree v := by
  classical
  let T : Finset V := univ \ S
  let E := G.edgeFinset.filter (fun e => e.toFinset ⊆ T)
  have hsub : G.edgeFinset ⊆ E ∪ S.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    by_cases h : e.toFinset ⊆ T
    · exact mem_union_left _ (mem_filter.mpr ⟨he, h⟩)
    · obtain ⟨v, hv, hvT⟩ := Finset.not_subset.mp h
      have hvS : v ∈ S := by simpa [T] using hvT
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨v, hvS, ?_⟩
      rw [G.incidenceFinset_eq_filter]
      exact mem_filter.mpr ⟨he, by simpa using hv⟩
  have hE : E.card ≤ (Fintype.card V - S.card).choose 2 := by
    dsimp [E]
    rw [G.card_filter_edgeFinset_toFinset_subset]
    have hh := (G.induce (T : Set V)).card_edgeFinset_le_card_choose_two
    rw [Set.fintypeCard_eq_ncard, Set.ncard_coe_finset] at hh
    simpa only [T, card_sdiff_of_subset (subset_univ S), card_univ] using hh
  calc
    G.edgeFinset.card ≤ (E ∪ S.biUnion (fun v => G.incidenceFinset v)).card := card_le_card hsub
    _ ≤ E.card + (S.biUnion (fun v => G.incidenceFinset v)).card := card_union_le _ _
    _ ≤ (Fintype.card V - S.card).choose 2 + ∑ v ∈ S, (G.incidenceFinset v).card :=
      Nat.add_le_add hE card_biUnion_le
    _ = _ := by simp

/-- The isolated-vertex case has the sharper bound on the other `m - 1` vertices. -/
theorem edge_bound_of_degree_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hv : G.degree v = 0) :
    G.minDegree = 0 ∧ G.edgeFinset.card ≤ (Fintype.card V - 1).choose 2 := by
  constructor
  · have := G.minDegree_le_degree v
    omega
  · simpa [hv] using edge_bound_remove G {v}

private theorem max_nonedge_low_set (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (hne : u ≠ v) (hnadj : ¬G.Adj u v)
    (hclosed : G.degree u + G.degree v ≤ Fintype.card V - 1)
    (hmax : ∀ a b, a ≠ b → ¬G.Adj a b →
      G.degree a + G.degree b ≤ G.degree u + G.degree v) :
    ∃ S : Finset V, S.card = G.degree u ∧ ∀ x ∈ S, G.degree x ≤ G.degree u := by
  classical
  let T := (univ \ G.neighborFinset v).erase v
  have hcard : T.card = Fintype.card V - G.degree v - 1 := by
    dsimp [T]
    rw [card_erase_of_mem (by simp), card_sdiff_of_subset (subset_univ _)]
    simp
  have hle : G.degree u ≤ T.card := by rw [hcard]; omega
  obtain ⟨S, hST, hS⟩ := exists_subset_card_eq hle
  refine ⟨S, hS, ?_⟩
  intro x hx
  have hxT := hST hx
  have hxv : x ≠ v := (mem_erase.mp hxT).1
  have hxn : ¬G.Adj v x := by
    have hh := (mem_sdiff.mp (mem_erase.mp hxT).2).2
    simpa using hh
  have hh := hmax x v hxv (fun h => hxn h.symm)
  omega

/-- A noncomplete degree-sum-closed graph has the standard extremal edge bound. -/
theorem closedGraph_edge_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : 3 ≤ Fintype.card V) (hne : G ≠ ⊤)
    (hclosed : ∀ u v, u ≠ v → ¬G.Adj u v →
      G.degree u + G.degree v ≤ Fintype.card V - 1) :
    (G.minDegree = 0 ∧ G.edgeFinset.card ≤ (Fintype.card V - 1).choose 2) ∨
    ∃ t : ℕ, 1 ≤ t ∧ 2 * t ≤ Fintype.card V - 1 ∧ G.minDegree ≤ t ∧
      G.edgeFinset.card ≤ (Fintype.card V - t).choose 2 + t * t := by
  classical
  let P : Finset (V × V) := univ.filter (fun p => p.1 ≠ p.2 ∧ ¬G.Adj p.1 p.2)
  have hP : P.Nonempty := by
    obtain ⟨a, b, hab, hn⟩ := G.ne_top_iff_exists_not_adj.mp hne
    exact ⟨(a,b), by simp [P, hab, hn]⟩
  obtain ⟨p, hp, hmax⟩ := P.exists_max_image (fun p => G.degree p.1 + G.degree p.2) hP
  have hp' : p.1 ≠ p.2 ∧ ¬G.Adj p.1 p.2 := (mem_filter.mp hp).2
  have hm' : ∀ a b, a ≠ b → ¬G.Adj a b →
      G.degree a + G.degree b ≤ G.degree p.1 + G.degree p.2 := by
    intro a b hab hn
    exact hmax (a,b) (by simp [P, hab, hn])
  have H : ∀ u v, u ≠ v → ¬G.Adj u v → G.degree u ≤ G.degree v →
      (∀ a b, a ≠ b → ¬G.Adj a b →
        G.degree a + G.degree b ≤ G.degree u + G.degree v) →
      (G.minDegree = 0 ∧ G.edgeFinset.card ≤ (Fintype.card V - 1).choose 2) ∨
      ∃ t : ℕ, 1 ≤ t ∧ 2 * t ≤ Fintype.card V - 1 ∧ G.minDegree ≤ t ∧
        G.edgeFinset.card ≤ (Fintype.card V - t).choose 2 + t * t := by
    intro u v huv hn huvdeg hM
    by_cases hzero : G.degree u = 0
    · exact Or.inl (edge_bound_of_degree_zero G u hzero)
    · right
      have hc := hclosed u v huv hn
      obtain ⟨S, hS, hlow⟩ := max_nonedge_low_set G u v huv hn hc hM
      refine ⟨G.degree u, by omega, by omega, G.minDegree_le_degree u, ?_⟩
      have hsum : ∑ x ∈ S, G.degree x ≤ G.degree u * G.degree u := by
        calc
          ∑ x ∈ S, G.degree x ≤ ∑ _x ∈ S, G.degree u := sum_le_sum hlow
          _ = _ := by simp [hS]
      have hb := edge_bound_remove G S
      rw [hS] at hb
      exact hb.trans (Nat.add_le_add_left hsum _)
  rcases le_total (G.degree p.1) (G.degree p.2) with hle | hle
  · exact H p.1 p.2 hp'.1 hp'.2 hle hm'
  · apply H p.2 p.1 hp'.1.symm (fun h => hp'.2 h.symm) hle
    intro a b hab hn
    simpa [Nat.add_comm] using hm' a b hab hn

end JSP842

#print axioms JSP842.closedGraph_edge_bound
