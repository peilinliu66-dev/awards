import Erdos1017.FiniteNeighborhoods

/-! Exact nonneighbor accounting for deleting cones with a common apex.
Original source implementation. UNCOMPILED. -/

namespace Erdos1017

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

namespace CliquePacking

noncomputable def lostNeighbors (P : CliquePacking G) (B : Finset V) (u : V) : Finset V := by
  classical
  exact B.filter (fun v => u ≠ v ∧ P.OwnsEdge u v)

theorem nonneighbors_remainder_subset (P : CliquePacking G) (B : Finset V) (u : V) :
    nonneighborsOn P.remainder B u ⊆
      nonneighborsOn G B u ∪ P.lostNeighbors B u := by
  classical
  intro v hv
  obtain ⟨hvB, huv, hrem⟩ := Finset.mem_filter.mp hv
  by_cases hG : G.Adj u v
  · have hown : P.OwnsEdge u v := by
      by_contra hn
      exact hrem ⟨hG, hn⟩
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvB, huv, hown⟩)
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvB, huv, hG⟩)

/-- One cone fiber can remove at most t−1 incident edges at a vertex in B.
The premise bounds its actual intersection with B, not its ambient size. -/
theorem lostNeighbors_card_le (P : CliquePacking G) (B : Finset V) (x : V) (t : ℕ)
    (hx : x ∉ B) (hroot : ∀ C ∈ P.blocks, x ∈ C)
    (hsize : ∀ C ∈ P.blocks, (C ∩ B).card ≤ t)
    {u : V} (huB : u ∈ B) : (P.lostNeighbors B u).card ≤ t - 1 := by
  classical
  by_cases hex : ∃ C ∈ P.blocks, u ∈ C
  · obtain ⟨C, hC, huC⟩ := hex
    have hux : u ≠ x := by intro h; subst u; exact hx huB
    have hsub : P.lostNeighbors B u ⊆ (C ∩ B).erase u := by
      intro v hv
      obtain ⟨hvB, huv, D, hD, huD, hvD⟩ := Finset.mem_filter.mp hv
      have hDC : D = C := P.unique D hD C hC u huD x (hroot D hD)
        huC (hroot C hC) hux
      subst D
      exact Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_inter.mpr ⟨hvD, hvB⟩⟩
    have hcard := Finset.card_le_card hsub
    have hmem : u ∈ C ∩ B := Finset.mem_inter.mpr ⟨huC, huB⟩
    have heq := Finset.card_erase_add_one hmem
    have hbound := hsize C hC
    omega
  · have hempty : P.lostNeighbors B u = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨_, _, C, hC, huC, _⟩ := Finset.mem_filter.mp hv
      exact hex ⟨C, hC, huC⟩
    simp [hempty]

theorem nonneighbors_remainder_lt (P : CliquePacking G) (B : Finset V)
    (x : V) (k t : ℕ) (hx : x ∉ B) (hroot : ∀ C ∈ P.blocks, x ∈ C)
    (hsize : ∀ C ∈ P.blocks, (C ∩ B).card ≤ t)
    (hbad : ∀ u ∈ B, (nonneighborsOn G B u).card < k) :
    ∀ u ∈ B, (nonneighborsOn P.remainder B u).card < k + (t - 1) := by
  intro u hu
  have h1 := Finset.card_le_card (P.nonneighbors_remainder_subset B u)
  have h2 : (nonneighborsOn G B u ∪ P.lostNeighbors B u).card ≤
      (nonneighborsOn G B u).card + (P.lostNeighbors B u).card :=
    Finset.card_union_le _ _
  have h3 := P.lostNeighbors_card_le B x t hx hroot hsize hu
  have h4 := hbad u hu
  omega

/-- A packing cannot delete an edge touching a vertex outside every block. -/
theorem remainder_adj_of_outside (P : CliquePacking G) {S : Finset V}
    (hsub : ∀ C ∈ P.blocks, C ⊆ S) {u v : V} (hu : u ∉ S) :
    P.remainder.Adj u v ↔ G.Adj u v := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rintro ⟨C, hC, huC, _⟩
    exact hu (hsub C hC huC)

end CliquePacking

end Erdos1017
