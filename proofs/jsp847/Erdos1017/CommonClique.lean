import Erdos1017.PackingLoss

/-! Residual neighborhoods around a maximum common clique.
Original source implementation. UNCOMPILED. -/

namespace Erdos1017

variable {V : Type*} [DecidableEq V]

noncomputable def commonNeighbors (G : SimpleGraph V) (S : Finset V) (x y : V) : Finset V :=
  neighborsOn G S x ∩ neighborsOn G S y

noncomputable def residualNeighbors (G : SimpleGraph V) (S : Finset V)
    (x y : V) (Z : Finset V) : Finset V :=
  neighborsOn G S x \ insert y Z

theorem commonNeighbors_comm (G : SimpleGraph V) (S : Finset V) (x y : V) :
    commonNeighbors G S x y = commonNeighbors G S y x := Finset.inter_comm _ _

theorem residualNeighbors_subset (G : SimpleGraph V) (S : Finset V)
    (x y : V) (Z : Finset V) : residualNeighbors G S x y Z ⊆ S :=
  (Finset.sdiff_subset).trans (neighborsOn_subset G S x)

theorem residualNeighbors_not_left (G : SimpleGraph V) (S : Finset V)
    (x y : V) (Z : Finset V) : x ∉ residualNeighbors G S x y Z := by
  intro h
  exact not_mem_own_neighbors G S x (Finset.mem_sdiff.mp h).1

theorem residualNeighbors_not_right (G : SimpleGraph V) (S : Finset V)
    (x y : V) (Z : Finset V) : y ∉ residualNeighbors G S x y Z := by
  intro h
  exact (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self _ _)

theorem residualNeighbors_not_clique (G : SimpleGraph V) (S : Finset V)
    (x y : V) (Z : Finset V) {z : V} (hz : z ∈ Z) :
    z ∉ residualNeighbors G S x y Z := by
  intro h
  exact (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_of_mem hz)

theorem commonClique_not_apices {G : SimpleGraph V} {S Z : Finset V} {x y : V}
    (hZ : Z ⊆ commonNeighbors G S x y) : x ∉ Z ∧ y ∉ Z := by
  constructor
  · intro hx
    exact not_mem_own_neighbors G S x (Finset.mem_inter.mp (hZ hx)).1
  · intro hy
    exact not_mem_own_neighbors G S y (Finset.mem_inter.mp (hZ hy)).2

theorem residualNeighbors_card {G : SimpleGraph V} {S Z : Finset V} {x y : V}
    (hy : y ∈ S) (hxy : G.Adj x y) (hZ : Z ⊆ commonNeighbors G S x y) :
    (residualNeighbors G S x y Z).card + Z.card + 1 = (neighborsOn G S x).card := by
  classical
  have hsub : insert y Z ⊆ neighborsOn G S x := by
    apply Finset.insert_subset_iff.mpr
    exact ⟨Finset.mem_filter.mpr ⟨hy, hxy⟩,
      fun z hz => (Finset.mem_inter.mp (hZ hz)).1⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_insert_of_notMem (commonClique_not_apices hZ).2] at hcard
  simpa [residualNeighbors, Nat.add_assoc] using hcard

theorem residualNeighbors_nonneighbors_lt {G : SimpleGraph V} {S Z : Finset V}
    {x y : V} {k : ℕ} (hy : y ∈ S)
    (hZ : Z ⊆ commonNeighbors G S x y) (hZcl : IsClique G Z)
    (hmax : ∀ C : Finset V, C ⊆ commonNeighbors G S x y →
      IsClique G C → C.card ≤ Z.card)
    (hbudget : ∀ u ∈ S, (nonneighborsOn G S u).card ≤ k) :
    ∀ u ∈ residualNeighbors G S x y Z,
      (nonneighborsOn G (residualNeighbors G S x y Z) u).card < k := by
  classical
  intro u hu
  have huS := residualNeighbors_subset G S x y Z hu
  have huNx := (Finset.mem_sdiff.mp hu).1
  have huZ : u ∉ Z := by
    intro h
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_insert_of_mem h)
  have huy : u ≠ y := by
    intro h
    subst u
    exact residualNeighbors_not_right G S x y Z hu
  by_cases hmiss : ¬ G.Adj u y
  · exact nonneighbors_lt_of_outside G (residualNeighbors_subset G S x y Z)
      (hbudget u huS) hy huy hmiss (residualNeighbors_not_right G S x y Z)
  · have huyAdj : G.Adj u y := not_not.mp hmiss
    have huCommon : u ∈ commonNeighbors G S x y :=
      Finset.mem_inter.mpr ⟨huNx, Finset.mem_filter.mpr ⟨huS, huyAdj.symm⟩⟩
    obtain ⟨z, hz, huzMiss⟩ := maximum_clique_outside_misses hZ hZcl hmax huCommon huZ
    have hzS : z ∈ S := neighborsOn_subset G S x (Finset.mem_inter.mp (hZ hz)).1
    have huz : u ≠ z := by intro h; subst u; exact huZ hz
    exact nonneighbors_lt_of_outside G (residualNeighbors_subset G S x y Z)
      (hbudget u huS) hzS huz huzMiss (residualNeighbors_not_clique G S x y Z hz)

theorem commonClique_with_apices {G : SimpleGraph V} {S Z : Finset V} {x y : V}
    (hxy : G.Adj x y) (hZ : Z ⊆ commonNeighbors G S x y) (hZcl : IsClique G Z) :
    IsClique G (insert x (insert y Z)) := by
  classical
  apply insert_isClique
  · apply insert_isClique hZcl
    intro z hz
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp (hZ hz)).2).2
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hxy
    · exact (Finset.mem_filter.mp (Finset.mem_inter.mp (hZ hu)).1).2

theorem commonClique_with_apices_card {G : SimpleGraph V} {S Z : Finset V} {x y : V}
    (hxy : G.Adj x y) (hZ : Z ⊆ commonNeighbors G S x y) :
    (insert x (insert y Z)).card = Z.card + 2 := by
  classical
  have h := commonClique_not_apices hZ
  simp [h.1, h.2, hxy.ne, Nat.add_assoc]

end Erdos1017
