import Erdos1017.ConePacking

/-! Active vertex sets, nonneighbor budgets, and maximum common cliques.
Original source implementation. UNCOMPILED. -/

namespace Erdos1017

variable {V : Type*} [DecidableEq V]

def SupportedOn (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u v, G.Adj u v → u ∈ S ∧ v ∈ S

noncomputable def neighborsOn (G : SimpleGraph V) (S : Finset V) (u : V) : Finset V := by
  classical
  exact S.filter (G.Adj u)

theorem neighborsOn_subset (G : SimpleGraph V) (S : Finset V) (u : V) :
    neighborsOn G S u ⊆ S := by
  classical
  exact Finset.filter_subset _ _

@[simp] theorem not_mem_own_neighbors (G : SimpleGraph V) (S : Finset V) (u : V) :
    u ∉ neighborsOn G S u := by
  classical
  simp [neighborsOn]

theorem neighbor_nonneighbor_card (G : SimpleGraph V) (S : Finset V) {u : V}
    (hu : u ∈ S) :
    (neighborsOn G S u).card + (nonneighborsOn G S u).card + 1 = S.card := by
  classical
  have heq : (S.filter fun v => ¬ G.Adj u v) = insert u (nonneighborsOn G S u) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, nonneighborsOn]
    constructor
    · rintro ⟨hv, hnv⟩
      by_cases huv : u = v
      · exact Or.inl huv.symm
      · exact Or.inr ⟨hv, huv, hnv⟩
    · rintro (hvu | ⟨hv, _, hnv⟩)
      · subst v
        exact ⟨hu, G.loopless.irrefl u⟩
      · exact ⟨hv, hnv⟩
  have hnot : u ∉ nonneighborsOn G S u := by simp [nonneighborsOn]
  have h := Finset.card_filter_add_card_filter_not (s := S) (G.Adj u)
  rw [heq, Finset.card_insert_of_notMem hnot] at h
  simpa [neighborsOn, Nat.add_assoc] using h

theorem exists_max_nonneighbors (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty) :
    ∃ x ∈ S, ∀ u ∈ S,
      (nonneighborsOn G S u).card ≤ (nonneighborsOn G S x).card := by
  classical
  exact Finset.exists_max_image S (fun u => (nonneighborsOn G S u).card) hS

/-- An outside nonneighbor supplies the strict unit of slack for clique coloring. -/
theorem nonneighbors_lt_of_outside (G : SimpleGraph V) {S R : Finset V}
    (hRS : R ⊆ S) {u w : V} {k : ℕ}
    (hbudget : (nonneighborsOn G S u).card ≤ k)
    (hw : w ∈ S) (huw : u ≠ w) (hmiss : ¬ G.Adj u w) (hwR : w ∉ R) :
    (nonneighborsOn G R u).card < k := by
  classical
  have hsub : insert w (nonneighborsOn G R u) ⊆ nonneighborsOn G S u := by
    apply Finset.insert_subset_iff.mpr
    exact ⟨Finset.mem_filter.mpr ⟨hw, huw, hmiss⟩,
      nonneighborsOn_mono G hRS u⟩
  have hnot : w ∉ nonneighborsOn G R u := by
    intro h
    exact hwR (Finset.mem_filter.mp h).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hcard
  omega

/-- A maximum clique exists in any finite set, including the empty set. -/
theorem exists_maximum_clique (G : SimpleGraph V) (S : Finset V) :
    ∃ Z : Finset V, Z ⊆ S ∧ IsClique G Z ∧
      ∀ C : Finset V, C ⊆ S → IsClique G C → C.card ≤ Z.card := by
  classical
  let T := S.powerset.filter (IsClique G)
  have hT : T.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    intro u hu
    simp at hu
  obtain ⟨Z, hZ, hmax⟩ := Finset.exists_max_image T Finset.card hT
  obtain ⟨hZS, hZcl⟩ := Finset.mem_filter.mp hZ
  refine ⟨Z, Finset.mem_powerset.mp hZS, hZcl, ?_⟩
  intro C hCS hCcl
  exact hmax C (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hCS, hCcl⟩)

theorem maximum_clique_outside_misses {G : SimpleGraph V} {S Z : Finset V}
    (hZS : Z ⊆ S) (hZ : IsClique G Z)
    (hmax : ∀ C : Finset V, C ⊆ S → IsClique G C → C.card ≤ Z.card)
    {u : V} (hu : u ∈ S) (huZ : u ∉ Z) : ∃ z ∈ Z, ¬ G.Adj u z := by
  classical
  by_contra hnone
  have hadj : ∀ z ∈ Z, G.Adj u z := by
    intro z hz
    by_contra hmiss
    exact hnone ⟨z, hz, hmiss⟩
  have hcard := hmax (insert u Z)
    (Finset.insert_subset_iff.mpr ⟨hu, hZS⟩) (insert_isClique hZ hadj)
  rw [Finset.card_insert_of_notMem huZ] at hcard
  omega

end Erdos1017
