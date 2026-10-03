import Erdos1017.Packing
import Erdos1017.VertexCliqueColoring

/-! Coning disjoint vertex-clique classes over one neighboring vertex.
Original source implementation. UNCOMPILED. -/

open scoped BigOperators

namespace Erdos1017

variable {V : Type*} [DecidableEq V]

theorem insert_isClique {G : SimpleGraph V} {x : V} {C : Finset V}
    (hC : IsClique G C) (hx : ∀ u ∈ C, G.Adj x u) : IsClique G (insert x C) := by
  intro u hu v hv huv
  rcases Finset.mem_insert.mp hu with hux | hu
  · subst u
    rcases Finset.mem_insert.mp hv with hvx | hv
    · exact False.elim (huv hvx.symm)
    · exact hx v hv
  · rcases Finset.mem_insert.mp hv with hvx | hv
    · subst v
      exact (hx u hu).symm
    · exact hC u hu v hv huv

theorem insert_injective_on_subsets {S : Finset V} {x : V} (hx : x ∉ S)
    {C D : Finset V} (hC : C ⊆ S) (hD : D ⊆ S)
    (h : insert x C = insert x D) : C = D := by
  apply Finset.ext
  intro u
  constructor <;> intro hu
  · have hux : u ≠ x := by intro hux; subst u; exact hx (hC hu)
    have hm : u ∈ insert x D := by rw [← h]; exact Finset.mem_insert_of_mem hu
    exact (Finset.mem_insert.mp hm).resolve_left hux
  · have hux : u ≠ x := by intro hux; subst u; exact hx (hD hu)
    have hm : u ∈ insert x C := by rw [h]; exact Finset.mem_insert_of_mem hu
    exact (Finset.mem_insert.mp hm).resolve_left hux

noncomputable def conePacking (G : SimpleGraph V) (x : V) (S : Finset V)
    (f : V → ℕ) (hx : x ∉ S)
    (hadj : ∀ u ∈ S, G.Adj x u)
    (hcolor : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → f u = f v → G.Adj u v) :
    CliquePacking G := by
  classical
  refine ⟨(colorClasses S f).image (insert x), ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    have hxD : x ∉ D := fun h => hx (colorClasses_subset hD h)
    have hpos := Finset.card_pos.mpr (colorClasses_nonempty hD)
    rw [Finset.card_insert_of_notMem hxD]
    omega
  · intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    exact insert_isClique (colorClasses_clique hcolor hD)
      (fun u hu => hadj u (colorClasses_subset hD hu))
  · intro C hC D hD u huC v hvC huD hvD huv
    obtain ⟨C', hC', rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨D', hD', rfl⟩ := Finset.mem_image.mp hD
    have hshared : ∃ w, w ∈ C' ∧ w ∈ D' := by
      by_cases hux : u = x
      · subst u
        have hvx : v ≠ x := Ne.symm huv
        exact ⟨v, (Finset.mem_insert.mp hvC).resolve_left hvx,
          (Finset.mem_insert.mp hvD).resolve_left hvx⟩
      · exact ⟨u, (Finset.mem_insert.mp huC).resolve_left hux,
          (Finset.mem_insert.mp huD).resolve_left hux⟩
    obtain ⟨w, hwC, hwD⟩ := hshared
    obtain ⟨E, _, hE⟩ := colorClasses_unique (colorClasses_subset hC' hwC)
    have hCD : C' = D' :=
      (hE C' ⟨hC', hwC⟩).trans (hE D' ⟨hD', hwD⟩).symm
    exact congrArg (insert x) hCD

theorem conePacking_weight (G : SimpleGraph V) (x : V) (S : Finset V)
    (f : V → ℕ) (hx : x ∉ S) (hadj : ∀ u ∈ S, G.Adj x u)
    (hcolor : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → f u = f v → G.Adj u v) :
    (conePacking G x S f hx hadj hcolor).weight =
      S.card + (colorClasses S f).card := by
  classical
  have hinj : Set.InjOn (fun C : Finset V => insert x C) (↑(colorClasses S f)) := by
    intro C hC D hD hCD
    exact insert_injective_on_subsets hx (colorClasses_subset hC)
      (colorClasses_subset hD) hCD
  change (∑ C ∈ (colorClasses S f).image (insert x), C.card) = _
  rw [Finset.sum_image hinj]
  calc
    ∑ C ∈ colorClasses S f, (insert x C).card =
        ∑ C ∈ colorClasses S f, (C.card + 1) := by
      apply Finset.sum_congr rfl
      intro C hC
      exact Finset.card_insert_of_notMem (fun h => hx (colorClasses_subset hC h))
    _ = S.card + (colorClasses S f).card := by
      simp [Finset.sum_add_distrib, colorClasses_sum_card]

theorem conePacking_owns_star (G : SimpleGraph V) (x : V) (S : Finset V)
    (f : V → ℕ) (hx : x ∉ S) (hadj : ∀ u ∈ S, G.Adj x u)
    (hcolor : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → f u = f v → G.Adj u v)
    {u : V} (hu : u ∈ S) :
    (conePacking G x S f hx hadj hcolor).OwnsEdge x u := by
  classical
  obtain ⟨C, hC, _⟩ := colorClasses_unique (f := f) hu
  exact ⟨insert x C, Finset.mem_image.mpr ⟨C, hC.1, rfl⟩,
    Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hC.2⟩

theorem exists_conePacking_weight_le (G : SimpleGraph V) (x : V) (S : Finset V)
    (k : ℕ) (hx : x ∉ S) (hadj : ∀ u ∈ S, G.Adj x u)
    (hdeg : ∀ u ∈ S, (nonneighborsOn G S u).card < k) :
    ∃ P : CliquePacking G,
      P.weight ≤ S.card + k ∧
      (∀ u ∈ S, P.OwnsEdge x u) ∧
      (∀ C ∈ P.blocks, x ∈ C ∧ C ⊆ insert x S) := by
  classical
  obtain ⟨f, hf, hcolor⟩ := exists_clique_coloring G S k hdeg
  let P := conePacking G x S f hx hadj hcolor
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [conePacking_weight]
    exact Nat.add_le_add_left (colorClasses_card_le hf) _
  · exact fun u hu => conePacking_owns_star G x S f hx hadj hcolor hu
  · intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨Finset.mem_insert_self _ _,
      Finset.insert_subset_insert x (colorClasses_subset hD)⟩

end Erdos1017
