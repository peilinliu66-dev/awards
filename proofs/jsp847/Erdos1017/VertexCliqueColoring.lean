import Erdos1017.Definitions

/-!
Elementary finite greedy coloring of the complement. This is Lemma4 of
Győri–Kostochka (1979), in a form with a strict bound on nonneighbors.
Original source implementation. UNCOMPILED.
-/

namespace Erdos1017

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- Other vertices of S not adjacent to u. -/
noncomputable def nonneighborsOn (G : SimpleGraph V) (S : Finset V) (u : V) : Finset V := by
  classical
  exact S.filter (fun v => u ≠ v ∧ ¬ G.Adj u v)

theorem nonneighborsOn_mono (G : SimpleGraph V) {S T : Finset V}
    (hST : S ⊆ T) (u : V) : nonneighborsOn G S u ⊆ nonneighborsOn G T u := by
  classical
  intro v hv
  simp only [nonneighborsOn, Finset.mem_filter] at hv ⊢
  exact ⟨hST hv.1, hv.2⟩

/-- At most k−1 nonneighbors per vertex suffice for k vertex-clique classes.
The color function is defined on the ambient type, with its range constrained
only on S. This allows S=∅ and k=0 without inventing a color.
-/
theorem exists_clique_coloring (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    (hdeg : ∀ u ∈ S, (nonneighborsOn G S u).card < k) :
    ∃ f : V → ℕ,
      (∀ u ∈ S, f u < k) ∧
      (∀ u ∈ S, ∀ v ∈ S, u ≠ v → f u = f v → G.Adj u v) := by
  classical
  revert hdeg
  induction S using Finset.induction_on with
  | empty =>
      intro hdeg
      exact ⟨fun _ => 0, by simp, by simp⟩
  | @insert a S ha ih =>
      intro hdeg
      have hdegS : ∀ u ∈ S, (nonneighborsOn G S u).card < k := by
        intro u hu
        exact lt_of_le_of_lt
          (Finset.card_le_card (nonneighborsOn_mono G (Finset.subset_insert a S) u))
          (hdeg u (Finset.mem_insert_of_mem hu))
      obtain ⟨f, hf, hclique⟩ := ih hdegS
      let bad : Finset V := S.filter (fun v => ¬ G.Adj a v)
      have hbad : bad ⊆ nonneighborsOn G (insert a S) a := by
        intro v hv
        obtain ⟨hvS, hva⟩ := Finset.mem_filter.mp hv
        have hav : a ≠ v := by intro h; subst v; exact ha hvS
        exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hvS, hav, hva⟩
      have hcard : (bad.image f).card < k :=
        lt_of_le_of_lt (Finset.card_image_le.trans (Finset.card_le_card hbad))
          (hdeg a (Finset.mem_insert_self _ _))
      have hnot : ¬ Finset.range k ⊆ bad.image f := by
        intro hsub
        have hle := Finset.card_le_card hsub
        simp only [Finset.card_range] at hle
        omega
      obtain ⟨c, hck, hc⟩ := Finset.not_subset.mp hnot
      have hck' : c < k := Finset.mem_range.mp hck
      have hgood : ∀ v ∈ S, c = f v → G.Adj a v := by
        intro v hv hcv
        by_contra hnv
        apply hc
        exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hnv⟩, hcv.symm⟩
      refine ⟨Function.update f a c, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · simpa using hck'
        · have hua : u ≠ a := by intro h; subst u; exact ha hu
          simpa [Function.update, hua] using hf u hu
      · intro u hu v hv huv heq
        rcases Finset.mem_insert.mp hu with huaEq | hu
        · subst u
          have hva : v ≠ a := Ne.symm huv
          have hvS : v ∈ S := (Finset.mem_insert.mp hv).resolve_left hva
          apply hgood v hvS
          simpa [Function.update, hva] using heq
        · have hua : u ≠ a := by intro h; subst u; exact ha hu
          rcases Finset.mem_insert.mp hv with hvaEq | hv
          · subst v
            exact (hgood u hu (by simpa [Function.update, hua] using heq.symm)).symm
          · have hva : v ≠ a := by intro h; subst v; exact ha hv
            apply hclique u hu v hv huv
            simpa [Function.update, hua, hva] using heq

/-- Nonempty classes of a bounded clique coloring. -/
noncomputable def colorClasses (S : Finset V) (f : V → ℕ) : Finset (Finset V) := by
  classical
  exact (S.image f).image (fun c => S.filter (fun v => f v = c))

theorem mem_colorClasses {S : Finset V} {f : V → ℕ} {C : Finset V}
    (hC : C ∈ colorClasses S f) :
    ∃ c ∈ S.image f, C = S.filter (fun v => f v = c) := by
  classical
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hC
  exact ⟨c, hc, rfl⟩

theorem colorClasses_nonempty {S : Finset V} {f : V → ℕ} {C : Finset V}
    (hC : C ∈ colorClasses S f) : C.Nonempty := by
  classical
  obtain ⟨c, hc, rfl⟩ := mem_colorClasses hC
  obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hc
  exact ⟨u, Finset.mem_filter.mpr ⟨hu, hfu⟩⟩

theorem colorClasses_subset {S : Finset V} {f : V → ℕ} {C : Finset V}
    (hC : C ∈ colorClasses S f) : C ⊆ S := by
  classical
  obtain ⟨c, _, rfl⟩ := mem_colorClasses hC
  exact Finset.filter_subset _ _

theorem colorClasses_card_le {S : Finset V} {f : V → ℕ} {k : ℕ}
    (hf : ∀ u ∈ S, f u < k) : (colorClasses S f).card ≤ k := by
  classical
  have hsub : S.image f ⊆ Finset.range k := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_range.mpr (hf u hu)
  exact Finset.card_image_le.trans (by simpa using Finset.card_le_card hsub)

theorem colorClasses_clique {G : SimpleGraph V} {S : Finset V} {f : V → ℕ}
    (hf : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → f u = f v → G.Adj u v)
    {C : Finset V} (hC : C ∈ colorClasses S f) : IsClique G C := by
  classical
  obtain ⟨c, _, rfl⟩ := mem_colorClasses hC
  intro u hu v hv huv
  obtain ⟨huS, huc⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvS, hvc⟩ := Finset.mem_filter.mp hv
  exact hf u huS v hvS huv (huc.trans hvc.symm)

theorem colorClasses_unique {S : Finset V} {f : V → ℕ} {u : V} (hu : u ∈ S) :
    ∃! C, C ∈ colorClasses S f ∧ u ∈ C := by
  classical
  refine ⟨S.filter (fun v => f v = f u), ?_, ?_⟩
  · exact ⟨Finset.mem_image.mpr ⟨f u, Finset.mem_image_of_mem f hu, rfl⟩,
      Finset.mem_filter.mpr ⟨hu, rfl⟩⟩
  · intro C hC
    obtain ⟨c, _, rfl⟩ := mem_colorClasses hC.1
    have hc := (Finset.mem_filter.mp hC.2).2
    simp [hc]

theorem colorClasses_sum_card (S : Finset V) (f : V → ℕ) :
    ∑ C ∈ colorClasses S f, C.card = S.card := by
  classical
  have hinj : Set.InjOn (fun c => S.filter (fun v => f v = c)) (↑(S.image f)) := by
    intro c hc d hd hcd
    obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hc
    have hmem : u ∈ S.filter (fun v => f v = c) :=
      Finset.mem_filter.mpr ⟨hu, hfu⟩
    change S.filter (fun v => f v = c) = S.filter (fun v => f v = d) at hcd
    rw [hcd] at hmem
    exact hfu.symm.trans (Finset.mem_filter.mp hmem).2
  unfold colorClasses
  rw [Finset.sum_image hinj]
  exact (Finset.card_eq_sum_card_image f S).symm

end Erdos1017
