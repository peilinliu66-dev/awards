import Mathlib

/-! A finite list-coloring lemma used in the formalization of Erdős 799.
The result below is a finite combinatorial ingredient, not the asymptotic theorem.
-/

open Finset

namespace JSP656

/-- Hall's condition follows by double counting if every list has at least `s`
colors and each color occurs in at most `s` lists. -/
theorem exists_injective_of_bounded_list_multiplicity
    {V C : Type*} [Fintype V] [DecidableEq C]
    (L : V → Finset C) (s : ℕ) (hs : 0 < s)
    (hL : ∀ v, s ≤ (L v).card)
    (hC : ∀ c, (univ.filter (fun v => c ∈ L v)).card ≤ s) :
    ∃ f : V → C, Function.Injective f ∧ ∀ v, f v ∈ L v := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp
  intro U
  have hcount : U.card * s ≤ (U.biUnion L).card * s := by
    apply Finset.card_mul_le_card_mul (fun v c => c ∈ L v)
    · intro v hv
      have heq : (U.biUnion L).bipartiteAbove (fun v c => c ∈ L v) v = L v := by
        ext c
        simp only [Finset.mem_bipartiteAbove, Finset.mem_biUnion]
        constructor
        · exact fun h => h.2
        · exact fun hc => ⟨⟨v, hv, hc⟩, hc⟩
      rw [heq]
      exact hL v
    · intro c _
      exact (Finset.card_le_card (by
        intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
          (Finset.mem_filter.mp hv).2⟩)).trans (hC c)
  exact (mul_le_mul_iff_left₀ hs).mp hcount

/-- Finite list coloring from a uniform independent-set extraction property.
The integer budget `k` satisfies `|A| ≤ k*m`; this deliberately uses a ceiling
bound rather than a sharp floor bound to avoid unnecessary endpoint cases. -/
theorem exists_list_coloring_of_independent_subsets
    {V C : Type*} [DecidableEq V] [DecidableEq C] [Nonempty C]
    (G : SimpleGraph V) (m s : ℕ) (hm : 0 < m) (hs : 0 < s)
    (k : ℕ) (A : Finset V) (L : V → Finset C)
    (hcard : A.card ≤ k * m)
    (hind : ∀ U : Finset V, U ⊆ A → s ≤ U.card →
      ∃ I : Finset V, I ⊆ U ∧ I.card = m ∧
        ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v)
    (hL : ∀ v ∈ A, k + s ≤ (L v).card) :
    ∃ f : V → C, (∀ v ∈ A, f v ∈ L v) ∧
      ∀ u ∈ A, ∀ v ∈ A, G.Adj u v → f u ≠ f v := by
  classical
  induction k generalizing A L with
  | zero =>
      have hA : A = ∅ := Finset.card_eq_zero.mp (by simpa using hcard)
      subst A
      exact ⟨fun _ => Classical.arbitrary C, by simp, by simp⟩
  | succ k ih =>
      by_cases hfreq : ∃ c : C, s ≤ (A.filter (fun v => c ∈ L v)).card
      · obtain ⟨c, hc⟩ := hfreq
        obtain ⟨I, hIfilter, hIcard, hIind⟩ :=
          hind (A.filter (fun v => c ∈ L v)) (Finset.filter_subset _ _) hc
        have hIA : I ⊆ A := hIfilter.trans (Finset.filter_subset _ _)
        have hIc : ∀ v ∈ I, c ∈ L v := fun v hv =>
          (Finset.mem_filter.mp (hIfilter hv)).2
        have hrest : (A \ I).card ≤ k * m := by
          rw [Finset.card_sdiff_of_subset hIA, hIcard]
          have he : (k + 1) * m = k * m + m := by ring
          rw [he] at hcard
          omega
        have hrestInd : ∀ U : Finset V, U ⊆ A \ I → s ≤ U.card →
            ∃ J : Finset V, J ⊆ U ∧ J.card = m ∧
              ∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v := by
          intro U hU hUs
          exact hind U (hU.trans Finset.sdiff_subset) hUs
        have hrestL : ∀ v ∈ A \ I, k + s ≤ ((L v).erase c).card := by
          intro v hv
          have hvA := (Finset.mem_sdiff.mp hv).1
          have hvL := hL v hvA
          by_cases hcL : c ∈ L v
          · rw [Finset.card_erase_of_mem hcL]
            omega
          · rw [Finset.erase_eq_of_notMem hcL]
            omega
        obtain ⟨f, hfL, hfG⟩ := ih (A \ I) (fun v => (L v).erase c)
          hrest hrestInd hrestL
        refine ⟨fun v => if v ∈ I then c else f v, ?_, ?_⟩
        · intro v hv
          by_cases hvI : v ∈ I
          · simp only [if_pos hvI]
            exact hIc v hvI
          · simp only [if_neg hvI]
            exact (Finset.mem_erase.mp (hfL v (Finset.mem_sdiff.mpr ⟨hv, hvI⟩))).2
        · intro u hu v hv huv
          by_cases huI : u ∈ I <;> by_cases hvI : v ∈ I
          · exact False.elim (hIind u huI v hvI huv)
          · simp only [if_pos huI, if_neg hvI]
            exact (Finset.mem_erase.mp (hfL v (Finset.mem_sdiff.mpr ⟨hv, hvI⟩))).1.symm
          · simp only [if_neg huI, if_pos hvI]
            exact (Finset.mem_erase.mp (hfL u (Finset.mem_sdiff.mpr ⟨hu, huI⟩))).1
          · simp only [if_neg huI, if_neg hvI]
            exact hfG u (Finset.mem_sdiff.mpr ⟨hu, huI⟩)
              v (Finset.mem_sdiff.mpr ⟨hv, hvI⟩) huv
      · have hrare : ∀ c : C, (A.filter (fun v => c ∈ L v)).card ≤ s := by
          intro c
          exact (Nat.lt_of_not_ge (fun hc => hfreq ⟨c, hc⟩)).le
        have hsubrare : ∀ c : C,
            (univ.filter (fun v : A => c ∈ L v)).card ≤ s := by
          intro c
          calc
            (univ.filter (fun v : A => c ∈ L v)).card =
                ((univ.filter (fun v : A => c ∈ L v)).image Subtype.val).card :=
              (Finset.card_image_of_injective _ Subtype.val_injective).symm
            _ ≤ (A.filter (fun v => c ∈ L v)).card := by
              apply Finset.card_le_card
              intro v hv
              obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
              exact Finset.mem_filter.mpr ⟨w.property, (Finset.mem_filter.mp hw).2⟩
            _ ≤ s := hrare c
        obtain ⟨f, hfinj, hfL⟩ := exists_injective_of_bounded_list_multiplicity
          (fun v : A => L v) s hs (fun v => (Nat.le_add_left s (k + 1)).trans
            (hL v v.property)) hsubrare
        refine ⟨fun v => if hv : v ∈ A then f ⟨v, hv⟩ else Classical.arbitrary C, ?_, ?_⟩
        · intro v hv
          simpa only [dif_pos hv] using hfL ⟨v, hv⟩
        · intro u hu v hv huv heq
          simp only [dif_pos hu, dif_pos hv] at heq
          have huvEq : u = v := congrArg Subtype.val (hfinj heq)
          exact G.ne_of_adj huv huvEq

#print axioms exists_injective_of_bounded_list_multiplicity
#print axioms exists_list_coloring_of_independent_subsets

end JSP656
