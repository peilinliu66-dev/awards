import JSP656ListColoring

/-! The actual list chromatic number of a finite simple graph. Lists use natural
number colors in the definition; the bridge below proves equivalence with lists
over arbitrary color types, since their finite union can be relabeled.
-/

open Finset

namespace JSP656

variable {V : Type*}

/-- A proper coloring selecting a color from every prescribed list. -/
def ListColorable (G : SimpleGraph V) (L : V → Finset ℕ) : Prop :=
  ∃ f : G.Coloring ℕ, ∀ v, f v ∈ L v

/-- `k`-choosability, with lists of size at least `k`. -/
def KChoosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, k ≤ (L v).card) → ListColorable G L

theorem KChoosable.mono {G : SimpleGraph V} {k l : ℕ}
    (h : KChoosable G k) (hkl : k ≤ l) : KChoosable G l := by
  intro L hL
  exact h L (fun v => hkl.trans (hL v))

/-- Every finite graph is choosable from lists of size at least its order. -/
theorem kChoosable_card [Fintype V] (G : SimpleGraph V) :
    KChoosable G (Fintype.card V) := by
  classical
  intro L hL
  have hHall : ∀ U : Finset V, U.card ≤ (U.biUnion L).card := by
    intro U
    rcases U.eq_empty_or_nonempty with hU | ⟨v, hv⟩
    · simp [hU]
    · calc
        U.card ≤ Fintype.card V := Finset.card_le_univ U
        _ ≤ (L v).card := hL v
        _ ≤ (U.biUnion L).card := Finset.card_le_card (by
          intro c hc
          exact Finset.mem_biUnion.mpr ⟨v, hv, hc⟩)
  obtain ⟨f, hfinj, hfL⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp hHall
  exact ⟨SimpleGraph.Coloring.mk f (fun huv heq => G.ne_of_adj huv (hfinj heq)), hfL⟩

theorem exists_kChoosable [Fintype V] (G : SimpleGraph V) :
    ∃ k : ℕ, KChoosable G k := ⟨Fintype.card V, kChoosable_card G⟩

/-- The list chromatic number: the least integer for which every list assignment
of that minimum size has a proper list coloring. -/
noncomputable def choiceNumber [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact Nat.find (exists_kChoosable G)

theorem kChoosable_choiceNumber [Fintype V] (G : SimpleGraph V) :
    KChoosable G (choiceNumber G) := by
  classical
  exact Nat.find_spec (exists_kChoosable G)

theorem choiceNumber_le_of_kChoosable [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : KChoosable G k) : choiceNumber G ≤ k := by
  classical
  exact Nat.find_min' (exists_kChoosable G) h

theorem choiceNumber_le_iff [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    choiceNumber G ≤ k ↔ KChoosable G k := by
  constructor
  · exact (kChoosable_choiceNumber G).mono
  · exact choiceNumber_le_of_kChoosable

theorem choiceNumber_le_card [Fintype V] (G : SimpleGraph V) :
    choiceNumber G ≤ Fintype.card V :=
  choiceNumber_le_of_kChoosable (kChoosable_card G)

/-- Relabel any injectively encodable color type by natural numbers. -/
theorem KChoosable.color_lists_of_injective
    {G : SimpleGraph V} {k : ℕ} (h : KChoosable G k)
    {C : Type*} [DecidableEq C] (e : C → ℕ) (he : Function.Injective e)
    (L : V → Finset C) (hL : ∀ v, k ≤ (L v).card) :
    ∃ f : G.Coloring C, ∀ v, f v ∈ L v := by
  classical
  obtain ⟨g, hg⟩ := h (fun v => (L v).image e) (fun v => by
    rw [Finset.card_image_of_injective _ he]
    exact hL v)
  have hpre : ∀ v, ∃ c, c ∈ L v ∧ e c = g v := by
    intro v
    exact Finset.mem_image.mp (hg v)
  choose f hfL hfg using hpre
  refine ⟨SimpleGraph.Coloring.mk f ?_, hfL⟩
  intro u v huv hEq
  apply g.valid huv
  rw [← hfg u, ← hfg v, hEq]

theorem KChoosable.color_lists_finite
    {G : SimpleGraph V} {k : ℕ} (h : KChoosable G k)
    {C : Type*} [Fintype C] [DecidableEq C]
    (L : V → Finset C) (hL : ∀ v, k ≤ (L v).card) :
    ∃ f : G.Coloring C, ∀ v, f v ∈ L v := by
  classical
  exact h.color_lists_of_injective
    (fun c => (Fintype.equivFin C c).val)
    (Fin.val_injective.comp (Fintype.equivFin C).injective) L hL

/-- For a finite graph, natural-number choosability suffices for arbitrary
color types: only the finite union of the input lists is needed. -/
theorem KChoosable.color_lists [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (h : KChoosable G k)
    {C : Type*} [DecidableEq C]
    (L : V → Finset C) (hL : ∀ v, k ≤ (L v).card) :
    ∃ f : G.Coloring C, ∀ v, f v ∈ L v := by
  classical
  let T : Finset C := univ.biUnion L
  have hT : ∀ v, ∀ c ∈ L v, c ∈ T := fun v c hc =>
    Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hc⟩
  let LT : V → Finset T := fun v => (L v).subtype (fun c => c ∈ T)
  have hLT : ∀ v, k ≤ (LT v).card := by
    intro v
    change k ≤ ((L v).subtype (fun c => c ∈ T)).card
    rw [Finset.card_subtype, Finset.filter_eq_self.mpr (hT v)]
    exact hL v
  obtain ⟨f, hfL⟩ := h.color_lists_finite LT hLT
  refine ⟨SimpleGraph.Coloring.mk (fun v => (f v).val) ?_, ?_⟩
  · intro u v huv hEq
    exact f.valid huv (Subtype.ext hEq)
  · intro v
    exact Finset.mem_subtype.mp (hfL v)

/-- The finite independent-set extraction lemma gives a bound on the actual
list chromatic number, not an auxiliary numerical invariant. -/
theorem choiceNumber_le_of_independent_subsets [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (m s k : ℕ) (hm : 0 < m) (hs : 0 < s)
    (hcard : Fintype.card V ≤ k * m)
    (hind : ∀ U : Finset V, s ≤ U.card →
      ∃ I : Finset V, I ⊆ U ∧ I.card = m ∧
        ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) :
    choiceNumber G ≤ k + s := by
  apply choiceNumber_le_of_kChoosable
  intro L hL
  obtain ⟨f, hfL, hfG⟩ := exists_list_coloring_of_independent_subsets
    G m s hm hs k univ L (by simpa using hcard)
    (fun U _ hU => hind U hU) (fun v _ => hL v)
  refine ⟨SimpleGraph.Coloring.mk f ?_, fun v => hfL v (Finset.mem_univ _)⟩
  intro u v huv
  exact hfG u (Finset.mem_univ _) v (Finset.mem_univ _) huv

#print axioms choiceNumber_le_card
#print axioms KChoosable.color_lists
#print axioms choiceNumber_le_of_independent_subsets

end JSP656
