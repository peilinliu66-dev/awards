import Erdos776.Combinatorics.Antichain
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Sum
import Lean.Elab.Tactic.Omega

/-!
# Two-point padding and persistent free sets

This is the symbolic construction used in both `TECHNICAL_NOTE.md` and
`SMALL_R_NOTE.md`.  It is stated over an arbitrary ground-set type.  Two new
points are represented by the right summand `Fin 2`; old points use the left
summand.
-/

namespace Erdos776.Antichain

open Finset

variable {α : Type*} [DecidableEq α]

/-- The left injection as a bundled embedding. -/
def oldEmbedding : α ↪ α ⊕ Fin 2 :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- The right injection of the two new points as a bundled embedding. -/
def newPointEmbedding : Fin 2 ↪ α ⊕ Fin 2 :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- Embed an old set into the enlarged ground set. -/
def oldSet (s : Finset α) : Finset (α ⊕ Fin 2) :=
  s.map oldEmbedding

/-- The pair of newly added points. -/
def addedPoints : Finset (α ⊕ Fin 2) :=
  (Finset.univ : Finset (Fin 2)).map newPointEmbedding

/-- The new member born from a free set `d`. -/
def paddedSet (d : Finset α) : Finset (α ⊕ Fin 2) :=
  oldSet d ∪ addedPoints

/-- The free set retained for the next padding stage; it uses only new point `0`. -/
def persistentSet (d : Finset α) : Finset (α ⊕ Fin 2) :=
  insert (Sum.inr (0 : Fin 2)) (oldSet d)

omit [DecidableEq α] in
@[simp] theorem mem_oldSet_inl {s : Finset α} {x : α} :
    Sum.inl x ∈ oldSet s ↔ x ∈ s := by
  simp [oldSet, oldEmbedding]

omit [DecidableEq α] in
@[simp] theorem not_mem_oldSet_inr {s : Finset α} {j : Fin 2} :
    Sum.inr j ∉ oldSet s := by
  simp [oldSet, oldEmbedding]

omit [DecidableEq α] in
@[simp] theorem mem_addedPoints_inr (j : Fin 2) :
    Sum.inr j ∈ (addedPoints : Finset (α ⊕ Fin 2)) := by
  simp [addedPoints, newPointEmbedding]

omit [DecidableEq α] in
@[simp] theorem not_mem_addedPoints_inl (x : α) :
    Sum.inl x ∉ (addedPoints : Finset (α ⊕ Fin 2)) := by
  simp [addedPoints, newPointEmbedding]

@[simp] theorem mem_paddedSet_inl {d : Finset α} {x : α} :
    Sum.inl x ∈ paddedSet d ↔ x ∈ d := by
  simp [paddedSet]

@[simp] theorem mem_paddedSet_inr {d : Finset α} (j : Fin 2) :
    Sum.inr j ∈ paddedSet d := by
  simp [paddedSet]

@[simp] theorem mem_persistentSet_inl {d : Finset α} {x : α} :
    Sum.inl x ∈ persistentSet d ↔ x ∈ d := by
  simp [persistentSet]

@[simp] theorem mem_persistentSet_zero {d : Finset α} :
    Sum.inr (0 : Fin 2) ∈ persistentSet d := by
  simp [persistentSet]

@[simp] theorem not_mem_persistentSet_one {d : Finset α} :
    Sum.inr (1 : Fin 2) ∉ persistentSet d := by
  simp [persistentSet]

theorem paddedSet_injective : Function.Injective (paddedSet (α := α)) := by
  intro d e hde
  ext x
  have h := congrArg (fun s => Sum.inl x ∈ s) hde
  simpa using h

theorem persistentSet_injective : Function.Injective (persistentSet (α := α)) := by
  intro d e hde
  ext x
  have h := congrArg (fun s => Sum.inl x ∈ s) hde
  simpa using h

/-- `paddedSet` as an embedding, used to map whole families. -/
def paddedSetEmbedding : Finset α ↪ Finset (α ⊕ Fin 2) :=
  ⟨paddedSet, paddedSet_injective⟩

/-- `persistentSet` as an embedding. -/
def persistentSetEmbedding : Finset α ↪ Finset (α ⊕ Fin 2) :=
  ⟨persistentSet, persistentSet_injective⟩

/-- The old members inside the enlarged ground set. -/
def oldFamily (C : Family α) : Family (α ⊕ Fin 2) :=
  mapFamily oldEmbedding C

/-- The family of members born in one padding step. -/
def bornFamily (D : Family α) : Family (α ⊕ Fin 2) :=
  D.map paddedSetEmbedding

/-- The complete result of one two-point padding step. -/
def twoPointPadding (C D : Family α) : Family (α ⊕ Fin 2) :=
  oldFamily C ∪ bornFamily D

/-- The family of free sets retained after the padding step. -/
def persistentFreeFamily (D : Family α) : Family (α ⊕ Fin 2) :=
  D.map persistentSetEmbedding

@[simp] theorem mem_bornFamily {D : Family α} {u : Finset (α ⊕ Fin 2)} :
    u ∈ bornFamily D ↔ ∃ d ∈ D, paddedSet d = u := by
  simp [bornFamily, paddedSetEmbedding]

@[simp] theorem mem_persistentFreeFamily
    {D : Family α} {u : Finset (α ⊕ Fin 2)} :
    u ∈ persistentFreeFamily D ↔ ∃ d ∈ D, persistentSet d = u := by
  simp [persistentFreeFamily, persistentSetEmbedding]

@[simp] theorem card_bornFamily (D : Family α) :
    (bornFamily D).card = D.card := by
  simp [bornFamily]

@[simp] theorem card_persistentFreeFamily (D : Family α) :
    (persistentFreeFamily D).card = D.card := by
  simp [persistentFreeFamily]

omit [DecidableEq α] in
theorem oldSet_disjoint_addedPoints (s : Finset α) :
    Disjoint (oldSet s) (addedPoints : Finset (α ⊕ Fin 2)) := by
  rw [Finset.disjoint_left]
  intro x hxs hxa
  obtain x | x := x
  · exact not_mem_addedPoints_inl x hxa
  · exact not_mem_oldSet_inr hxs

@[simp] theorem card_paddedSet (d : Finset α) :
    (paddedSet d).card = d.card + 2 := by
  rw [paddedSet, card_union_of_disjoint (oldSet_disjoint_addedPoints d)]
  simp [oldSet, addedPoints]

@[simp] theorem card_persistentSet (d : Finset α) :
    (persistentSet d).card = d.card + 1 := by
  rw [persistentSet, card_insert_of_notMem]
  · simp [oldSet]
  · exact not_mem_oldSet_inr

theorem bornFamily_sized {D : Family α} {s : ℕ} (hs : 1 ≤ s)
    (hD : (D : Set (Finset α)).Sized (s - 1)) :
    (bornFamily D : Set (Finset (α ⊕ Fin 2))).Sized (s + 1) := by
  intro u hu
  obtain ⟨d, hd, rfl⟩ := mem_bornFamily.mp hu
  rw [card_paddedSet, hD hd]
  omega

theorem persistentFreeFamily_sized {D : Family α} {s : ℕ} (hs : 1 ≤ s)
    (hD : (D : Set (Finset α)).Sized (s - 1)) :
    (persistentFreeFamily D : Set (Finset (α ⊕ Fin 2))).Sized s := by
  intro u hu
  obtain ⟨d, hd, rfl⟩ := mem_persistentFreeFamily.mp hu
  rw [card_persistentSet, hD hd]
  omega

theorem oldSet_not_subset_paddedSet
    {C D : Family α} (hfree : IsFreeFamily C D)
    {c d : Finset α} (hc : c ∈ C) (hd : d ∈ D) :
    ¬ oldSet c ⊆ paddedSet d := by
  intro hsub
  apply hfree d hd c hc
  intro x hx
  exact mem_paddedSet_inl.mp (hsub (mem_oldSet_inl.mpr hx))

theorem paddedSet_not_subset_oldSet (c d : Finset α) :
    ¬ paddedSet d ⊆ oldSet c := by
  intro hsub
  exact not_mem_oldSet_inr (hsub (mem_paddedSet_inr (d := d) 0))

/-- The set-theoretic heart of the two-point padding lemma. -/
theorem isSperner_twoPointPadding
    {C D : Family α} {s : ℕ} (hs : 1 ≤ s)
    (hC : IsSperner C)
    (hD : (D : Set (Finset α)).Sized (s - 1))
    (hfree : IsFreeFamily C D) :
    IsSperner (twoPointPadding C D) := by
  have hold : IsSperner (oldFamily C) := isSperner_mapFamily hC
  have hborn : IsSperner (bornFamily D) :=
    (bornFamily_sized hs hD).isAntichain
  unfold IsSperner twoPointPadding
  rw [Finset.coe_union]
  apply isAntichain_union.mpr
  refine ⟨hold, hborn, ?_⟩
  intro a ha b hb hab
  obtain ⟨c, hc, rfl⟩ := mem_mapFamily.mp ha
  obtain ⟨d, hd, rfl⟩ := mem_bornFamily.mp hb
  exact ⟨oldSet_not_subset_paddedSet hfree hc hd,
    paddedSet_not_subset_oldSet c d⟩

/-- Every old level survives a padding step with at least its old cardinality. -/
theorem card_level_le_twoPointPadding
    (C D : Family α) (i : ℕ) :
    (level C i).card ≤ (level (twoPointPadding C D) i).card := by
  have hsubset : oldFamily C ⊆ twoPointPadding C D := subset_union_left
  have hlevel := card_le_card (level_mono hsubset i)
  simpa [oldFamily] using hlevel

theorem level_bornFamily_eq {D : Family α} {s : ℕ} (hs : 1 ≤ s)
    (hD : (D : Set (Finset α)).Sized (s - 1)) :
    level (bornFamily D) (s + 1) = bornFamily D := by
  ext u
  constructor
  · exact fun hu => (mem_level.mp hu).1
  · intro hu
    exact mem_level.mpr ⟨hu, bornFamily_sized hs hD hu⟩

/-- The born family supplies the next level. -/
theorem card_freeFamily_le_new_level
    {C D : Family α} {s : ℕ} (hs : 1 ≤ s)
    (hD : (D : Set (Finset α)).Sized (s - 1)) :
    D.card ≤ (level (twoPointPadding C D) (s + 1)).card := by
  have hsubset : bornFamily D ⊆ twoPointPadding C D := subset_union_right
  have hlevel := card_le_card (level_mono hsubset (s + 1))
  rw [level_bornFamily_eq hs hD, card_bornFamily] at hlevel
  exact hlevel

/-- One padding step extends multiplicity support from `2..s` to `2..s+1`. -/
theorem hasMultiplicities_twoPointPadding
    {C D : Family α} {r s : ℕ} (hs : 1 ≤ s)
    (hlevels : HasMultiplicities C r 2 s)
    (hDsize : (D : Set (Finset α)).Sized (s - 1))
    (hDcard : r ≤ D.card) :
    HasMultiplicities (twoPointPadding C D) r 2 (s + 1) := by
  intro i hi his
  unfold HasMultiplicityAt
  by_cases htop : i = s + 1
  · subst i
    exact hDcard.trans (card_freeFamily_le_new_level hs hDsize)
  · have his' : i ≤ s := by omega
    exact (hlevels i hi his').trans (card_level_le_twoPointPadding C D i)

theorem oldSet_not_subset_persistentSet
    {C D : Family α} (hfree : IsFreeFamily C D)
    {c d : Finset α} (hc : c ∈ C) (hd : d ∈ D) :
    ¬ oldSet c ⊆ persistentSet d := by
  intro hsub
  apply hfree d hd c hc
  intro x hx
  exact mem_persistentSet_inl.mp (hsub (mem_oldSet_inl.mpr hx))

theorem paddedSet_not_subset_persistentSet (d e : Finset α) :
    ¬ paddedSet e ⊆ persistentSet d := by
  intro hsub
  exact not_mem_persistentSet_one
    (hsub (mem_paddedSet_inr (d := e) (1 : Fin 2)))

/-- The chosen free sets remain free after the padding step. -/
theorem isFreeFamily_persistent
    {C D : Family α} (hfree : IsFreeFamily C D) :
    IsFreeFamily (twoPointPadding C D) (persistentFreeFamily D) := by
  intro u hu
  obtain ⟨d, hd, rfl⟩ := mem_persistentFreeFamily.mp hu
  intro a ha
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨c, hc, rfl⟩ := mem_mapFamily.mp ha
    exact oldSet_not_subset_persistentSet hfree hc hd
  · obtain ⟨e, he, rfl⟩ := mem_bornFamily.mp ha
    exact paddedSet_not_subset_persistentSet d e

/--
The complete reusable padding package: antichain, one extra occupied level,
and a same-cardinality free family ready for the next iteration.
-/
theorem twoPointPadding_with_persistent_free
    {C D : Family α} {r s : ℕ} (hs : 1 ≤ s)
    (hC : IsSperner C)
    (hlevels : HasMultiplicities C r 2 s)
    (hDsize : (D : Set (Finset α)).Sized (s - 1))
    (hDcard : r ≤ D.card)
    (hfree : IsFreeFamily C D) :
    IsSperner (twoPointPadding C D) ∧
      HasMultiplicities (twoPointPadding C D) r 2 (s + 1) ∧
      (persistentFreeFamily D : Set (Finset (α ⊕ Fin 2))).Sized s ∧
      (persistentFreeFamily D).card = D.card ∧
      IsFreeFamily (twoPointPadding C D) (persistentFreeFamily D) := by
  exact ⟨isSperner_twoPointPadding hs hC hDsize hfree,
    hasMultiplicities_twoPointPadding hs hlevels hDsize hDcard,
    persistentFreeFamily_sized hs hDsize,
    card_persistentFreeFamily D,
    isFreeFamily_persistent hfree⟩

/-! ### Arbitrarily many padding stages -/

universe u

/-- The ground type after adjoining `t` successive pairs of points. -/
def IteratedGround (α : Type u) : ℕ → Type u
  | 0 => α
  | t + 1 => IteratedGround α t ⊕ Fin 2

instance iteratedGroundDecidableEq [DecidableEq α] (t : ℕ) :
    DecidableEq (IteratedGround α t) := by
  induction t with
  | zero => simpa [IteratedGround] using (inferInstance : DecidableEq α)
  | succ t ih =>
      letI := ih
      change DecidableEq (IteratedGround α t ⊕ Fin 2)
      exact inferInstance

instance iteratedGroundFintype [Fintype α] (t : ℕ) :
    Fintype (IteratedGround α t) := by
  induction t with
  | zero => simpa [IteratedGround] using (inferInstance : Fintype α)
  | succ t ih =>
      letI : Fintype (IteratedGround α t) := ih
      change Fintype (IteratedGround α t ⊕ Fin 2)
      exact inferInstance

omit [DecidableEq α] in
@[simp] theorem card_iteratedGround [Fintype α] (t : ℕ) :
    Fintype.card (IteratedGround α t) = Fintype.card α + 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change Fintype.card (IteratedGround α t ⊕ Fin 2) =
        Fintype.card α + 2 * (t + 1)
      rw [Fintype.card_sum, ih]
      simp
      omega

/-- A family together with the free family reserved for the next stage. -/
structure PaddingState (α : Type u) where
  family : Family α
  free : Family α

/-- Iterate the explicit padding construction `t` times. -/
def iteratedPaddingState
    (C D : Family α) : (t : ℕ) → PaddingState (IteratedGround α t)
  | 0 => ⟨C, D⟩
  | t + 1 =>
      let previous := iteratedPaddingState C D t
      ⟨twoPointPadding previous.family previous.free,
        persistentFreeFamily previous.free⟩

/--
Persistent freeness really supports any finite number of padding stages, not
merely the first checked stage.
-/
theorem iteratedPaddingState_spec
    {C D : Family α} {r s : ℕ} (hs : 1 ≤ s)
    (hC : IsSperner C)
    (hlevels : HasMultiplicities C r 2 s)
    (hDsize : (D : Set (Finset α)).Sized (s - 1))
    (hDcard : r ≤ D.card)
    (hfree : IsFreeFamily C D) :
    ∀ t,
      let state := iteratedPaddingState C D t
      IsSperner state.family ∧
        HasMultiplicities state.family r 2 (s + t) ∧
        (state.free : Set (Finset (IteratedGround α t))).Sized (s + t - 1) ∧
        state.free.card = D.card ∧
        IsFreeFamily state.family state.free := by
  intro t
  induction t with
  | zero =>
      refine ⟨hC, ?_, ?_, rfl, hfree⟩
      · convert! hlevels using 1
      · convert! hDsize using 1
  | succ t ih =>
      dsimp only [iteratedPaddingState]
      have hst : 1 ≤ s + t := by omega
      have hcard : r ≤ (iteratedPaddingState C D t).free.card := by
        rw [ih.2.2.2.1]
        exact hDcard
      have hstep := twoPointPadding_with_persistent_free
        hst ih.1 ih.2.1 ih.2.2.1 hcard ih.2.2.2.2
      refine ⟨hstep.1, ?_, ?_, ?_, hstep.2.2.2.2⟩
      · convert! hstep.2.1 using 1 <;> omega
      · convert! hstep.2.2.1 using 1 <;> omega
      · exact hstep.2.2.2.1.trans ih.2.2.2.1

end Erdos776.Antichain
