import Erdos776.Combinatorics.NumericShadow
import Mathlib.Order.Antichain

/-!
# The necessary half of the antichain profile criterion

For a finite antichain, `cumulativeLevel F i` consists of the `i`-sets lying
below at least one member of `F`.  The shadow of level `i+1` is contained in
level `i`; moreover it is disjoint from the actual level-`i` slice of `F`.
Kruskal--Katona therefore gives the top-down profile recurrence as a lower
bound.  This is the Clements--Daykin--Godfrey--Hilton necessity argument used
by L4.
-/

namespace Erdos776.KruskalKatona

open Finset

/-- The members of a family lying on one level. -/
def levelFamily {n : ℕ} (F : Finset (Finset (Fin n))) (i : ℕ) :
    Finset (Finset (Fin n)) :=
  F.filter fun s => s.card = i

@[simp] theorem mem_levelFamily {n i : ℕ}
    {F : Finset (Finset (Fin n))} {s : Finset (Fin n)} :
    s ∈ levelFamily F i ↔ s ∈ F ∧ s.card = i := by
  simp [levelFamily]

/-- The level-`i` part of the down-closure of a family. -/
def cumulativeLevel {n : ℕ} (F : Finset (Finset (Fin n))) (i : ℕ) :
    Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard i).filter fun s => ∃ t ∈ F, s ⊆ t

@[simp] theorem mem_cumulativeLevel {n i : ℕ}
    {F : Finset (Finset (Fin n))} {s : Finset (Fin n)} :
    s ∈ cumulativeLevel F i ↔ s.card = i ∧ ∃ t ∈ F, s ⊆ t := by
  simp [cumulativeLevel, and_comm]

theorem levelFamily_subset_cumulativeLevel {n i : ℕ}
    {F : Finset (Finset (Fin n))} :
    levelFamily F i ⊆ cumulativeLevel F i := by
  intro s hs
  exact mem_cumulativeLevel.mpr
    ⟨(mem_levelFamily.mp hs).2, s, (mem_levelFamily.mp hs).1, Subset.rfl⟩

theorem cumulativeLevel_sized {n i : ℕ}
    {F : Finset (Finset (Fin n))} :
    (cumulativeLevel F i : Set (Finset (Fin n))).Sized i := by
  intro s hs
  exact (mem_cumulativeLevel.mp hs).1

theorem card_cumulativeLevel_le_choose {n i : ℕ}
    {F : Finset (Finset (Fin n))} :
    (cumulativeLevel F i).card ≤ n.choose i := by
  calc
    (cumulativeLevel F i).card ≤ (Finset.univ.powersetCard i).card :=
      card_le_card (filter_subset _ _)
    _ = n.choose i := by simp

/-- Taking one shadow step stays in the down-closure of the original family. -/
theorem shadow_cumulativeLevel_subset {n i : ℕ}
    {F : Finset (Finset (Fin n))} :
    Finset.shadow (cumulativeLevel F (i + 1)) ⊆ cumulativeLevel F i := by
  intro s hs
  obtain ⟨u, hu, x, hx, rfl⟩ := mem_shadow_iff.mp hs
  obtain ⟨hu_card, t, htF, hut⟩ := mem_cumulativeLevel.mp hu
  apply mem_cumulativeLevel.mpr
  constructor
  · rw [card_erase_of_mem hx, hu_card]
    omega
  · exact ⟨t, htF, (Finset.erase_subset x u).trans hut⟩

/-- Antichain members on level `i` avoid the down-closure shadow from above. -/
theorem disjoint_levelFamily_shadow_cumulativeLevel
    {n i : ℕ} {F : Finset (Finset (Fin n))}
    (hanti : IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n)))) :
    Disjoint (levelFamily F i)
      (Finset.shadow (cumulativeLevel F (i + 1))) := by
  rw [Finset.disjoint_left]
  intro s hsF hsShadow
  obtain ⟨u, hu, x, hx, hsu⟩ := mem_shadow_iff.mp hsShadow
  obtain ⟨hu_card, t, htF, hut⟩ := mem_cumulativeLevel.mp hu
  have hs_member : s ∈ F := (mem_levelFamily.mp hsF).1
  have hst : s ⊆ t := by
    rw [← hsu]
    exact (Finset.erase_subset x u).trans hut
  have heq : s = t := hanti.eq hs_member htF hst
  have hs_card : s.card = i := (mem_levelFamily.mp hsF).2
  have ht_card_ge : i + 1 ≤ t.card := by
    rw [← hu_card]
    exact card_le_card hut
  rw [heq] at hs_card
  omega

/--
One necessary profile step: a level with at least `q` antichain members,
together with the shadow forced from above, consumes at least
`q + kkShadow` sets in the current cumulative level.
-/
theorem profile_step_le_cumulativeLevel
    {n i q : ℕ} {F : Finset (Finset (Fin n))}
    (hanti : IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n))))
    (hlevel : q ≤ (levelFamily F i).card) :
    q + kkShadow n (i + 1) (cumulativeLevel F (i + 1)).card ≤
      (cumulativeLevel F i).card := by
  have hshadow :
      kkShadow n (i + 1) (cumulativeLevel F (i + 1)).card ≤
        (Finset.shadow (cumulativeLevel F (i + 1))).card :=
    kkShadow_le_card_shadow cumulativeLevel_sized
  have hunion_subset :
      levelFamily F i ∪ Finset.shadow (cumulativeLevel F (i + 1)) ⊆
        cumulativeLevel F i :=
    union_subset levelFamily_subset_cumulativeLevel shadow_cumulativeLevel_subset
  have hunion_card := card_le_card hunion_subset
  rw [card_union_of_disjoint
    (disjoint_levelFamily_shadow_cumulativeLevel hanti)] at hunion_card
  omega

end Erdos776.KruskalKatona
