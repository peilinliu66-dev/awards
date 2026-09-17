import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Slice
import Mathlib.Order.Antichain

/-!
# Generic finite antichain infrastructure

The extremal problem uses finite families of finite sets on several different
ground-set types.  These definitions are intentionally independent of `Fin n`
so that constructions can add named points using sum types and transport the
result to a numerical ground set only at the end.
-/

namespace Erdos776.Antichain

open Finset

/-- A finite family of finite subsets of `α`. -/
abbrev Family (α : Type*) := Finset (Finset α)

/-- The Sperner/antichain property under set inclusion. -/
def IsSperner {α : Type*} (F : Family α) : Prop :=
  IsAntichain (· ⊆ ·) (F : Set (Finset α))

/-- The members of `F` on level `i`. -/
def level {α : Type*} [DecidableEq α] (F : Family α) (i : ℕ) : Family α :=
  F.filter fun s => s.card = i

@[simp] theorem mem_level {α : Type*} [DecidableEq α]
    {F : Family α} {i : ℕ} {s : Finset α} :
    s ∈ level F i ↔ s ∈ F ∧ s.card = i := by
  simp [level]

theorem level_mono {α : Type*} [DecidableEq α]
    {F G : Family α} (hFG : F ⊆ G) (i : ℕ) :
    level F i ⊆ level G i := by
  intro s hs
  exact mem_level.mpr ⟨hFG (mem_level.mp hs).1, (mem_level.mp hs).2⟩

/-- `F` contains at least `r` members on level `i`. -/
def HasMultiplicityAt {α : Type*} [DecidableEq α]
    (F : Family α) (r i : ℕ) : Prop :=
  r ≤ (level F i).card

/-- `F` contains at least `r` members on every level from `lo` through `hi`. -/
def HasMultiplicities {α : Type*} [DecidableEq α]
    (F : Family α) (r lo hi : ℕ) : Prop :=
  ∀ i, lo ≤ i → i ≤ hi → HasMultiplicityAt F r i

/-- A set which contains no member of `F`. -/
def FreeFor {α : Type*} (F : Family α) (d : Finset α) : Prop :=
  ∀ c ∈ F, ¬ c ⊆ d

/-- Every member of `D` is free for `F`. -/
def IsFreeFamily {α : Type*} (F D : Family α) : Prop :=
  ∀ d ∈ D, FreeFor F d

/-- Map every set in a family along an embedding of ground sets. -/
def mapFamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (F : Family α) : Family β :=
  F.map (Finset.mapEmbedding e).toEmbedding

@[simp] theorem mem_mapFamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    {e : α ↪ β} {F : Family α} {t : Finset β} :
    t ∈ mapFamily e F ↔ ∃ s ∈ F, s.map e = t := by
  simp only [mapFamily, mem_map]
  constructor
  · rintro ⟨s, hs, hst⟩
    exact ⟨s, hs, by exact hst⟩
  · rintro ⟨s, hs, hst⟩
    exact ⟨s, hs, by exact hst⟩

@[simp] theorem card_mapFamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (F : Family α) :
    (mapFamily e F).card = F.card := by
  simp [mapFamily]

theorem level_mapFamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (F : Family α) (i : ℕ) :
    level (mapFamily e F) i = mapFamily e (level F i) := by
  ext t
  constructor
  · intro ht
    obtain ⟨htF, htcard⟩ := mem_level.mp ht
    obtain ⟨s, hs, hst⟩ := mem_mapFamily.mp htF
    subst t
    apply mem_mapFamily.mpr
    exact ⟨s, mem_level.mpr ⟨hs, by simpa using htcard⟩, rfl⟩
  · intro ht
    obtain ⟨s, hs, hst⟩ := mem_mapFamily.mp ht
    subst t
    apply mem_level.mpr
    exact ⟨mem_mapFamily.mpr ⟨s, (mem_level.mp hs).1, rfl⟩,
      by simpa using (mem_level.mp hs).2⟩

@[simp] theorem card_level_mapFamily
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (F : Family α) (i : ℕ) :
    (level (mapFamily e F) i).card = (level F i).card := by
  rw [level_mapFamily, card_mapFamily]

theorem isSperner_mapFamily
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {e : α ↪ β} {F : Family α} (hF : IsSperner F) :
    IsSperner (mapFamily e F) := by
  intro s hs t ht hst hsub
  obtain ⟨u, hu, rfl⟩ := mem_mapFamily.mp hs
  obtain ⟨v, hv, rfl⟩ := mem_mapFamily.mp ht
  have huv : u ⊆ v := Finset.map_subset_map.mp hsub
  have huv_eq : u = v := hF.eq hu hv huv
  apply hst
  rw [huv_eq]

theorem freeFor_map
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {e : α ↪ β} {F : Family α} {d : Finset α}
    (hd : FreeFor F d) :
    FreeFor (mapFamily e F) (d.map e) := by
  intro t ht htd
  obtain ⟨s, hs, rfl⟩ := mem_mapFamily.mp ht
  exact hd s hs (Finset.map_subset_map.mp htd)

end Erdos776.Antichain
