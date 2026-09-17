import Erdos776.Combinatorics.CascadeFamily
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Finset.Preimage

/-!
# Transporting finitely supported colex families to `Fin n`

Mathlib's Kruskal--Katona theorem is stated for families of subsets of
`Fin n`.  Our recursive cascade family is more convenient over `ℕ`; this file
provides the lossless transport for families supported below `n`.
-/

namespace Erdos776.KruskalKatona

open Finset

/-- The subset of `Fin n` whose values belong to `s`. -/
noncomputable def finify (n : ℕ) (s : Finset ℕ) : Finset (Fin n) :=
  s.preimage Fin.val Fin.val_injective.injOn

@[simp] theorem mem_finify {n : ℕ} {s : Finset ℕ} {x : Fin n} :
    x ∈ finify n s ↔ x.val ∈ s := by
  simp [finify]

/-- Mapping a bounded `finify` back to naturals recovers the original set. -/
theorem map_valEmbedding_finify {n : ℕ} {s : Finset ℕ}
    (hs : ∀ x ∈ s, x < n) :
    (finify n s).map Fin.valEmbedding = s := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
    simpa [← hyx] using (mem_finify.mp hy)
  · intro hx
    exact mem_map.mpr ⟨⟨x, hs x hx⟩, mem_finify.mpr hx, rfl⟩

theorem card_finify {n : ℕ} {s : Finset ℕ}
    (hs : ∀ x ∈ s, x < n) : (finify n s).card = s.card := by
  have h := congrArg Finset.card (map_valEmbedding_finify hs)
  simpa using h

/-- A family is supported on the first `n` natural numbers. -/
def BoundedFamily (n : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  ∀ s ∈ F, ∀ x ∈ s, x < n

/-- Apply `finify` to every member of a family. -/
noncomputable def finifyFamily (n : ℕ) (F : Finset (Finset ℕ)) :
    Finset (Finset (Fin n)) :=
  F.image (finify n)

theorem finify_injOn {n : ℕ} {F : Finset (Finset ℕ)}
    (hF : BoundedFamily n F) : Set.InjOn (finify n) (F : Set (Finset ℕ)) := by
  intro s hs t ht hst
  have := congrArg (Finset.map Fin.valEmbedding) hst
  simpa [map_valEmbedding_finify (hF s hs), map_valEmbedding_finify (hF t ht)] using this

theorem card_finifyFamily {n : ℕ} {F : Finset (Finset ℕ)}
    (hF : BoundedFamily n F) : (finifyFamily n F).card = F.card := by
  exact card_image_of_injOn (finify_injOn hF)

theorem sized_finifyFamily {n k : ℕ} {F : Finset (Finset ℕ)}
    (hF : BoundedFamily n F)
    (hsize : (F : Set (Finset ℕ)).Sized k) :
    (finifyFamily n F : Set (Finset (Fin n))).Sized k := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
  rw [card_finify (hF t ht), hsize ht]

theorem bounded_cascadeFamily {n k : ℕ} {a : ℕ} {digits : List ℕ}
    (h : IsCanonical k (a :: digits)) (ha : a < n) :
    BoundedFamily n (cascadeFamily k (a :: digits)) := by
  intro s hs
  exact mem_cascadeFamily_lt_of_digits_lt (h.all_lt_of_head ha) hs

/-- Colex comparison is preserved by lossless transport to `Fin n`. -/
theorem colex_finify_lt_iff {n : ℕ} {s t : Finset ℕ}
    (hs : ∀ x ∈ s, x < n) (ht : ∀ x ∈ t, x < n) :
    toColex (finify n s) < toColex (finify n t) ↔
      toColex s < toColex t := by
  have hs' : image Fin.val (finify n s) = s := by
    simpa [map_eq_image] using map_valEmbedding_finify hs
  have ht' : image Fin.val (finify n t) = t := by
    simpa [map_eq_image] using map_valEmbedding_finify ht
  constructor
  · intro hst
    have himage :=
      (Finset.Colex.toColex_image_lt_toColex_image Fin.val_strictMono).mpr hst
    rwa [hs', ht'] at himage
  · intro hst
    rw [← hs', ← ht'] at hst
    exact (Finset.Colex.toColex_image_lt_toColex_image Fin.val_strictMono).mp hst

/-- A bounded colex initial segment transports to an initial segment on `Fin n`. -/
theorem isInitSeg_finifyFamily {n k : ℕ} {F : Finset (Finset ℕ)}
    (hF : BoundedFamily n F)
    (hinit : Finset.Colex.IsInitSeg F k) :
    Finset.Colex.IsInitSeg (finifyFamily n F) k := by
  constructor
  · exact sized_finifyFamily hF hinit.1
  · intro s t hs ht
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hs
    let v : Finset ℕ := t.map Fin.valEmbedding
    have hvcard : v.card = k := by
      simp [v, ht.2]
    have hvbound : ∀ x ∈ v, x < n := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      exact y.isLt
    have hvcolex : toColex v < toColex u := by
      have himage :=
        (Finset.Colex.toColex_image_lt_toColex_image Fin.val_strictMono).mpr ht.1
      have hu' : image Fin.val (finify n u) = u := by
        simpa [map_eq_image] using map_valEmbedding_finify (hF u hu)
      simpa [v, map_eq_image, hu'] using himage
    have hvF : v ∈ F := hinit.2 hu ⟨hvcolex, hvcard⟩
    apply mem_image.mpr
    refine ⟨v, hvF, ?_⟩
    ext x
    simp only [v, finify, mem_preimage, mem_map]
    constructor
    · rintro ⟨y, hy, hval⟩
      exact Fin.val_injective hval ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩

theorem finify_erase {n : ℕ} {s : Finset ℕ} {x : ℕ}
    (hx : x < n) :
    finify n (s.erase x) = (finify n s).erase ⟨x, hx⟩ := by
  ext y
  rw [mem_finify, mem_erase, mem_erase, mem_finify]
  constructor
  · rintro ⟨hne, hmem⟩
    exact ⟨fun h => hne (congrArg Fin.val h), hmem⟩
  · rintro ⟨hne, hmem⟩
    exact ⟨fun h => hne (Fin.ext h), hmem⟩

theorem BoundedFamily.shadow {n : ℕ} {F : Finset (Finset ℕ)}
    (hF : BoundedFamily n F) : BoundedFamily n (Finset.shadow F) := by
  intro t ht x hx
  obtain ⟨s, hs, y, hy, rfl⟩ := mem_shadow_iff.mp ht
  exact hF s hs x (mem_of_mem_erase hx)

/-- `finifyFamily` commutes with taking a lower shadow. -/
theorem shadow_finifyFamily {n : ℕ} {F : Finset (Finset ℕ)}
    (hF : BoundedFamily n F) :
    Finset.shadow (finifyFamily n F) =
      finifyFamily n (Finset.shadow F) := by
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs, x, hx, hxt⟩ := mem_shadow_iff.mp ht
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hs
    have hxu : x.val ∈ u := mem_finify.mp hx
    apply mem_image.mpr
    refine ⟨u.erase x.val, erase_mem_shadow hu hxu, ?_⟩
    rw [finify_erase x.isLt]
    exact hxt
  · intro ht
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ht
    obtain ⟨u, hu, x, hxu, hxv⟩ := mem_shadow_iff.mp hv
    have hxn : x < n := hF u hu x hxu
    apply mem_shadow_iff.mpr
    refine ⟨finify n u, mem_image.mpr ⟨u, hu, rfl⟩,
      ⟨x, hxn⟩, mem_finify.mpr hxu, ?_⟩
    rw [← finify_erase hxn, hxv]

theorem card_shadow_finifyFamily {n : ℕ} {F : Finset (Finset ℕ)}
    (hF : BoundedFamily n F) :
    (Finset.shadow (finifyFamily n F)).card = (Finset.shadow F).card := by
  rw [shadow_finifyFamily hF, card_finifyFamily hF.shadow]

end Erdos776.KruskalKatona
