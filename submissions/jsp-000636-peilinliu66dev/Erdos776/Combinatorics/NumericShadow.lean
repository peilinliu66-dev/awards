import Erdos776.Combinatorics.FiniteColex

/-!
# The numerical Kruskal--Katona shadow

`kkShadow n k m` is the least lower-shadow size among `m` distinct `k`-sets
on `Fin n`.  A maximal sentinel is included for impossible cardinalities; this
makes the function globally monotone without changing any feasible value.
-/

namespace Erdos776.KruskalKatona

open Finset

def uniformFamilies (n k m : ℕ) : Finset (Finset (Finset (Fin n))) :=
  Finset.univ.filter fun A =>
    (∀ s ∈ A, s.card = k) ∧ A.card = m

def shadowCandidates (n k m : ℕ) : Finset ℕ :=
  insert (n.choose (k - 1)) <|
    (uniformFamilies n k m).image fun A => (Finset.shadow A).card

/-- The minimum numerical lower-shadow size, extended monotonically off range. -/
noncomputable def kkShadow (n k m : ℕ) : ℕ :=
  (shadowCandidates n k m).min' <| by
    exact ⟨n.choose (k - 1), mem_insert_self _ _⟩

theorem sentinel_mem_shadowCandidates (n k m : ℕ) :
    n.choose (k - 1) ∈ shadowCandidates n k m := by
  exact mem_insert_self _ _

theorem shadowCandidates_nonempty (n k m : ℕ) :
    (shadowCandidates n k m).Nonempty :=
  ⟨n.choose (k - 1), sentinel_mem_shadowCandidates n k m⟩

theorem mem_shadowCandidates_iff {n k m q : ℕ} :
    q ∈ shadowCandidates n k m ↔
      q = n.choose (k - 1) ∨
      ∃ A : Finset (Finset (Fin n)),
        (A : Set (Finset (Fin n))).Sized k ∧
        A.card = m ∧ (Finset.shadow A).card = q := by
  simp only [shadowCandidates, mem_insert, mem_image, uniformFamilies,
    mem_filter, mem_univ, true_and, Set.Sized]
  constructor
  · rintro (h | ⟨A, ⟨hsize, hcard⟩, hshadow⟩)
    · exact Or.inl h
    · exact Or.inr ⟨A, hsize, hcard, hshadow⟩
  · rintro (h | ⟨A, hsize, hcard, hshadow⟩)
    · exact Or.inl h
    · exact Or.inr ⟨A, ⟨hsize, hcard⟩, hshadow⟩

theorem kkShadow_le_sentinel (n k m : ℕ) :
    kkShadow n k m ≤ n.choose (k - 1) := by
  exact min'_le _ _ (sentinel_mem_shadowCandidates n k m)

/-- Global monotonicity in the number of sets. -/
theorem kkShadow_mono (n k : ℕ) : Monotone (kkShadow n k) := by
  intro x y hxy
  apply le_min' (shadowCandidates n k y) (shadowCandidates_nonempty n k y)
  intro q hq
  rcases mem_shadowCandidates_iff.mp hq with hq | hq
  · rw [hq]
    exact kkShadow_le_sentinel n k x
  · obtain ⟨A, hAsize, hAcard, rfl⟩ := hq
    obtain ⟨B, hBA, hBcard⟩ := exists_subset_card_eq (hAcard ▸ hxy)
    have hBsize : (B : Set (Finset (Fin n))).Sized k := hAsize.mono hBA
    have hBcandidate : (Finset.shadow B).card ∈ shadowCandidates n k x := by
      exact mem_shadowCandidates_iff.mpr (Or.inr ⟨B, hBsize, hBcard, rfl⟩)
    exact (min'_le _ _ hBcandidate).trans
      (card_le_card (shadow_mono hBA))

/-- Every uniform family has shadow at least the numerical minimum. -/
theorem kkShadow_le_card_shadow
    {n k : ℕ} {A : Finset (Finset (Fin n))}
    (hsize : (A : Set (Finset (Fin n))).Sized k) :
    kkShadow n k A.card ≤ (Finset.shadow A).card := by
  apply min'_le
  exact mem_shadowCandidates_iff.mpr
    (Or.inr ⟨A, hsize, rfl, rfl⟩)

/--
The concrete family represented by a bounded canonical cascade realizes the
numerical minimum.  The lower bound is exactly mathlib's Kruskal--Katona
theorem applied to the transported colex initial segment.
-/
theorem kkShadow_eq_cascadeShadowValue
    {n k : ℕ} {digits : List ℕ}
    (hcanon : IsCanonical k digits)
    (hbound : BoundedFamily n (cascadeFamily k digits)) :
    kkShadow n k (cascadeValue k digits) =
      cascadeShadowValue k digits := by
  let C : Finset (Finset (Fin n)) :=
    finifyFamily n (cascadeFamily k digits)
  have hCsize : (C : Set (Finset (Fin n))).Sized k :=
    sized_finifyFamily hbound (sized_cascadeFamily hcanon)
  have hCcard : C.card = cascadeValue k digits := by
    rw [show C = finifyFamily n (cascadeFamily k digits) by rfl,
      card_finifyFamily hbound, card_cascadeFamily hcanon]
  have hCshadow : (Finset.shadow C).card = cascadeShadowValue k digits := by
    rw [show C = finifyFamily n (cascadeFamily k digits) by rfl,
      card_shadow_finifyFamily hbound, card_shadow_cascadeFamily hcanon]
  have hCinit : Finset.Colex.IsInitSeg C k :=
    isInitSeg_finifyFamily hbound (isInitSeg_cascadeFamily hcanon)
  apply le_antisymm
  · apply min'_le
    exact mem_shadowCandidates_iff.mpr (Or.inr ⟨C, hCsize, hCcard, hCshadow⟩)
  · apply le_min' (shadowCandidates n k (cascadeValue k digits))
      (shadowCandidates_nonempty n k (cascadeValue k digits))
    intro q hq
    rcases mem_shadowCandidates_iff.mp hq with hq | hq
    · rw [hq, ← hCshadow]
      exact (by
        simpa using card_le_card (subset_powersetCard_univ_iff.mpr hCsize.shadow))
    · obtain ⟨A, hAsize, hAcard, rfl⟩ := hq
      rw [← hCshadow]
      apply Finset.kruskal_katona hAsize
      · rw [hCcard, hAcard]
      · exact hCinit

/-- Convenient head-bound form of the cascade evaluation theorem. -/
theorem kkShadow_eq_cascadeShadowValue_of_head
    {n k a : ℕ} {digits : List ℕ}
    (hcanon : IsCanonical k (a :: digits)) (ha : a < n) :
    kkShadow n k (cascadeValue k (a :: digits)) =
      cascadeShadowValue k (a :: digits) :=
  kkShadow_eq_cascadeShadowValue hcanon (bounded_cascadeFamily hcanon ha)

end Erdos776.KruskalKatona
