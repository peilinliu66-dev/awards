import Erdos776.Uniform.CoreCarry

/-!
# Occupied levels and the global threshold formulation

This file formalizes the elementary reduction in Section 17: for `r ≥ 4`, an
`r`-multiplicity antichain with `n-3` occupied levels must occupy exactly the
middle levels `2,...,n-2`.
-/

namespace Erdos776.Uniform

open Finset
open Erdos776.Antichain

/-- The set sizes represented by a family on `Fin n`. -/
def occupiedLevels {n : ℕ} (F : Family (Fin n)) : Finset ℕ :=
  (range (n + 1)).filter fun i => (level F i).Nonempty

@[simp] theorem mem_occupiedLevels {n : ℕ} {F : Family (Fin n)} {i : ℕ} :
    i ∈ occupiedLevels F ↔ i ≤ n ∧ (level F i).Nonempty := by
  simp [occupiedLevels]

/-- An antichain with at least `r` members on each level that it occupies. -/
def IsMultiplicityAntichain {n : ℕ} (F : Family (Fin n)) (r : ℕ) : Prop :=
  IsSperner F ∧
    ∀ i ∈ occupiedLevels F, r ≤ (level F i).card

theorem card_level_le_choose {n i : ℕ} (F : Family (Fin n)) :
    (level F i).card ≤ n.choose i := by
  have hsub : level F i ⊆ (Finset.univ : Finset (Fin n)).powersetCard i := by
    intro s hs
    exact mem_powersetCard.mpr
      ⟨subset_univ s, (mem_level.mp hs).2⟩
  simpa using card_le_card hsub

theorem zero_not_mem_occupiedLevels
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hF : IsMultiplicityAntichain F r) :
    0 ∉ occupiedLevels F := by
  intro hzero
  have hmult := hF.2 0 hzero
  have hcap := card_level_le_choose (i := 0) F
  simp at hcap
  omega

theorem top_not_mem_occupiedLevels
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hF : IsMultiplicityAntichain F r) :
    n ∉ occupiedLevels F := by
  intro htop
  have hmult := hF.2 n htop
  have hcap := card_level_le_choose (i := n) F
  rw [Nat.choose_self] at hcap
  omega

/-- Points whose singleton belongs to the family. -/
def singletonPoints {n : ℕ} (F : Family (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun x => ({x} : Finset (Fin n)) ∈ F

def singletonSetEmbedding (n : ℕ) : Fin n ↪ Finset (Fin n) where
  toFun x := {x}
  inj' := by
    intro x y h
    simpa using h

theorem level_one_eq_singletonPoints_map {n : ℕ} (F : Family (Fin n)) :
    level F 1 = (singletonPoints F).map (singletonSetEmbedding n) := by
  ext s
  constructor
  · intro hs
    have hcard := (mem_level.mp hs).2
    rw [card_eq_one] at hcard
    obtain ⟨x, rfl⟩ := hcard
    apply mem_map.mpr
    exact ⟨x, by simpa [singletonPoints] using (mem_level.mp hs).1, rfl⟩
  · intro hs
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hs
    have hxF : ({x} : Finset (Fin n)) ∈ F := (mem_filter.mp hx).2
    exact mem_level.mpr ⟨hxF, card_singleton x⟩

@[simp] theorem card_singletonPoints {n : ℕ} (F : Family (Fin n)) :
    (singletonPoints F).card = (level F 1).card := by
  rw [level_one_eq_singletonPoints_map, card_map]

theorem disjoint_singletonPoints_of_card_ne_one
    {n : ℕ} {F : Family (Fin n)} (hanti : IsSperner F)
    {s : Finset (Fin n)} (hs : s ∈ F) (hcard : s.card ≠ 1) :
    Disjoint s (singletonPoints F) := by
  rw [disjoint_left]
  intro x hxs hxsingle
  have hxF : ({x} : Finset (Fin n)) ∈ F := by
    simpa [singletonPoints] using hxsingle
  have heq : ({x} : Finset (Fin n)) = s :=
    hanti.eq hxF hs (singleton_subset_iff.mpr hxs)
  apply hcard
  rw [← heq]
  simp

theorem card_le_ground_sub_singletons
    {n r : ℕ} {F : Family (Fin n)}
    (hanti : IsSperner F) (hsingle : r ≤ (singletonPoints F).card)
    {s : Finset (Fin n)} (hs : s ∈ F) (hcard : s.card ≠ 1) :
    s.card ≤ n - r := by
  have hdisj := disjoint_singletonPoints_of_card_ne_one hanti hs hcard
  have hunion : (s ∪ singletonPoints F).card =
      s.card + (singletonPoints F).card := card_union_of_disjoint hdisj
  have hground : (s ∪ singletonPoints F).card ≤ n := by
    simpa using card_le_card (subset_univ (s ∪ singletonPoints F))
  omega

/-- If level one occurs, all occupied levels lie in `1,...,n-r`. -/
theorem occupiedLevels_subset_Icc_of_one
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hnr : r + 1 ≤ n) (hF : IsMultiplicityAntichain F r)
    (hone : 1 ∈ occupiedLevels F) :
    occupiedLevels F ⊆ Finset.Icc 1 (n - r) := by
  have hsingle : r ≤ (singletonPoints F).card := by
    rw [card_singletonPoints]
    exact hF.2 1 hone
  intro i hi
  have hiPos : 1 ≤ i := by
    have hi0 := (mem_occupiedLevels.mp hi).1
    by_contra
    have : i = 0 := by omega
    subst i
    exact zero_not_mem_occupiedLevels hr hF hi
  apply mem_Icc.mpr
  refine ⟨hiPos, ?_⟩
  by_cases hi1 : i = 1
  · omega
  · obtain ⟨s, hslevel⟩ := (mem_occupiedLevels.mp hi).2
    have hsF := (mem_level.mp hslevel).1
    have hscard := (mem_level.mp hslevel).2
    have hle := card_le_ground_sub_singletons hF.1 hsingle hsF (by omega)
    omega

theorem card_occupiedLevels_le_of_one
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hnr : r + 1 ≤ n) (hF : IsMultiplicityAntichain F r)
    (hone : 1 ∈ occupiedLevels F) :
    (occupiedLevels F).card ≤ n - r := by
  have hcard := card_le_card (occupiedLevels_subset_Icc_of_one hr hnr hF hone)
  simpa [hnr] using hcard

/-! ### The complementary top-level reduction -/

/-- Complementing every member reverses the set of occupied levels. -/
theorem occupiedLevels_compls {n : ℕ} (F : Family (Fin n)) :
    occupiedLevels (Finset.compls F) =
      (occupiedLevels F).image (fun i => n - i) := by
  ext i
  constructor
  · intro hi
    have hi' := mem_occupiedLevels.mp hi
    have hlevel := hi'.2
    rw [level_compls F (by simpa using hi'.1), Finset.compls_nonempty] at hlevel
    apply mem_image.mpr
    refine ⟨n - i, ?_, by omega⟩
    apply mem_occupiedLevels.mpr
    refine ⟨by omega, ?_⟩
    simpa [show n - (n - i) = i by omega] using hlevel
  · intro hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    have hj' := mem_occupiedLevels.mp hj
    apply mem_occupiedLevels.mpr
    refine ⟨by omega, ?_⟩
    rw [level_compls F (by simp), Finset.compls_nonempty]
    simpa [show n - (n - j) = j by omega] using hj'.2

@[simp] theorem card_occupiedLevels_compls {n : ℕ} (F : Family (Fin n)) :
    (occupiedLevels (Finset.compls F)).card = (occupiedLevels F).card := by
  rw [occupiedLevels_compls]
  apply card_image_of_injOn
  intro i hi j hj hij
  have hi' := (mem_occupiedLevels.mp hi).1
  have hj' := (mem_occupiedLevels.mp hj).1
  change n - i = n - j at hij
  omega

theorem isMultiplicityAntichain_compls
    {n r : ℕ} {F : Family (Fin n)}
    (hF : IsMultiplicityAntichain F r) :
    IsMultiplicityAntichain (Finset.compls F) r := by
  refine ⟨isSperner_compls hF.1, ?_⟩
  intro i hi
  have hiLe := (mem_occupiedLevels.mp hi).1
  have hrev : n - i ∈ occupiedLevels F := by
    rw [occupiedLevels_compls] at hi
    obtain ⟨j, hj, hji⟩ := mem_image.mp hi
    have hjLe := (mem_occupiedLevels.mp hj).1
    have : j = n - i := by omega
    simpa [this] using hj
  rw [card_level_compls F (by simpa using hiLe)]
  simpa using hF.2 (n - i) hrev

theorem card_occupiedLevels_le_of_penultimate
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hnr : r + 1 ≤ n) (hF : IsMultiplicityAntichain F r)
    (htop : n - 1 ∈ occupiedLevels F) :
    (occupiedLevels F).card ≤ n - r := by
  let G : Family (Fin n) := Finset.compls F
  have hG : IsMultiplicityAntichain G r :=
    isMultiplicityAntichain_compls hF
  have hone : 1 ∈ occupiedLevels G := by
    rw [show occupiedLevels G =
      (occupiedLevels F).image (fun i => n - i) by
        simpa [G] using occupiedLevels_compls F]
    apply mem_image.mpr
    exact ⟨n - 1, htop, by omega⟩
  have hbound := card_occupiedLevels_le_of_one hr hnr hG hone
  simpa [G] using hbound

/-! ### Forcing all middle levels -/

theorem occupiedLevels_subset_middle_of_boundary_free
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hF : IsMultiplicityAntichain F r)
    (hone : 1 ∉ occupiedLevels F) (hpen : n - 1 ∉ occupiedLevels F) :
    occupiedLevels F ⊆ Finset.Icc 2 (n - 2) := by
  intro i hi
  have hiLe := (mem_occupiedLevels.mp hi).1
  have hi0 : i ≠ 0 := fun h =>
    zero_not_mem_occupiedLevels hr hF (h ▸ hi)
  have hiTop : i ≠ n := fun h =>
    top_not_mem_occupiedLevels hr hF (h ▸ hi)
  have hi1 : i ≠ 1 := fun h => hone (h ▸ hi)
  have hiPen : i ≠ n - 1 := fun h => hpen (h ▸ hi)
  exact mem_Icc.mpr ⟨by omega, by omega⟩

theorem card_occupiedLevels_le_of_boundary_free
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hF : IsMultiplicityAntichain F r)
    (hone : 1 ∉ occupiedLevels F) (hpen : n - 1 ∉ occupiedLevels F) :
    (occupiedLevels F).card ≤ n - 3 := by
  have hcard := card_le_card
    (occupiedLevels_subset_middle_of_boundary_free hr hF hone hpen)
  simpa [Nat.card_Icc, show n - 2 - 1 = n - 3 by omega] using hcard

/-- Section 17 upper bound: at most the `n-3` middle levels can occur. -/
theorem card_occupiedLevels_le_middle
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 4 ≤ r) (hnr : r + 1 ≤ n)
    (hF : IsMultiplicityAntichain F r) :
    (occupiedLevels F).card ≤ n - 3 := by
  by_cases hone : 1 ∈ occupiedLevels F
  · have hbound := card_occupiedLevels_le_of_one (by omega) hnr hF hone
    omega
  by_cases hpen : n - 1 ∈ occupiedLevels F
  · have hbound := card_occupiedLevels_le_of_penultimate (by omega) hnr hF hpen
    omega
  exact card_occupiedLevels_le_of_boundary_free
    (by omega) hF hone hpen

/-- Equality in the occupied-level bound forces exactly levels `2,...,n-2`. -/
theorem occupiedLevels_eq_middle_of_card
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 4 ≤ r) (hnr : r + 1 ≤ n)
    (hF : IsMultiplicityAntichain F r)
    (hcard : (occupiedLevels F).card = n - 3) :
    occupiedLevels F = Finset.Icc 2 (n - 2) := by
  have hone : 1 ∉ occupiedLevels F := by
    intro hone
    have hbound := card_occupiedLevels_le_of_one (by omega) hnr hF hone
    omega
  have hpen : n - 1 ∉ occupiedLevels F := by
    intro hpen
    have hbound := card_occupiedLevels_le_of_penultimate (by omega) hnr hF hpen
    omega
  apply eq_of_subset_of_card_le
    (occupiedLevels_subset_middle_of_boundary_free (by omega) hF hone hpen)
  rw [hcard, Nat.card_Icc]
  omega

/-! ### Equivalence with the full-middle profile -/

/-- Discard every member outside the middle levels. -/
def middlePart {n : ℕ} (F : Family (Fin n)) : Family (Fin n) :=
  F.filter fun s => 2 ≤ s.card ∧ s.card ≤ n - 2

theorem level_middlePart_eq
    {n i : ℕ} (F : Family (Fin n)) (hi2 : 2 ≤ i) (hin : i ≤ n - 2) :
    level (middlePart F) i = level F i := by
  ext s
  constructor
  · intro hs
    exact mem_level.mpr ⟨(mem_filter.mp (mem_level.mp hs).1).1,
      (mem_level.mp hs).2⟩
  · intro hs
    have hs' := mem_level.mp hs
    apply mem_level.mpr
    refine ⟨mem_filter.mpr ⟨hs'.1, ?_⟩, hs'.2⟩
    omega

theorem isSperner_middlePart
    {n : ℕ} {F : Family (Fin n)} (hF : IsSperner F) :
    IsSperner (middlePart F) := by
  intro s hs t ht hst hsub
  apply hst
  exact hF.eq (mem_filter.mp hs).1 (mem_filter.mp ht).1 hsub

theorem occupiedLevels_middlePart_eq
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 1 ≤ r) (hlevels : HasMultiplicities F r 2 (n - 2)) :
    occupiedLevels (middlePart F) = Finset.Icc 2 (n - 2) := by
  ext i
  constructor
  · intro hi
    obtain ⟨s, hs⟩ := (mem_occupiedLevels.mp hi).2
    have hsfilter := (mem_filter.mp (mem_level.mp hs).1).2
    have hscard := (mem_level.mp hs).2
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro hi
    have hi' := mem_Icc.mp hi
    apply mem_occupiedLevels.mpr
    refine ⟨by omega, ?_⟩
    rw [level_middlePart_eq F hi'.1 hi'.2]
    apply card_pos.mp
    have hmult := hlevels i hi'.1 hi'.2
    unfold HasMultiplicityAt at hmult
    omega

theorem isMultiplicityAntichain_middlePart
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 1 ≤ r) (hanti : IsSperner F)
    (hlevels : HasMultiplicities F r 2 (n - 2)) :
    IsMultiplicityAntichain (middlePart F) r := by
  refine ⟨isSperner_middlePart hanti, ?_⟩
  intro i hi
  have hi' : i ∈ Finset.Icc 2 (n - 2) := by
    rw [← occupiedLevels_middlePart_eq hr hlevels]
    exact hi
  rw [level_middlePart_eq F (mem_Icc.mp hi').1 (mem_Icc.mp hi').2]
  exact hlevels i (mem_Icc.mp hi').1 (mem_Icc.mp hi').2

/-- The original extremal event: an `r`-multiplicity antichain attaining `n-3` levels. -/
def OccupiedMiddleProfileExists (n r : ℕ) : Prop :=
  ∃ F : Family (Fin n),
    IsMultiplicityAntichain F r ∧ (occupiedLevels F).card = n - 3

/-- For `r ≥ 4`, attaining `n-3` occupied levels is exactly the full-middle profile. -/
theorem occupiedMiddleProfileExists_iff_fullMiddleProfileExists
    {n r : ℕ} (hr : 4 ≤ r) (hnr : r + 1 ≤ n) :
    OccupiedMiddleProfileExists n r ↔ FullMiddleProfileExists n r := by
  constructor
  · rintro ⟨F, hF, hcard⟩
    have hoccupied := occupiedLevels_eq_middle_of_card hr hnr hF hcard
    refine ⟨F, hF.1, ?_⟩
    intro i hi2 hin
    exact hF.2 i (by rw [hoccupied]; exact mem_Icc.mpr ⟨hi2, hin⟩)
  · rintro ⟨F, hanti, hlevels⟩
    let M := middlePart F
    have hM : IsMultiplicityAntichain M r :=
      isMultiplicityAntichain_middlePart (by omega) hanti hlevels
    refine ⟨M, hM, ?_⟩
    rw [show occupiedLevels M = Finset.Icc 2 (n - 2) by
      simpa [M] using occupiedLevels_middlePart_eq (by omega) hlevels,
      Nat.card_Icc]
    omega

end Erdos776.Uniform
