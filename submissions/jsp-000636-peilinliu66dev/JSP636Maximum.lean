import Mathlib
import JSP636SmallParameters

/-! Maximum-value and exact-multiplicity interfaces for JSP636.
Extracted without changing statements from the all-parameter extension.
Mathematics: He-Tang and Thiim; MIT, see extension provenance. -/
namespace JSP636
noncomputable section
open Finset
open Erdos776.Antichain Erdos776.Uniform

/-- `k` is achieved and is an upper bound for EVERY admissible family. -/
def OptimalLevels (n r k : ℕ) : Prop :=
  (∃ F : Family (Fin n),
    ProblemAdmissible F r ∧ (occupiedLevels F).card = k) ∧
  (∀ F : Family (Fin n),
    ProblemAdmissible F r → (occupiedLevels F).card ≤ k)

/-- The least threshold for the actual maximum, with strict `N < n`. -/
def ExactThreshold (r N : ℕ) : Prop :=
  (∀ n : ℕ, N < n → OptimalLevels n r (n - 3)) ∧
  (∀ M : ℕ, (∀ n : ℕ, M < n → OptimalLevels n r (n - 3)) → N ≤ M)


/-- The general upper bound upgrades any true target construction to an optimum. -/
theorem optimalLevels_of_target {n r : ℕ}
    (hr : 2 ≤ r) (hn : 4 ≤ n) (h : ProblemTargetExists n r) :
    OptimalLevels n r (n - 3) := by
  refine ⟨h, ?_⟩
  intro F hF
  exact universal_occupiedLevels_bound hr hn
    (problemAdmissible_iff_isMultiplicityAntichain.mp hF)

/-- The finite boundary really has maximum one, not zero. -/
theorem optimalLevels_three_two : OptimalLevels 3 2 1 := by
  refine ⟨⟨twoSingletonsThree, twoSingletonsThree_admissible,
    twoSingletonsThree_card⟩, ?_⟩
  intro F hF
  exact r2_three_upper F (problemAdmissible_iff_isMultiplicityAntichain.mp hF)

/-- This is deliberately a failure of OPTIMALITY. Existence of zero levels
at n=3 would hold (the empty family), but would be the wrong predicate. -/
theorem r2_three_not_optimal : ¬ OptimalLevels 3 2 (3 - 3) := by
  intro h
  have hbound := h.2 twoSingletonsThree twoSingletonsThree_admissible
  rw [twoSingletonsThree_card] at hbound
  omega

theorem r3_eight_not_optimal : ¬ OptimalLevels 8 3 (8 - 3) := by
  intro h
  exact r3_eight_target_fails h.1


/-! ## The literal extremal number g(n,r) -/

theorem empty_problemAdmissible (n r : ℕ) :
    ProblemAdmissible (∅ : Family (Fin n)) r := by
  refine ⟨?_, ?_⟩
  · intro s hs
    simp at hs
  · intro t ht
    simp [level] at ht

@[simp] theorem occupiedLevels_empty (n : ℕ) :
    occupiedLevels (∅ : Family (Fin n)) = ∅ := by
  ext t
  simp [mem_occupiedLevels, level]

/-- A finite, nonempty set of actually attained occupied-level counts. -/
def attainableLevels (n r : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.univ : Finset (Family (Fin n))).filter
    (fun F => ProblemAdmissible F r)).image (fun F => (occupiedLevels F).card)

@[simp] theorem mem_attainableLevels (n r k : ℕ) :
    k ∈ attainableLevels n r ↔
      ∃ F : Family (Fin n), ProblemAdmissible F r ∧ (occupiedLevels F).card = k := by
  classical
  simp [attainableLevels]

theorem attainableLevels_nonempty (n r : ℕ) : (attainableLevels n r).Nonempty := by
  refine ⟨0, (mem_attainableLevels n r 0).mpr ?_⟩
  exact ⟨∅, empty_problemAdmissible n r, by simp⟩

/-- The maximum over admissible families; nonemptiness is proved explicitly. -/
def g (n r : ℕ) : ℕ :=
  (attainableLevels n r).max' (attainableLevels_nonempty n r)

theorem g_spec (n r : ℕ) : OptimalLevels n r (g n r) := by
  classical
  refine ⟨?_, ?_⟩
  · exact (mem_attainableLevels n r (g n r)).mp
      (Finset.max'_mem (attainableLevels n r) (attainableLevels_nonempty n r))
  · intro F hF
    exact Finset.le_max' (attainableLevels n r) (occupiedLevels F).card
      ((mem_attainableLevels n r (occupiedLevels F).card).mpr ⟨F, hF, rfl⟩)

/-- Compatibility with the upstream extremal API, for all n and r.
The auxiliary maximum is not a different extremal problem. -/
theorem g_eq_extremalOccupiedLevels (n r : ℕ) :
    g n r = extremalOccupiedLevels n r := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨F, hF, hcard⟩ := (g_spec n r).1
    have hbound := card_occupiedLevels_le_extremal
      (problemAdmissible_iff_isMultiplicityAntichain.mp hF)
    simpa only [hcard] using hbound
  · unfold extremalOccupiedLevels
    apply Finset.sup_le
    intro F hmem
    by_cases hF : IsMultiplicityAntichain F r
    · rw [if_pos hF]
      exact (g_spec n r).2 F
        (problemAdmissible_iff_isMultiplicityAntichain.mpr hF)
    · rw [if_neg hF]
      exact Nat.zero_le _

theorem optimalLevels_unique {n r k l : ℕ}
    (hk : OptimalLevels n r k) (hl : OptimalLevels n r l) : k = l := by
  obtain ⟨F, hF, hFk⟩ := hk.1
  obtain ⟨G, hG, hGl⟩ := hl.1
  have hkl := hl.2 F hF
  have hlk := hk.2 G hG
  omega

theorem optimalLevels_iff_g_eq (n r k : ℕ) :
    OptimalLevels n r k ↔ g n r = k := by
  constructor
  · intro h
    exact optimalLevels_unique (g_spec n r) h
  · intro h
    rw [← h]
    exact g_spec n r

theorem g_three_two : g 3 2 = 1 :=
  (optimalLevels_iff_g_eq 3 2 1).mp optimalLevels_three_two

/-- Correct uniform maximum upper bound for all admissible n,r. -/
theorem g_le_sub_three {n r : ℕ} (hr : 2 ≤ r) (hn : 4 ≤ n) :
    g n r ≤ n - 3 := by
  obtain ⟨F, hF, hcard⟩ := (g_spec n r).1
  have h := universal_occupiedLevels_bound hr hn
    (problemAdmissible_iff_isMultiplicityAntichain.mp hF)
  simpa only [hcard] using h


/-! ## The original "exactly r per occurring level" convention -/

/-- The exact-multiplicity wording of the original Erdős–Trotter question. -/
def ExactAdmissible {n : ℕ} (F : Family (Fin n)) (r : ℕ) : Prop :=
  IsSperner F ∧ ∀ t : ℕ, (level F t).Nonempty → (level F t).card = r

theorem ExactAdmissible.to_admissible {n r : ℕ} {F : Family (Fin n)}
    (hF : ExactAdmissible F r) : ProblemAdmissible F r := by
  refine ⟨hF.1, ?_⟩
  intro t ht
  rw [hF.2 t ht]

/-- Thin each actual occupied slice to exactly r members. The family is
constructed as a finite union, and the occurring levels are preserved exactly. -/
theorem exists_exact_subfamily {n r : ℕ} {F : Family (Fin n)}
    (hr : 0 < r) (hF : ProblemAdmissible F r) :
    ∃ E : Family (Fin n), E ⊆ F ∧ ExactAdmissible E r ∧
      occupiedLevels E = occupiedLevels F := by
  classical
  have hex (t : ℕ) (ht : t ∈ occupiedLevels F) :
      ∃ D : Family (Fin n), D ⊆ level F t ∧ D.card = r :=
    Finset.exists_subset_card_eq (hF.2 t (mem_occupiedLevels.mp ht).2)
  let selected : ℕ → Family (Fin n) := fun t =>
    if ht : t ∈ occupiedLevels F then Classical.choose (hex t ht) else ∅
  have hselected (t : ℕ) (ht : t ∈ occupiedLevels F) :
      selected t ⊆ level F t ∧ (selected t).card = r := by
    dsimp only [selected]
    rw [dif_pos ht]
    exact Classical.choose_spec (hex t ht)
  let E : Family (Fin n) := (occupiedLevels F).biUnion selected
  have hEF : E ⊆ F := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp hs
    exact (mem_level.mp ((hselected t ht).1 hst)).1
  have hlevel (t : ℕ) (ht : t ∈ occupiedLevels F) : level E t = selected t := by
    ext s
    constructor
    · intro hs
      obtain ⟨j, hj, hsj⟩ := Finset.mem_biUnion.mp (mem_level.mp hs).1
      have hsjt : s.card = j := (mem_level.mp ((hselected j hj).1 hsj)).2
      have hst : s.card = t := (mem_level.mp hs).2
      have hjt : j = t := by omega
      simpa only [hjt] using hsj
    · intro hs
      exact mem_level.mpr
        ⟨Finset.mem_biUnion.mpr ⟨t, ht, hs⟩,
          (mem_level.mp ((hselected t ht).1 hs)).2⟩
  have hocc : occupiedLevels E = occupiedLevels F := by
    apply Finset.Subset.antisymm
    · intro t ht
      have ht' := mem_occupiedLevels.mp ht
      obtain ⟨s, hs⟩ := ht'.2
      exact mem_occupiedLevels.mpr
        ⟨ht'.1, s, mem_level.mpr ⟨hEF (mem_level.mp hs).1, (mem_level.mp hs).2⟩⟩
    · intro t ht
      apply mem_occupiedLevels.mpr
      refine ⟨(mem_occupiedLevels.mp ht).1, ?_⟩
      rw [hlevel t ht]
      apply Finset.card_pos.mp
      rw [(hselected t ht).2]
      exact hr
  have hanti : IsSperner E := by
    intro s hs t ht hne hst
    exact hne (hF.1.eq (hEF hs) (hEF ht) hst)
  refine ⟨E, hEF, ⟨hanti, ?_⟩, hocc⟩
  intro t ht
  have htF : (level F t).Nonempty := by
    obtain ⟨s, hs⟩ := ht
    exact ⟨s, mem_level.mpr ⟨hEF (mem_level.mp hs).1, (mem_level.mp hs).2⟩⟩
  have htocc : t ∈ occupiedLevels F := by
    obtain ⟨s, hs⟩ := htF
    have hcard : s.card = t := (mem_level.mp hs).2
    have hle : s.card ≤ n := by simpa using s.card_le_univ
    exact mem_occupiedLevels.mpr ⟨by omega, s, hs⟩
  rw [hlevel t htocc, (hselected t htocc).2]

/-- The two multiplicity conventions have the same attainable level counts. -/
theorem exact_attainability_iff {n r k : ℕ} (hr : 0 < r) :
    (∃ F : Family (Fin n), ExactAdmissible F r ∧ (occupiedLevels F).card = k) ↔
    (∃ F : Family (Fin n), ProblemAdmissible F r ∧ (occupiedLevels F).card = k) := by
  constructor
  · rintro ⟨F, hF, hcard⟩
    exact ⟨F, hF.to_admissible, hcard⟩
  · rintro ⟨F, hF, hcard⟩
    obtain ⟨E, hEF, hE, hocc⟩ := exists_exact_subfamily hr hF
    exact ⟨E, hE, by simpa only [hocc] using hcard⟩

/-- Original maximum formulation, with exact multiplicities. -/
def ExactOptimalLevels (n r k : ℕ) : Prop :=
  (∃ F : Family (Fin n), ExactAdmissible F r ∧ (occupiedLevels F).card = k) ∧
  (∀ F : Family (Fin n), ExactAdmissible F r → (occupiedLevels F).card ≤ k)

theorem exactOptimalLevels_iff {n r k : ℕ} (hr : 0 < r) :
    ExactOptimalLevels n r k ↔ OptimalLevels n r k := by
  constructor
  · rintro ⟨hex, hupper⟩
    refine ⟨(exact_attainability_iff hr).mp hex, ?_⟩
    intro F hF
    obtain ⟨E, hEF, hE, hocc⟩ := exists_exact_subfamily hr hF
    simpa only [hocc] using hupper E hE
  · rintro ⟨hex, hupper⟩
    exact ⟨(exact_attainability_iff hr).mpr hex,
      fun F hF => hupper F hF.to_admissible⟩


end
end JSP636

#print axioms JSP636.g_eq_extremalOccupiedLevels
#print axioms JSP636.exactOptimalLevels_iff
