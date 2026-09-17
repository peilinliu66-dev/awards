import Erdos776.Uniform.SmallRangeCertificate

/-!
# Published statement of Erdős Problem 776

The definitions in this file deliberately follow the wording published at
<https://www.erdosproblems.com/776>. They form a short review façade over the
more reusable definitions used by the proof.

The published statement labels the ground set by `1,...,n`; `Fin n` labels the
same finite set by `0,...,n-1`. This relabelling does not affect cardinality,
inclusion, or set size. An indexed list of sets loses no information when
represented by a `Finset`: the strict antichain condition already forbids
duplicate entries.
-/

namespace Erdos776.Uniform

open Finset
open Erdos776.Antichain

/-- The problem condition: an antichain with at least `r` sets of every size
that occurs at all. -/
def ProblemAdmissible {n : ℕ} (F : Family (Fin n)) (r : ℕ) : Prop :=
  IsSperner F ∧
    ∀ t, (level F t).Nonempty → r ≤ (level F t).card

/-- The target event: such a family realizes exactly `n-3` sizes. -/
def ProblemTargetExists (n r : ℕ) : Prop :=
  ∃ F : Family (Fin n),
    ProblemAdmissible F r ∧ (occupiedLevels F).card = n - 3

/-- `N` is the least integer after which the problem target always exists. -/
def ProblemThreshold (r N : ℕ) : Prop :=
  (∀ n, N < n → ProblemTargetExists n r) ∧
    ∀ M, (∀ n, M < n → ProblemTargetExists n r) → N ≤ M

/-- A convenient stronger certificate: `N` fails and every larger size works. -/
def ProblemLastFailure (r N : ℕ) : Prop :=
  (¬ ProblemTargetExists N r) ∧
    ∀ n, N < n → ProblemTargetExists n r

/-- The published multiplicity condition is exactly the internal definition. -/
theorem problemAdmissible_iff_isMultiplicityAntichain
    {n r : ℕ} {F : Family (Fin n)} :
    ProblemAdmissible F r ↔ IsMultiplicityAntichain F r := by
  constructor
  · rintro ⟨hanti, hlevels⟩
    refine ⟨hanti, ?_⟩
    intro i hi
    exact hlevels i (mem_occupiedLevels.mp hi).2
  · rintro ⟨hanti, hlevels⟩
    refine ⟨hanti, ?_⟩
    intro t ht
    apply hlevels t
    apply mem_occupiedLevels.mpr
    refine ⟨?_, ht⟩
    obtain ⟨s, hs⟩ := ht
    have hcard : s.card = t := (mem_level.mp hs).2
    have hle := card_le_card (subset_univ s)
    simpa [hcard] using hle

/-- The published target is exactly the occupied-level event used internally. -/
theorem problemTargetExists_iff_occupiedMiddleProfileExists
    {n r : ℕ} :
    ProblemTargetExists n r ↔ OccupiedMiddleProfileExists n r := by
  constructor
  · rintro ⟨F, hF, hcard⟩
    exact ⟨F, problemAdmissible_iff_isMultiplicityAntichain.mp hF, hcard⟩
  · rintro ⟨F, hF, hcard⟩
    exact ⟨F, problemAdmissible_iff_isMultiplicityAntichain.mpr hF, hcard⟩

/-- In the theorem range, the problem target is the full middle-profile event. -/
theorem problemTargetExists_iff_fullMiddleProfileExists
    {n r : ℕ} (hr : 4 ≤ r) (hnr : r + 1 ≤ n) :
    ProblemTargetExists n r ↔ FullMiddleProfileExists n r := by
  rw [problemTargetExists_iff_occupiedMiddleProfileExists,
    occupiedMiddleProfileExists_iff_fullMiddleProfileExists hr hnr]

/-- Failure at `N` followed by success everywhere above makes `N` least. -/
theorem problemThreshold_of_lastFailure
    {r N : ℕ} (h : ProblemLastFailure r N) :
    ProblemThreshold r N := by
  refine ⟨h.2, ?_⟩
  intro M hM
  by_contra hNM
  exact h.1 (hM N (by omega))

/-- A full-profile last failure is the same last failure in problem language. -/
theorem problemLastFailure_of_fullMiddleProfileThresholdAt
    {r N : ℕ} (hr : 4 ≤ r) (hrN : r + 1 ≤ N)
    (h : FullMiddleProfileThresholdAt r N) :
    ProblemLastFailure r N := by
  refine ⟨?_, ?_⟩
  · intro hproblem
    exact h.1 ((problemTargetExists_iff_fullMiddleProfileExists hr hrN).mp hproblem)
  · intro n hn
    apply (problemTargetExists_iff_fullMiddleProfileExists hr (by omega)).mpr
    exact h.2 n hn


end Erdos776.Uniform
