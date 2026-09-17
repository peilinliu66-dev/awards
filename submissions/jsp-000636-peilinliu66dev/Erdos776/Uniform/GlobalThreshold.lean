import Erdos776.Uniform.OccupiedLevels

/-!
# The global extremal function and threshold

This file packages the semantic occupied-level reduction as the extremal
function `g(n,r)` from the problem statement and proves that the existing
full-middle-profile threshold really is the least global threshold.
-/

namespace Erdos776.Uniform

open Finset
open Erdos776.Antichain

/-- The maximum number of occupied levels in an `r`-multiplicity antichain. -/
noncomputable def extremalOccupiedLevels (n r : ℕ) : ℕ :=
  by
    classical
    exact (Finset.univ : Finset (Family (Fin n))).sup fun F =>
      if IsMultiplicityAntichain F r then (occupiedLevels F).card else 0

/-- Every admissible family gives a lower bound for `extremalOccupiedLevels`. -/
theorem card_occupiedLevels_le_extremal
    {n r : ℕ} {F : Family (Fin n)} (hF : IsMultiplicityAntichain F r) :
    (occupiedLevels F).card ≤ extremalOccupiedLevels n r := by
  classical
  unfold extremalOccupiedLevels
  have hle := Finset.le_sup
    (s := (Finset.univ : Finset (Family (Fin n))))
    (f := fun G => if IsMultiplicityAntichain G r then
      (occupiedLevels G).card else 0) (mem_univ F)
  simpa [hF] using hle

/-- For `r ≥ 4`, the elementary reduction gives the global upper bound. -/
theorem extremalOccupiedLevels_le_middle
    {n r : ℕ} (hr : 4 ≤ r) (hnr : r + 1 ≤ n) :
    extremalOccupiedLevels n r ≤ n - 3 := by
  classical
  unfold extremalOccupiedLevels
  apply Finset.sup_le
  intro F hFmem
  by_cases hF : IsMultiplicityAntichain F r
  · simpa [hF] using card_occupiedLevels_le_middle hr hnr hF
  · simp [hF]

theorem extremalOccupiedLevels_eq_middle_iff
    {n r : ℕ} (hr : 4 ≤ r) (hnr : r + 1 ≤ n) :
    extremalOccupiedLevels n r = n - 3 ↔ OccupiedMiddleProfileExists n r := by
  classical
  constructor
  · intro hg
    have hpos : 0 < n - 3 := by omega
    have hle : n - 3 ≤
        (Finset.univ : Finset (Family (Fin n))).sup (fun F =>
          if IsMultiplicityAntichain F r then
            (occupiedLevels F).card else 0) := by
      have hle' : n - 3 ≤ extremalOccupiedLevels n r := hg.ge
      simpa only [extremalOccupiedLevels] using hle'
    rw [Finset.le_sup_iff hpos] at hle
    obtain ⟨F, hFuniv, hFcard⟩ := hle
    by_cases hF : IsMultiplicityAntichain F r
    · have hupper := card_occupiedLevels_le_middle hr hnr hF
      simp only [if_pos hF] at hFcard
      refine ⟨F, hF, ?_⟩
      exact Nat.le_antisymm hupper hFcard
    · simp only [if_neg hF] at hFcard
      omega
  · rintro ⟨F, hF, hcard⟩
    apply Nat.le_antisymm (extremalOccupiedLevels_le_middle hr hnr)
    rw [← hcard]
    exact card_occupiedLevels_le_extremal hF

/-- The numerical equality `g(n,r)=n-3` is the full-middle profile event. -/
theorem extremalOccupiedLevels_eq_middle_iff_fullMiddleProfileExists
    {n r : ℕ} (hr : 4 ≤ r) (hnr : r + 1 ≤ n) :
    extremalOccupiedLevels n r = n - 3 ↔ FullMiddleProfileExists n r := by
  rw [extremalOccupiedLevels_eq_middle_iff hr hnr,
    occupiedMiddleProfileExists_iff_fullMiddleProfileExists hr hnr]

/-- `N` is the least integer after which `g(n,r)=n-3` always holds. -/
def IsErdosThreshold (r N : ℕ) : Prop :=
  (∀ n, N < n → extremalOccupiedLevels n r = n - 3) ∧
    ∀ M, (∀ n, M < n → extremalOccupiedLevels n r = n - 3) → N ≤ M

/-- The full-middle threshold assembled earlier is the actual global threshold. -/
theorem isErdosThreshold_of_fullMiddleProfileThresholdAt
    {r N : ℕ} (hr : 4 ≤ r) (hrN : r + 1 ≤ N)
    (hthreshold : FullMiddleProfileThresholdAt r N) :
    IsErdosThreshold r N := by
  have hsuccess : ∀ n, N < n →
      extremalOccupiedLevels n r = n - 3 := by
    intro n hn
    apply (extremalOccupiedLevels_eq_middle_iff_fullMiddleProfileExists
      hr (by omega)).2
    exact hthreshold.2 n hn
  refine ⟨hsuccess, ?_⟩
  intro M hM
  by_contra hMN
  have hg := hM N (by omega)
  have hfull := (extremalOccupiedLevels_eq_middle_iff_fullMiddleProfileExists
    (n := N) hr hrN).1 hg
  exact hthreshold.1 hfull

/-- The standard uniform full-middle threshold is the actual global threshold. -/
theorem isErdosThreshold_of_fullMiddleProfileThreshold
    {r : ℕ} (hr : 4 ≤ r) (hthreshold : FullMiddleProfileThreshold r) :
    IsErdosThreshold r (2 * r + 5) := by
  apply isErdosThreshold_of_fullMiddleProfileThresholdAt hr (by omega)
  exact (fullMiddleProfileThreshold_iff_at r).mp hthreshold

/-- The single remaining lower-window input implies the global threshold. -/
theorem isErdosThreshold_of_lowerWindowFits
    (r : ℕ) (hr : 29 ≤ r) (hfit : LowerWindowFits r) :
    IsErdosThreshold r (2 * r + 5) := by
  exact isErdosThreshold_of_fullMiddleProfileThreshold (by omega)
    (fullMiddleProfileThreshold_of_lowerWindowFits r hr hfit)

end Erdos776.Uniform
