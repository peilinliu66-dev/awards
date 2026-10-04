import Erdos524.CoordinateVolume
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
The special difference-body volume inequality needed for finite Anderson.
This module is under active compilation. It does not assume Brunn–Minkowski
and does not declare the final random-polynomial theorem.
-/

namespace Erdos524.DifferenceVolume

open Set MeasureTheory
open scoped Pointwise ENNReal
open Erdos524.CoordinateSymmetrization
open Erdos524.CoordinateVolume

variable {n : ℕ}

theorem difference_eq_sub (A B : Set (Fin (n + 1) → ℝ)) :
    difference A B = A - B := by
  ext x
  rfl

theorem isCompact_difference {A B : Set (Fin (n + 1) → ℝ)}
    (hA : IsCompact A) (hB : IsCompact B) : IsCompact (difference A B) := by
  have he : difference A B =
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) ↦ z.1 - z.2) '' (A ×ˢ B) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      exact ⟨(a, b), ⟨ha, hb⟩, hab⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩
      exact ⟨a, ha, b, hb, hab⟩
  rw [he]
  exact (hA.prod hB).image (by fun_prop)

theorem convex_difference {A B : Set (Fin (n + 1) → ℝ)}
    (hA : Convex ℝ A) (hB : Convex ℝ B) : Convex ℝ (difference A B) := by
  rw [difference_eq_sub]
  exact hA.sub hB

/-- Successive volume-preserving symmetrizations prove this special case
directly, without importing a general Brunn–Minkowski inequality. -/
theorem volume_double_le_difference {A : Set (Fin (n + 1) → ℝ)}
    (hcompact : IsCompact A) (hconvex : Convex ℝ A) :
    volume ((2 : ℝ) • A) ≤ volume (difference A A) := by
  classical
  let is : List (Fin (n + 1)) := Finset.univ.toList
  have his : ∀ i, i ∈ is := by intro i; simp [is]
  have hscale : volume ((2 : ℝ) • symmList is A) = volume ((2 : ℝ) • A) := by
    rw [Measure.addHaar_smul_of_nonneg volume (by norm_num : (0 : ℝ) ≤ 2),
      Measure.addHaar_smul_of_nonneg volume (by norm_num : (0 : ℝ) ≤ 2),
      volume_symmList is hcompact hconvex]
  calc
    volume ((2 : ℝ) • A) = volume ((2 : ℝ) • symmList is A) := hscale.symm
    _ ≤ volume (symmList is (difference A A)) := by
      apply measure_mono
      exact double_symmList_subset is his hconvex
    _ = volume (difference A A) :=
      volume_symmList is (isCompact_difference hcompact hcompact)
        (convex_difference hconvex hconvex)

theorem volume_le_half_difference {A : Set (Fin (n + 1) → ℝ)}
    (hcompact : IsCompact A) (hconvex : Convex ℝ A) :
    volume A ≤ volume ((1 / 2 : ℝ) • difference A A) := by
  have hdouble := volume_double_le_difference hcompact hconvex
  have hcancel : (1 / 2 : ℝ) • ((2 : ℝ) • A) = A := by
    rw [smul_smul]
    norm_num
  let c : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ Module.finrank ℝ (Fin (n + 1) → ℝ))
  calc
    volume A = volume ((1 / 2 : ℝ) • ((2 : ℝ) • A)) := by rw [hcancel]
    _ = c * volume ((2 : ℝ) • A) :=
      Measure.addHaar_smul_of_nonneg volume (by norm_num : (0 : ℝ) ≤ 1 / 2) _
    _ ≤ c * volume (difference A A) := by gcongr
    _ = volume ((1 / 2 : ℝ) • difference A A) :=
      (Measure.addHaar_smul_of_nonneg volume (by norm_num : (0 : ℝ) ≤ 1 / 2) _).symm

end Erdos524.DifferenceVolume
