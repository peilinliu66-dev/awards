import Erdos524.DifferenceVolume
import Mathlib.Analysis.Normed.Operator.Basic

/-!
The compact-convex intersection step in the classical finite Anderson argument.
Active formalization; no Gaussian comparison or final probability theorem is
assumed as an axiom.
-/

namespace Erdos524.ShiftIntersection

open Set MeasureTheory
open scoped Pointwise
open Erdos524.CoordinateSymmetrization
open Erdos524.DifferenceVolume

variable {n : ℕ}

def shiftedIntersection (A B : Set (Fin (n + 1) → ℝ)) (t : Fin (n + 1) → ℝ) :
    Set (Fin (n + 1) → ℝ) := {x | x ∈ A ∧ x - t ∈ B}

theorem isCompact_shiftedIntersection {A B : Set (Fin (n + 1) → ℝ)}
    (hA : IsCompact A) (hB : IsClosed B) (t : Fin (n + 1) → ℝ) :
    IsCompact (shiftedIntersection A B t) :=
  hA.inter_right (hB.preimage (by fun_prop))

theorem convex_shiftedIntersection {A B : Set (Fin (n + 1) → ℝ)}
    (hA : Convex ℝ A) (hB : Convex ℝ B) (t : Fin (n + 1) → ℝ) :
    Convex ℝ (shiftedIntersection A B t) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hA hx.1 hy.1 ha hb hab, ?_⟩
  have hmem := hB hx.2 hy.2 ha hb hab
  have he : a • (x - t) + b • (y - t) = a • x + b • y - t := by
    ext j
    change a * (x j - t j) + b * (y j - t j) = a * x j + b * y j - t j
    calc
      a * (x j - t j) + b * (y j - t j) = a * x j + b * y j - (a + b) * t j := by ring
      _ = a * x j + b * y j - t j := by rw [hab, one_mul]
  rwa [he] at hmem

theorem half_difference_subset_inter {A B : Set (Fin (n + 1) → ℝ)}
    (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hnegA : ∀ ⦃x⦄, x ∈ A → -x ∈ A)
    (hnegB : ∀ ⦃x⦄, x ∈ B → -x ∈ B) (t : Fin (n + 1) → ℝ) :
    (1 / 2 : ℝ) • difference (shiftedIntersection A B t) (shiftedIntersection A B t)
      ⊆ A ∩ B := by
  rintro x ⟨y, ⟨u, hu, v, hv, rfl⟩, rfl⟩
  constructor
  · have hmem := hA hu.1 (hnegA hv.1)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have he : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • (-v) = (1 / 2 : ℝ) • (u - v) := by
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rwa [he] at hmem
  · have hmem := hB hu.2 (hnegB hv.2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have he : (1 / 2 : ℝ) • (u - t) + (1 / 2 : ℝ) • (-(v - t)) =
        (1 / 2 : ℝ) • (u - v) := by
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rwa [he] at hmem

/-- Translating one symmetric convex set cannot increase its intersection
volume with another compact symmetric convex set. -/
theorem volume_shiftedIntersection_le {A B : Set (Fin (n + 1) → ℝ)}
    (hcompact : IsCompact A) (hclosed : IsClosed B)
    (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hnegA : ∀ ⦃x⦄, x ∈ A → -x ∈ A)
    (hnegB : ∀ ⦃x⦄, x ∈ B → -x ∈ B) (t : Fin (n + 1) → ℝ) :
    volume (shiftedIntersection A B t) ≤ volume (A ∩ B) := by
  exact (volume_le_half_difference (isCompact_shiftedIntersection hcompact hclosed t)
    (convex_shiftedIntersection hA hB t)).trans
    (measure_mono (half_difference_subset_inter hA hB hnegA hnegB t))

/-! The linear-image version also covers singular maps. Gaussian layer-cake
can therefore be carried out in the source coordinates, without an inverse
covariance matrix or a nonsingular-density assumption. -/

variable {m : ℕ}

def linearShiftSlice (L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin m → ℝ))
    (E : Set (Fin (n + 1) → ℝ)) (K : Set (Fin m → ℝ)) (t : Fin m → ℝ) :
    Set (Fin (n + 1) → ℝ) := {x | x ∈ E ∧ L x + t ∈ K}

theorem isCompact_linearShiftSlice
    (L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin m → ℝ))
    {E : Set (Fin (n + 1) → ℝ)} {K : Set (Fin m → ℝ)}
    (hE : IsCompact E) (hK : IsClosed K) (t : Fin m → ℝ) :
    IsCompact (linearShiftSlice L E K t) :=
  hE.inter_right (hK.preimage (L.continuous.add continuous_const))

theorem convex_linearShiftSlice
    (L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin m → ℝ))
    {E : Set (Fin (n + 1) → ℝ)} {K : Set (Fin m → ℝ)}
    (hE : Convex ℝ E) (hK : Convex ℝ K) (t : Fin m → ℝ) :
    Convex ℝ (linearShiftSlice L E K t) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hE hx.1 hy.1 ha hb hab, ?_⟩
  have hmem := hK hx.2 hy.2 ha hb hab
  have he : a • (L x + t) + b • (L y + t) = L (a • x + b • y) + t := by
    rw [L.map_add, L.map_smul, L.map_smul]
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      a * (L x j + t j) + b * (L y j + t j) =
          a * L x j + b * L y j + (a + b) * t j := by ring
      _ = a * L x j + b * L y j + t j := by rw [hab, one_mul]
  rwa [he] at hmem

theorem half_difference_linearShiftSlice_subset
    (L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin m → ℝ))
    {E : Set (Fin (n + 1) → ℝ)} {K : Set (Fin m → ℝ)}
    (hE : Convex ℝ E) (hK : Convex ℝ K)
    (hnegE : ∀ ⦃x⦄, x ∈ E → -x ∈ E)
    (hnegK : ∀ ⦃x⦄, x ∈ K → -x ∈ K) (t : Fin m → ℝ) :
    (1 / 2 : ℝ) • difference (linearShiftSlice L E K t) (linearShiftSlice L E K t)
      ⊆ linearShiftSlice L E K 0 := by
  rintro x ⟨z, ⟨u, hu, v, hv, rfl⟩, rfl⟩
  constructor
  · have hmem := hE hu.1 (hnegE hv.1)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have he : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • (-v) = (1 / 2 : ℝ) • (u - v) := by
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rwa [he] at hmem
  · have hmem := hK hu.2 (hnegK hv.2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have he : (1 / 2 : ℝ) • (L u + t) + (1 / 2 : ℝ) • (-(L v + t)) =
        L ((1 / 2 : ℝ) • (u - v)) + 0 := by
      rw [L.map_smul, L.map_sub]
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.sub_apply,
        Pi.zero_apply, add_zero, smul_eq_mul]
      ring
    rwa [he] at hmem

/-- Geometric Anderson comparison in source coordinates, valid for singular
as well as nonsingular continuous linear maps. -/
theorem volume_linearShiftSlice_le
    (L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin m → ℝ))
    {E : Set (Fin (n + 1) → ℝ)} {K : Set (Fin m → ℝ)}
    (hcompact : IsCompact E) (hclosed : IsClosed K)
    (hE : Convex ℝ E) (hK : Convex ℝ K)
    (hnegE : ∀ ⦃x⦄, x ∈ E → -x ∈ E)
    (hnegK : ∀ ⦃x⦄, x ∈ K → -x ∈ K) (t : Fin m → ℝ) :
    volume (linearShiftSlice L E K t) ≤ volume (linearShiftSlice L E K 0) := by
  exact (volume_le_half_difference (isCompact_linearShiftSlice L hcompact hclosed t)
    (convex_linearShiftSlice L hE hK t)).trans
    (measure_mono (half_difference_linearShiftSlice_subset L hE hK hnegE hnegK t))

end Erdos524.ShiftIntersection
