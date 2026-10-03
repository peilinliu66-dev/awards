/-
Copyright (c) 2026. Released under Apache 2.0.
Original compact-body extension of the maximal-simplex normalization proved
in the Apache-2.0 Erdos186.PZ.ConvexDensity.EnclosingBox dependency.
Only a dimension-dependent constant is needed; this does not assert the
sharp Rogers--Shephard binomial coefficient.
Compiled and audited; Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
-/
import Erdos131Research.Upstream.NormalizedDifference
import ErdosProblems.Erdos186.PZ.ConvexDensity.Normalization
import Mathlib.Analysis.Convex.Body
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open Set MeasureTheory
open scoped BigOperators Pointwise ENNReal

namespace Erdos131Research
noncomputable section
open Erdos186.PZ.ConvexDensity

/-- One fixed positive integer suffices in each dimension. -/
def rogersConstant (d : ℕ) : ℕ := ⌈finiteHullDeterminantVolumeFactor d⌉₊ + 1

theorem rogersConstant_pos (d : ℕ) : 0 < rogersConstant d := by
  simp [rogersConstant]

private theorem normalizedConstant_le (d : ℕ) :
    (2 : ENNReal) ^ d * normalizedBoxConstant d ≤ (rogersConstant d : ENNReal) := by
  apply (normalizedDifferenceConstant_le_ofReal d).trans
  have h : finiteHullDeterminantVolumeFactor d ≤ (rogersConstant d : ℝ) := by
    exact (Nat.le_ceil _).trans (by simp [rogersConstant])
  simpa using ENNReal.ofReal_le_ofReal h

private theorem exists_simplex_in_spanning_set {d : ℕ} {K : Set (EuclideanPoint d)}
    (hspan : affineSpan ℝ K = ⊤) :
    ∃ p : Fin (d + 1) → EuclideanPoint d,
      (∀ i, p i ∈ K) ∧ simplexDet p ≠ 0 := by
  classical
  obtain ⟨S, hSK, hSspan, hSind⟩ := exists_affineIndependent ℝ (EuclideanPoint d) K
  have hSf : S.Finite := finite_set_of_fin_dim_affineIndependent ℝ hSind
  obtain ⟨p, hp, hp0⟩ := exists_nonzero_simplex_of_affineSpan_eq_top hSf.toFinset
    (by simpa using hSspan.trans hspan)
  exact ⟨p, fun i => hSK (by simpa using hp i), hp0⟩

/-- Compactness supplies a genuinely maximal simplex over the entire body. -/
private theorem compact_maximal_simplex {d : ℕ} {K : Set (EuclideanPoint d)}
    (hcompact : IsCompact K) (hspan : affineSpan ℝ K = ⊤) :
    ∃ p : Fin (d + 1) → EuclideanPoint d,
      (∀ i, p i ∈ K) ∧ simplexDet p ≠ 0 ∧
        ∀ q : Fin (d + 1) → EuclideanPoint d,
          (∀ i, q i ∈ K) → |simplexDet q| ≤ |simplexDet p| := by
  classical
  obtain ⟨p₀, hp₀K, hp₀⟩ := exists_simplex_in_spanning_set hspan
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  letI : Nonempty K := ⟨⟨p₀ 0, hp₀K 0⟩⟩
  have hc : Continuous (fun q : Fin (d + 1) → K =>
      |simplexDet (fun i => (q i : EuclideanPoint d))|) := by
    unfold simplexDet simplexFrame
    simp only [Module.Basis.det_apply]
    apply Continuous.abs
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [Module.Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
    fun_prop
  obtain ⟨p, _hp, hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set (Fin (d + 1) → K)).Nonempty) hc.continuousOn
  refine ⟨fun i => p i, fun i => (p i).property, ?_, ?_⟩
  · intro hzero
    have hle := hmax (Set.mem_univ (fun i => (⟨p₀ i, hp₀K i⟩ : K)))
    change |simplexDet p₀| ≤ |simplexDet (fun i => (p i : EuclideanPoint d))| at hle
    rw [hzero, abs_zero] at hle
    exact hp₀ (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))
  · intro q hq
    let qK : Fin (d + 1) → K := fun i => ⟨q i, hq i⟩
    have hm := hmax (Set.mem_univ qK)
    simpa only [qK, Set.mem_setOf_eq] using hm

private theorem compact_difference_volume {d : ℕ} (K : Set (EuclideanPoint d))
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) (hne : K.Nonempty) :
    volume (K - K) ≤ (rogersConstant d : ENNReal) * volume K := by
  classical
  by_cases hspan : affineSpan ℝ K = ⊤
  · obtain ⟨p, hpK, hp, hmax⟩ := compact_maximal_simplex hcompact hspan
    let e := simplexAffineEquiv p hp
    let X : Finset (EuclideanPoint d) := Finset.univ.image p
    have hpX : ∀ i, p i ∈ X := fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hXK : (X : Set _) ⊆ K := by
      rintro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hpK i
    have hinner : normalizedInnerCube d ⊆ e '' K :=
      (normalizedInnerCube_subset_image_convexHull hpX hp).trans
        (Set.image_mono (convexHull_min hXK hconvex))
    have houter : e '' K ⊆ normalizedOuterCube d := by
      rintro y ⟨x, hx, rfl⟩
      let Y := insert x X
      have hpY : ∀ i, p i ∈ Y := fun i => Finset.mem_insert_of_mem (hpX i)
      have hYK : (Y : Set _) ⊆ K := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx
        · exact hXK hz
      exact subset_unitCube_of_maximal_simplex hpY hp
        (fun q hq => hmax q (fun i => hYK (hq i)))
        ⟨x, Finset.mem_insert_self _ _, rfl⟩
    have hbox : volume (normalizedOuterCube d) ≤ normalizedBoxConstant d * volume (e '' K) := by
      calc
        volume (normalizedOuterCube d) = normalizedBoxConstant d * volume (normalizedInnerCube d) := by
          symm
          exact ENNReal.div_mul_cancel (volume_normalizedInnerCube_ne_zero d)
            (volume_normalizedInnerCube_ne_top d)
        _ ≤ normalizedBoxConstant d * volume (e '' K) := by gcongr
    let c := affineEquivVolumeFactor e
    have hc0 : c ≠ 0 := affineEquivVolumeFactor_ne_zero e
    have hc_top : c ≠ ⊤ := affineEquivVolumeFactor_ne_top e
    have hscaled : c * volume (euclideanClosedDifferenceBody K) ≤
        c * (((2 : ENNReal) ^ d * normalizedBoxConstant d) * volume K) := by
      calc
        c * volume (euclideanClosedDifferenceBody K) =
            volume (e.linear '' euclideanClosedDifferenceBody K) := by
          simpa [c, affineEquivVolumeFactor] using
            (volume_linearEquivImage e.linear (euclideanClosedDifferenceBody K)).symm
        _ ≤ volume (normalizedDoubleCube d) := measure_mono
          (linear_image_closedDifferenceBody_subset_normalizedDoubleCube e K houter)
        _ = (2 : ENNReal) ^ d * volume (normalizedOuterCube d) := volume_normalizedDoubleCube d
        _ ≤ (2 : ENNReal) ^ d * (normalizedBoxConstant d * volume (e '' K)) := by gcongr
        _ = c * (((2 : ENNReal) ^ d * normalizedBoxConstant d) * volume K) := by
          rw [volume_affineEquivImage]
          change (2 : ENNReal) ^ d * (normalizedBoxConstant d * (c * volume K)) = _
          ac_rfl
    have hcancel := (ENNReal.mul_le_mul_iff_right hc0 hc_top).mp hscaled
    exact (measure_mono (subset_closure : K - K ⊆ euclideanClosedDifferenceBody K)).trans
      (hcancel.trans (mul_le_mul_left (normalizedConstant_le d) _))
  · let H := affineSpan ℝ K
    have hHne : (H : Set (EuclideanPoint d)).Nonempty := hne.mono (subset_affineSpan ℝ K)
    have hdir : H.direction ≠ ⊤ := fun h => hspan
      ((AffineSubspace.direction_eq_top_iff_of_nonempty hHne).mp h)
    have hsub : K - K ⊆ (H.direction : Set (EuclideanPoint d)) := by
      rw [Set.sub_subset_iff]
      intro x hx y hy
      exact AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ K hx)
        (subset_affineSpan ℝ K hy)
    have hzero : volume (K - K) = 0 := measure_mono_null hsub
      (MeasureTheory.Measure.addHaar_submodule volume H.direction hdir)
    rw [hzero]
    positivity

/-- The coarse replacement consumed by the projective argument, with the
same body interface and a positive natural dimension constant. -/
theorem rogers_shephard {d : ℕ} (K : ConvexBody (Fin d → ℝ)) :
    volume ((K + (-1 : ℝ) • K : ConvexBody (Fin d → ℝ)) : Set (Fin d → ℝ)) ≤
      (rogersConstant d : ENNReal) * volume (K : Set (Fin d → ℝ)) := by
  let e : (Fin d → ℝ) ≃L[ℝ] EuclideanPoint d :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let L := e '' (K : Set (Fin d → ℝ))
  have hLc : IsCompact L := K.isCompact'.image e.continuous
  have hLv : Convex ℝ L := K.convex'.linear_image e.toLinearMap
  have hLn : L.Nonempty := K.nonempty'.image e
  have hvol := compact_difference_volume L hLc hLv hLn
  have hpre : e ⁻¹' L = (K : Set (Fin d → ℝ)) :=
    Set.preimage_image_eq _ e.injective
  have hpreD : e ⁻¹' (L - L) = (K : Set (Fin d → ℝ)) - K := by
    ext z
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, y, ⟨v, hv, rfl⟩, h⟩
      exact ⟨u, hu, v, hv, e.injective (by simpa only [map_sub] using h)⟩
    · rintro ⟨u, hu, v, hv, rfl⟩
      exact ⟨e u, ⟨u, hu, rfl⟩, e v, ⟨v, hv, rfl⟩, (map_sub e u v).symm⟩
  have hmeasure : MeasurePreserving e := PiLp.volume_preserving_toLp (Fin d)
  have hvolL := hmeasure.measure_preimage hLc.measurableSet.nullMeasurableSet
  have hLcD : IsCompact (L - L) := by
    simpa only [sub_eq_add_neg] using hLc.add hLc.neg
  have hvolD := hmeasure.measure_preimage hLcD.measurableSet.nullMeasurableSet
  rw [hpre] at hvolL
  rw [hpreD] at hvolD
  rw [← hvolD, ← hvolL] at hvol
  simpa only [ConvexBody.coe_add, ConvexBody.coe_smul, Set.neg_smul_set, one_smul,
    sub_eq_add_neg] using hvol

end
end Erdos131Research

#print axioms Erdos131Research.rogers_shephard
