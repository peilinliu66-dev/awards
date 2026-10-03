/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the upstream file LICENSE.
Authors: Codex

Extracted and namespace-adapted from plby/lean-proofs at
8822f7ddef30fadbd92e1c6ab4ed897af356af5e:
PZ/OneStepAssembly.lean and PZ/FiniteHullDeterminant.lean.
Only generic normalization lemmas are retained, avoiding imports of the
unrelated one-step descent assembly. Compiled and audited adaptation; see BUILD_REPORT.json.
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.EnclosingBox
import ErdosProblems.Erdos186.PZ.ConvexDensity.LinearNormalization

open Set MeasureTheory
open scoped Pointwise BigOperators ENNReal

namespace Erdos131Research
open Erdos186.PZ.ConvexDensity

noncomputable section

def euclideanClosedDifferenceBody {d : ℕ} (K : Set (EuclideanPoint d)) :
    Set (EuclideanPoint d) := closure (K - K)


/-- The maximal-simplex comparison constant is finite. -/
theorem normalizedBoxConstant_ne_top (d : ℕ) :
    normalizedBoxConstant d ≠ ⊤ := by
  exact ENNReal.div_ne_top (volume_closedAxisBox_ne_top _ _)
    (volume_normalizedInnerCube_ne_zero d)

/-- A real version of the dimension-only constant in the difference-body
estimate.  Taking a maximum with one matches the source interface without
changing the quantitative content. -/
def finiteHullDeterminantVolumeFactor (d : ℕ) : ℝ :=
  max 1 (((2 : ℝ≥0∞) ^ d * normalizedBoxConstant d).toReal)

theorem one_le_finiteHullDeterminantVolumeFactor (d : ℕ) :
    1 ≤ finiteHullDeterminantVolumeFactor d :=
  le_max_left _ _

theorem normalizedDifferenceConstant_le_ofReal (d : ℕ) :
    (2 : ℝ≥0∞) ^ d * normalizedBoxConstant d ≤
      ENNReal.ofReal (finiteHullDeterminantVolumeFactor d) := by
  have htop : (2 : ℝ≥0∞) ^ d * normalizedBoxConstant d ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (normalizedBoxConstant_ne_top d)
  rw [← ENNReal.ofReal_toReal htop]
  exact ENNReal.ofReal_mono (le_max_right _ _)

/-- The fixed doubled cube which contains the normalized difference body. -/
def normalizedDoubleCube (d : ℕ) :
    Set (Erdos186.PZ.ConvexDensity.EuclideanPoint d) :=
  Erdos186.PZ.ConvexDensity.closedAxisBox (fun _ ↦ -2) (fun _ ↦ 2)

theorem isClosed_normalizedDoubleCube (d : ℕ) :
    IsClosed (normalizedDoubleCube d) :=
  Erdos186.PZ.ConvexDensity.isClosed_closedAxisBox _ _

/-- If an affine normalization sends `L` into `[-1,1]^d`, its linear part
sends the closed difference body into `[-2,2]^d`. -/
theorem linear_image_closedDifferenceBody_subset_normalizedDoubleCube
    {d : ℕ} (e : Erdos186.PZ.ConvexDensity.EuclideanPoint d ≃ᵃ[ℝ]
      Erdos186.PZ.ConvexDensity.EuclideanPoint d)
    (L : Set (Erdos186.PZ.ConvexDensity.EuclideanPoint d))
    (houter : e '' L ⊆ Erdos186.PZ.ConvexDensity.normalizedOuterCube d) :
    e.linear '' euclideanClosedDifferenceBody L ⊆ normalizedDoubleCube d := by
  rw [euclideanClosedDifferenceBody]
  change (fun x ↦ e.linear.toContinuousLinearEquiv.toHomeomorph x) ''
      closure (L - L) ⊆ normalizedDoubleCube d
  rw [e.linear.toContinuousLinearEquiv.toHomeomorph.image_closure]
  apply (isClosed_normalizedDoubleCube d).closure_subset_iff.mpr
  rintro w ⟨v, hv, rfl⟩
  rw [Set.mem_sub] at hv
  obtain ⟨x, hx, y, hy, rfl⟩ := hv
  have hex := houter ⟨x, hx, rfl⟩
  have hey := houter ⟨y, hy, rfl⟩
  change e.linear (x - y) ∈ normalizedDoubleCube d
  rw [show e.linear (x - y) = e x - e y by
    exact AffineMap.linearMap_vsub e.toAffineMap x y]
  intro i
  constructor
  · have hxcoord := hex i
    have hycoord := hey i
    dsimp [Erdos186.PZ.ConvexDensity.normalizedOuterCube,
      Erdos186.PZ.ConvexDensity.closedAxisBox] at hxcoord hycoord
    dsimp [normalizedDoubleCube, Erdos186.PZ.ConvexDensity.closedAxisBox]
    linarith
  · have hxcoord := hex i
    have hycoord := hey i
    dsimp [Erdos186.PZ.ConvexDensity.normalizedOuterCube,
      Erdos186.PZ.ConvexDensity.closedAxisBox] at hxcoord hycoord
    dsimp [normalizedDoubleCube, Erdos186.PZ.ConvexDensity.closedAxisBox]
    linarith

/-- The doubled normalized cube has `2^d` times the volume of the outer
normalization cube. -/
theorem volume_normalizedDoubleCube (d : ℕ) :
    (MeasureTheory.volume : MeasureTheory.Measure
        (Erdos186.PZ.ConvexDensity.EuclideanPoint d)) (normalizedDoubleCube d) =
      (2 : ℝ≥0∞) ^ d *
        (MeasureTheory.volume : MeasureTheory.Measure
          (Erdos186.PZ.ConvexDensity.EuclideanPoint d))
            (Erdos186.PZ.ConvexDensity.normalizedOuterCube d) := by
  rw [normalizedDoubleCube, Erdos186.PZ.ConvexDensity.volume_closedAxisBox,
    Erdos186.PZ.ConvexDensity.volume_normalizedOuterCube]
  norm_num [← mul_pow]

end
end Erdos131Research
