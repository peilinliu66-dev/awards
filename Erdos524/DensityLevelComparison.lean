import Erdos524.LayercakeComparison
import Erdos524.ShiftIntersection
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
Finite Anderson comparison for densities with compact symmetric convex positive
superlevel sets. The density hypotheses are discharged for the standard
Gaussian in a separate module.
-/

namespace Erdos524.DensityLevelComparison

open Set MeasureTheory
open scoped ENNReal
open Erdos524.LayercakeComparison Erdos524.ShiftIntersection

variable {n m : ℕ}

theorem integral_linear_shift_le
    (L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin m → ℝ))
    {ρ : (Fin (n + 1) → ℝ) → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hcompact : ∀ s : ℝ, 0 < s → IsCompact {x | s ≤ ρ x})
    (hconvex : ∀ s : ℝ, 0 < s → Convex ℝ {x | s ≤ ρ x})
    (hneg : ∀ s : ℝ, 0 < s → ∀ ⦃x⦄, s ≤ ρ x → s ≤ ρ (-x))
    {K : Set (Fin m → ℝ)} (hclosedK : IsClosed K) (hconvexK : Convex ℝ K)
    (hnegK : ∀ ⦃y⦄, y ∈ K → -y ∈ K) (t : Fin m → ℝ) :
    ∫⁻ x in {x | L x + t ∈ K}, ENNReal.ofReal (ρ x) ≤
      ∫⁻ x in {x | L x ∈ K}, ENNReal.ofReal (ρ x) := by
  apply setLIntegral_le_of_superlevel_inter_le volume hρ hρ0
  intro s hs
  simpa only [linearShiftSlice, Set.inter_def, Set.mem_setOf_eq, add_zero] using
    volume_linearShiftSlice_le L (hcompact s hs) hclosedK (hconvex s hs) hconvexK
      (hneg s hs) hnegK t

theorem withDensity_linear_shift_le
    (L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin m → ℝ))
    {ρ : (Fin (n + 1) → ℝ) → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hcompact : ∀ s : ℝ, 0 < s → IsCompact {x | s ≤ ρ x})
    (hconvex : ∀ s : ℝ, 0 < s → Convex ℝ {x | s ≤ ρ x})
    (hneg : ∀ s : ℝ, 0 < s → ∀ ⦃x⦄, s ≤ ρ x → s ≤ ρ (-x))
    {K : Set (Fin m → ℝ)} (hclosedK : IsClosed K) (hconvexK : Convex ℝ K)
    (hnegK : ∀ ⦃y⦄, y ∈ K → -y ∈ K) (t : Fin m → ℝ) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (ρ x))) {x | L x + t ∈ K} ≤
      (volume.withDensity (fun x ↦ ENNReal.ofReal (ρ x))) {x | L x ∈ K} := by
  rw [withDensity_apply', withDensity_apply']
  exact integral_linear_shift_le L hρ hρ0 hcompact hconvex hneg hclosedK hconvexK hnegK t

end Erdos524.DensityLevelComparison
