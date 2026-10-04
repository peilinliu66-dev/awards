import Erdos524.DensityLevelComparison
import Erdos524.GaussianProductDensity

/-!
Finite Anderson translation inequality for linear images of independent
standard Gaussians, including singular linear maps. This classical comparison
is proved from the preceding geometric and layer-cake modules.
-/

namespace Erdos524.FiniteAnderson

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open Erdos524.DensityLevelComparison Erdos524.GaussianProductDensity
open Erdos524.GaussianLevelSets

variable {n m : ℕ}

theorem pi_gaussian_linear_shift_le
    (L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin m → ℝ))
    {K : Set (Fin m → ℝ)} (hclosedK : IsClosed K) (hconvexK : Convex ℝ K)
    (hnegK : ∀ ⦃y⦄, y ∈ K → -y ∈ K) (t : Fin m → ℝ) :
    (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) {x | L x + t ∈ K} ≤
      (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) {x | L x ∈ K} := by
  have h := withDensity_linear_shift_le L measurable_rho rho_nonneg
    (fun s hs ↦ isCompact_superlevel hs) (fun s hs ↦ convex_superlevel hs)
    (fun s hs x hx ↦ neg_mem_superlevel hx) hclosedK hconvexK hnegK t
  simp_rw [pi_gaussian_eq_smul_radial]
  exact mul_le_mul_right h _

end Erdos524.FiniteAnderson
