import Erdos524.GaussianCovarianceComparison

namespace Erdos524.GaussianLinearAnderson

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped MatrixOrder Matrix.Norms.L2Operator
open Erdos524.FiniteAnderson Erdos524.GaussianCovarianceComparison

variable {n m : ℕ}

theorem multivariate_linear_shift_le (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] (Fin m → ℝ))
    {K : Set (Fin m → ℝ)} (hclosed : IsClosed K) (hconvex : Convex ℝ K)
    (hneg : ∀ ⦃y⦄, y ∈ K → -y ∈ K) (t : Fin m → ℝ) :
    (multivariateGaussian 0 S) {z | L z + t ∈ K} ≤
      (multivariateGaussian 0 S) {z | L z ∈ K} := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) ↦ ℝ)
  let A := L.comp ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).comp e.symm.toContinuousLinearMap)
  have hs1 : MeasurableSet {z : EuclideanSpace ℝ (Fin (n + 1)) | L z + t ∈ K} :=
    hclosed.measurableSet.preimage (by fun_prop)
  have hs0 : MeasurableSet {z : EuclideanSpace ℝ (Fin (n + 1)) | L z ∈ K} :=
    hclosed.measurableSet.preimage (by fun_prop)
  rw [multivariate_zero_eq_map_pi,
    Measure.map_apply (by fun_prop) hs1, Measure.map_apply (by fun_prop) hs0]
  exact pi_gaussian_linear_shift_le A hclosed hconvex hneg t

end Erdos524.GaussianLinearAnderson
