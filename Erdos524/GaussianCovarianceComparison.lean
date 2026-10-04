import Erdos524.FiniteAnderson
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction

/-! Covariance addition and comparison for Mathlib's actual multivariate Gaussians. -/

namespace Erdos524.GaussianCovarianceComparison

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
open Erdos524.FiniteAnderson

variable {n m : ℕ}

theorem pi_gaussian_linear_shift_le_euclidean
    (L : (Fin (n + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m))
    {K : Set (EuclideanSpace ℝ (Fin m))} (hclosed : IsClosed K) (hconvex : Convex ℝ K)
    (hneg : ∀ ⦃y⦄, y ∈ K → -y ∈ K) (t : EuclideanSpace ℝ (Fin m)) :
    (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) {x | L x + t ∈ K} ≤
      (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) {x | L x ∈ K} := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)
  let K' : Set (Fin m → ℝ) := e.symm ⁻¹' K
  have hc : IsClosed K' := hclosed.preimage e.symm.continuous
  have hv : Convex ℝ K' := hconvex.linear_preimage e.symm.toLinearMap
  have hn : ∀ ⦃y⦄, y ∈ K' → -y ∈ K' := by
    intro y hy
    change e.symm (-y) ∈ K
    rw [map_neg]
    exact hneg hy
  have h := pi_gaussian_linear_shift_le (e.toContinuousLinearMap.comp L) hc hv hn (e t)
  simpa [K', ContinuousLinearMap.comp_apply, map_add] using h

theorem multivariate_zero_eq_map_pi (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    multivariateGaussian 0 S =
      (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)).map
        (fun x ↦ toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) (toLp 2 x)) := by
  simp only [multivariateGaussian, zero_add]
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem multivariate_gaussian_shift_le
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hclosed : IsClosed K) (hconvex : Convex ℝ K)
    (hneg : ∀ ⦃y⦄, y ∈ K → -y ∈ K) (t : EuclideanSpace ℝ (Fin (n + 1))) :
    (multivariateGaussian 0 S) {x | x + t ∈ K} ≤ (multivariateGaussian 0 S) K := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) ↦ ℝ)
  let L := (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).comp e.symm.toContinuousLinearMap
  have hs : MeasurableSet {x : EuclideanSpace ℝ (Fin (n + 1)) | x + t ∈ K} :=
    hclosed.measurableSet.preimage (by fun_prop)
  rw [multivariate_zero_eq_map_pi, Measure.map_apply (by fun_prop) hs,
    Measure.map_apply (by fun_prop) hclosed.measurableSet]
  exact pi_gaussian_linear_shift_le_euclidean L hclosed hconvex hneg t

theorem multivariate_gaussian_add
    {S T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) :
    ((multivariateGaussian 0 S).prod (multivariateGaussian 0 T)).map
        (fun p ↦ p.1 + p.2) = multivariateGaussian 0 (S + T) := by
  apply Measure.ext_of_charFun
  ext x
  rw [charFun_map_add_prod_eq_mul, Pi.mul_apply,
    charFun_multivariateGaussian hS, charFun_multivariateGaussian hT,
    charFun_multivariateGaussian (hS.add hT)]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub,
    Matrix.add_mulVec, dotProduct_add]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem multivariate_gaussian_covariance_add_le
    {S T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef)
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hclosed : IsClosed K) (hconvex : Convex ℝ K)
    (hneg : ∀ ⦃y⦄, y ∈ K → -y ∈ K) :
    (multivariateGaussian 0 (S + T)) K ≤ (multivariateGaussian 0 S) K := by
  rw [← multivariate_gaussian_add hS hT,
    Measure.map_apply (by fun_prop) hclosed.measurableSet,
    Measure.prod_apply_symm (hclosed.measurableSet.preimage (by fun_prop))]
  calc
    (∫⁻ y, (multivariateGaussian 0 S) {x | x + y ∈ K} ∂(multivariateGaussian 0 T)) ≤
        ∫⁻ y, (multivariateGaussian 0 S) K ∂(multivariateGaussian 0 T) :=
      lintegral_mono fun y ↦ multivariate_gaussian_shift_le S hclosed hconvex hneg y
    _ = (multivariateGaussian 0 S) K := by simp

theorem multivariate_gaussian_covariance_mono
    {S T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hS : S.PosSemidef) (hTS : (T - S).PosSemidef)
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hclosed : IsClosed K) (hconvex : Convex ℝ K)
    (hneg : ∀ ⦃y⦄, y ∈ K → -y ∈ K) :
    (multivariateGaussian 0 T) K ≤ (multivariateGaussian 0 S) K := by
  have h := multivariate_gaussian_covariance_add_le hS hTS hclosed hconvex hneg
  have he : S + (T - S) = T := by abel
  rw [he] at h
  exact h

end Erdos524.GaussianCovarianceComparison
