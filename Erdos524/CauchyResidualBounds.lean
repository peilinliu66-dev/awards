import Erdos524.CauchyGaussianRegression
import Erdos524.GaussianDiagonalScaling
import Erdos524.FiniteGaussianCoreBound
import Erdos524.UnorderedGaussianBounds

/-! Uniform finite core/tail bounds for the exact Gaussian interpolation residual. -/

namespace Erdos524.CauchyResidualBounds

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators
open Erdos524.CauchyKernel Erdos524.CauchyGaussianRegression
open Erdos524.FiniteGaussianTailBound Erdos524.FiniteGaussianCoreBound
open Erdos524.GaussianDiagonalScaling

variable {n m : ℕ}

theorem norm_coordinate_mul_le (d z : Fin m → ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hd : ∀ i, |d i| ≤ b) : ‖fun i ↦ d i * z i‖ ≤ b * ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hb (norm_nonneg z))).mpr
  intro i
  rw [norm_mul, Real.norm_eq_abs (d i)]
  exact mul_le_mul (hd i) (norm_le_pi_norm z i) (norm_nonneg _) hb

theorem integral_coordinate_mul_le (S : Matrix (Fin m) (Fin m) ℝ)
    (d : Fin m → ℝ) {b : ℝ} (hb : 0 ≤ b) (hd : ∀ i, |d i| ≤ b) :
    (∫ z : EuclideanSpace ℝ (Fin m), ‖fun i ↦ d i * z i‖ ∂multivariateGaussian 0 S) ≤
      b * ∫ z : EuclideanSpace ℝ (Fin m), ‖ofLp z‖ ∂multivariateGaussian 0 S := by
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearMap.pi (fun i ↦ d i • EuclideanSpace.proj i)
  let B := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)).toContinuousLinearMap
  have hA := (A.integrable_comp (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S)
    IsGaussian.integrable_id).norm
  have hB := (B.integrable_comp (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S)
    IsGaussian.integrable_id).norm.const_mul b
  rw [← integral_const_mul]
  exact integral_mono hA hB (fun z ↦ norm_coordinate_mul_le d (ofLp z) hb hd)

theorem integral_residual_tail_le (x : Fin n → ℝ) (v : Fin (m + 1) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (hv : ∀ j, 0 < v j)
    (hmono : ∀ j : Fin m, v j.castSucc ≤ v j.succ)
    {b : ℝ} (hb : 0 ≤ b) (hB : ∀ j, |blaschke x (v j)| ≤ b) :
    (∫ z, ‖cauchyResidual x v z‖ ∂jointMeasure x v) ≤ b / Real.sqrt (v 0) := by
  have he : (∫ z, ‖cauchyResidual x v z‖ ∂jointMeasure x v) =
      ∫ z : EuclideanSpace ℝ (Fin (m + 1)),
        ‖fun j ↦ blaschke x (v j) * z j‖ ∂multivariateGaussian 0 (cauchy v) := by
    rw [← integral_map (residual_gaussian x v).aemeasurable (by fun_prop),
      residual_law x v hx hinj hv, integral_map (by fun_prop) (by fun_prop)]
  rw [he]
  calc
    _ ≤ b * ∫ z : EuclideanSpace ℝ (Fin (m + 1)), ‖ofLp z‖ ∂multivariateGaussian 0 (cauchy v) :=
      integral_coordinate_mul_le _ _ hb hB
    _ ≤ b * (1 / Real.sqrt (v 0)) :=
      mul_le_mul_of_nonneg_left (integral_cauchy_sup_norm_le v hv hmono) hb
    _ = _ := by ring

theorem normalized_residual_law (x : Fin n → ℝ) (v : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (hv : ∀ j, 0 < v j) :
    (jointMeasure x v).map (fun z ↦ fun j ↦ Real.sqrt (v j) * cauchyResidual x v z j) =
      (multivariateGaussian 0 (normalized v)).map
        (fun z ↦ fun j ↦ blaschke x (v j) * z j) := by
  let f : (Fin m → ℝ) → (Fin m → ℝ) := fun z j ↦ Real.sqrt (v j) * z j
  let g : (Fin m → ℝ) → (Fin m → ℝ) := fun z j ↦ blaschke x (v j) * z j
  have h := congrArg (fun μ : Measure (Fin m → ℝ) ↦ μ.map f) (residual_law x v hx hinj hv)
  have hG := congrArg (fun μ : Measure (Fin m → ℝ) ↦ μ.map g)
    (diagonal_gaussian_map (posSemidef_cauchy_fin v hv) (fun j ↦ Real.sqrt (v j)))
  have hmeas : Measurable (cauchyResidual x v) := by
    unfold cauchyResidual Erdos524.FiniteGaussianRegression.residual sample evaluation
    fun_prop
  rw [Measure.map_map (by fun_prop) hmeas,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at hG
  rw [← normalized_eq_diagonal] at hG
  exact h.trans (by convert hG using 1 <;> congr 1 <;> funext z j <;> simp only [f, g, Function.comp_apply] <;> ring)

theorem integral_normalized_residual_core_le (x : Fin n → ℝ)
    (t : Fin (m + 1) → ℝ) (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (hmono : ∀ j : Fin m, t j.castSucc ≤ t j.succ)
    {b : ℝ} (hb : 0 ≤ b) (hB : ∀ j, |blaschke x (Real.exp (t j))| ≤ b) :
    (∫ z, ‖fun j ↦ Real.sqrt (Real.exp (t j)) *
      cauchyResidual x (fun i ↦ Real.exp (t i)) z j‖
      ∂jointMeasure x (fun i ↦ Real.exp (t i))) ≤
        b * (1 + (t (Fin.last m) - t 0) / Real.sqrt 8) := by
  let v := fun i ↦ Real.exp (t i)
  have hm : Measurable (fun z ↦ fun j ↦ Real.sqrt (v j) * cauchyResidual x v z j) := by
    unfold cauchyResidual Erdos524.FiniteGaussianRegression.residual sample evaluation
    fun_prop
  have he : (∫ z, ‖fun j ↦ Real.sqrt (v j) * cauchyResidual x v z j‖ ∂jointMeasure x v) =
      ∫ z : EuclideanSpace ℝ (Fin (m + 1)),
        ‖fun j ↦ blaschke x (v j) * z j‖ ∂multivariateGaussian 0 (normalized v) := by
    rw [← integral_map hm.aemeasurable (by fun_prop),
      normalized_residual_law x v hx hinj (fun i ↦ Real.exp_pos _),
      integral_map (by fun_prop) (by fun_prop)]
  change (∫ z, ‖fun j ↦ Real.sqrt (v j) * cauchyResidual x v z j‖ ∂jointMeasure x v) ≤ _
  rw [he]
  exact (integral_coordinate_mul_le _ _ hb hB).trans
    (mul_le_mul_of_nonneg_left (integral_stationary_sup_norm_le t hmono) hb)

theorem residual_normalized_representation (x : Fin n → ℝ) (v : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (hv : ∀ j, 0 < v j) :
    (jointMeasure x v).map (cauchyResidual x v) =
      (multivariateGaussian 0 (normalized v)).map
        (fun z ↦ fun j ↦ (blaschke x (v j) / Real.sqrt (v j)) * z j) := by
  let g : (Fin m → ℝ) → (Fin m → ℝ) :=
    fun z j ↦ (blaschke x (v j) / Real.sqrt (v j)) * z j
  have h := congrArg (fun μ : Measure (Fin m → ℝ) ↦ μ.map g)
    (diagonal_gaussian_map (posSemidef_cauchy_fin v hv) (fun j ↦ Real.sqrt (v j)))
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop), ← normalized_eq_diagonal] at h
  have he : (g ∘ (fun z : EuclideanSpace ℝ (Fin m) ↦ fun j ↦ Real.sqrt (v j) * z j)) =
      fun z ↦ fun j ↦ blaschke x (v j) * z j := by
    funext z j
    dsimp [g]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hv j))]
  rw [he] at h
  exact (residual_law x v hx hinj hv).trans h

theorem integral_residual_core_le (x : Fin n → ℝ) (t : Fin (m + 1) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (hmono : ∀ j : Fin m, t j.castSucc ≤ t j.succ)
    {b : ℝ} (hb : 0 ≤ b)
    (hB : ∀ j, |blaschke x (Real.exp (t j))| ≤ b * Real.sqrt (Real.exp (t j))) :
    (∫ z, ‖cauchyResidual x (fun i ↦ Real.exp (t i)) z‖
      ∂jointMeasure x (fun i ↦ Real.exp (t i))) ≤
        b * (1 + (t (Fin.last m) - t 0) / Real.sqrt 8) := by
  let v := fun i ↦ Real.exp (t i)
  have he : (∫ z, ‖cauchyResidual x v z‖ ∂jointMeasure x v) =
      ∫ z : EuclideanSpace ℝ (Fin (m + 1)),
        ‖fun j ↦ (blaschke x (v j) / Real.sqrt (v j)) * z j‖
          ∂multivariateGaussian 0 (normalized v) := by
    rw [← integral_map (residual_gaussian x v).aemeasurable (by fun_prop),
      residual_normalized_representation x v hx hinj (fun i ↦ Real.exp_pos _),
      integral_map (by fun_prop) (by fun_prop)]
  change (∫ z, ‖cauchyResidual x v z‖ ∂jointMeasure x v) ≤ _
  rw [he]
  have hd (j : Fin (m + 1)) : |blaschke x (v j) / Real.sqrt (v j)| ≤ b := by
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_iff₀ (Real.sqrt_pos.mpr (Real.exp_pos _))).mpr (hB j)
  exact (integral_coordinate_mul_le _ _ hb hd).trans
    (mul_le_mul_of_nonneg_left (integral_stationary_sup_norm_le t hmono) hb)

theorem integral_residual_tail_unordered_le (x : Fin n → ℝ) (v : Fin (m + 1) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    {V b : ℝ} (hV : 0 < V) (hv : ∀ j, V ≤ v j)
    (hb : 0 ≤ b) (hB : ∀ j, |blaschke x (v j)| ≤ b) :
    (∫ z, ‖cauchyResidual x v z‖ ∂jointMeasure x v) ≤ b / Real.sqrt V := by
  have he : (∫ z, ‖cauchyResidual x v z‖ ∂jointMeasure x v) =
      ∫ z : EuclideanSpace ℝ (Fin (m + 1)),
        ‖fun j ↦ blaschke x (v j) * z j‖ ∂multivariateGaussian 0 (cauchy v) := by
    rw [← integral_map (residual_gaussian x v).aemeasurable (by fun_prop),
      residual_law x v hx hinj (fun j ↦ hV.trans_le (hv j)),
      integral_map (by fun_prop) (by fun_prop)]
  rw [he]
  have h := (integral_coordinate_mul_le _ _ hb hB).trans
    (mul_le_mul_of_nonneg_left
      (Erdos524.UnorderedGaussianBounds.integral_cauchy_sup_norm_unordered_le v hV hv) hb)
  simpa only [div_eq_mul_inv, one_mul] using h

theorem integral_residual_core_unordered_le (x : Fin n → ℝ) (t : Fin (m + 1) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    {a c b : ℝ} (hlo : ∀ j, a ≤ t j) (hhi : ∀ j, t j ≤ c)
    (hb : 0 ≤ b)
    (hB : ∀ j, |blaschke x (Real.exp (t j))| ≤ b * Real.sqrt (Real.exp (t j))) :
    (∫ z, ‖cauchyResidual x (fun i ↦ Real.exp (t i)) z‖
      ∂jointMeasure x (fun i ↦ Real.exp (t i))) ≤ b * (1 + (c - a) / Real.sqrt 8) := by
  let v := fun i ↦ Real.exp (t i)
  have he : (∫ z, ‖cauchyResidual x v z‖ ∂jointMeasure x v) =
      ∫ z : EuclideanSpace ℝ (Fin (m + 1)),
        ‖fun j ↦ (blaschke x (v j) / Real.sqrt (v j)) * z j‖
          ∂multivariateGaussian 0 (normalized v) := by
    rw [← integral_map (residual_gaussian x v).aemeasurable (by fun_prop),
      residual_normalized_representation x v hx hinj (fun i ↦ Real.exp_pos _),
      integral_map (by fun_prop) (by fun_prop)]
  change (∫ z, ‖cauchyResidual x v z‖ ∂jointMeasure x v) ≤ _
  rw [he]
  have hd (j : Fin (m + 1)) : |blaschke x (v j) / Real.sqrt (v j)| ≤ b := by
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_iff₀ (Real.sqrt_pos.mpr (Real.exp_pos _))).mpr (hB j)
  exact (integral_coordinate_mul_le _ _ hb hd).trans
    (mul_le_mul_of_nonneg_left
      (Erdos524.UnorderedGaussianBounds.integral_stationary_sup_norm_unordered_le t hlo hhi) hb)

end Erdos524.CauchyResidualBounds
