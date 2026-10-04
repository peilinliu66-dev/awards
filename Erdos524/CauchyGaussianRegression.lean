import Erdos524.FiniteGaussianRegression
import Erdos524.CauchyInterpolation
import Erdos524.FiniteGaussianTailBound
import Erdos524.GaussianVectorLaw

/-! Explicit regression for actual joint Cauchy Gaussian vectors. -/

namespace Erdos524.CauchyGaussianRegression

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators ProbabilityTheory
open Erdos524.CauchyKernel Erdos524.FiniteGaussianRegression

variable {n m : ℕ}

theorem posSemidef_cauchy_fintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) : (cauchy u).PosSemidef := by
  let e := (Fintype.equivFin ι).symm
  have h := posSemidef_cauchy_fin (fun i ↦ u (e i)) (fun i ↦ hu (e i))
  exact (Matrix.posSemidef_submatrix_equiv e).mp h

noncomputable def jointMeasure (x : Fin n → ℝ) (v : Fin m → ℝ) :
    Measure (EuclideanSpace ℝ (Fin n ⊕ Fin m)) :=
  multivariateGaussian 0 (cauchy (Sum.elim x v))

def sample (z : EuclideanSpace ℝ (Fin n ⊕ Fin m)) : Fin n → ℝ := fun i ↦ z (Sum.inl i)
def evaluation (z : EuclideanSpace ℝ (Fin n ⊕ Fin m)) : Fin m → ℝ := fun j ↦ z (Sum.inr j)

noncomputable def weights (x : Fin n → ℝ) (v : Fin m → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun j i ↦ regressionWeight x i (v j)

noncomputable def cauchyResidual (x : Fin n → ℝ) (v : Fin m → ℝ) :=
  residual (weights x v) (sample (n := n) (m := m)) evaluation

theorem joint_gaussian (x : Fin n → ℝ) (v : Fin m → ℝ) :
    HasGaussianLaw (fun z ↦ (sample z, evaluation z)) (jointMeasure x v) := by
  have h : HasGaussianLaw id (jointMeasure x v) := by
    unfold jointMeasure
    exact IsGaussian.hasGaussianLaw_id
  let A : EuclideanSpace ℝ (Fin n ⊕ Fin m) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi (fun i ↦ EuclideanSpace.proj (Sum.inl i))
  let B : EuclideanSpace ℝ (Fin n ⊕ Fin m) →L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearMap.pi (fun i ↦ EuclideanSpace.proj (Sum.inr i))
  change HasGaussianLaw (fun z ↦ (A.prod B) (id z)) (jointMeasure x v)
  exact h.map_fun (A.prod B)

theorem joint_covariance (x : Fin n → ℝ) (v : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hv : ∀ j, 0 < v j) (i j : Fin n ⊕ Fin m) :
    cov[fun z ↦ z i, fun z ↦ z j; jointMeasure x v] =
      1 / (Sum.elim x v i + Sum.elim x v j) := by
  have hC := posSemidef_cauchy_fintype (Sum.elim x v) (fun k ↦ by cases k <;> simp [*])
  exact covariance_eval_multivariateGaussian hC i j

theorem actual_normal_equations (x : Fin n → ℝ) (v : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (hv : ∀ j, 0 < v j)
    (i : Fin n) (j : Fin m) :
    cov[fun z ↦ sample z i, fun z ↦ evaluation z j; jointMeasure x v] =
      ∑ k, weights x v j k * cov[fun z ↦ sample z i, fun z ↦ sample z k; jointMeasure x v] := by
  simp only [sample, evaluation, weights, joint_covariance x v hx hv, Sum.elim_inl, Sum.elim_inr]
  simpa only [div_eq_mul_inv, one_mul, add_comm] using (normal_equations x hx hinj i (hv j)).symm

theorem samples_residual_independent (x : Fin n → ℝ) (v : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (hv : ∀ j, 0 < v j) :
    IndepFun (sample (n := n) (m := m)) (cauchyResidual x v) (jointMeasure x v) :=
  residual_independent (weights x v) (joint_gaussian x v)
    (actual_normal_equations x v hx hinj hv)

theorem actual_residual_covariance (x : Fin n → ℝ) (v : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (hv : ∀ j, 0 < v j)
    (j l : Fin m) :
    cov[fun z ↦ cauchyResidual x v z j, fun z ↦ cauchyResidual x v z l; jointMeasure x v] =
      blaschke x (v j) * blaschke x (v l) / (v j + v l) := by
  have h := covariance_residual (weights x v) (joint_gaussian x v)
    (actual_normal_equations x v hx hinj hv) j l
  simp only [sample, evaluation, weights, joint_covariance x v hx hv, Sum.elim_inl, Sum.elim_inr] at h
  change cov[fun z ↦ cauchyResidual x v z j, fun z ↦ cauchyResidual x v z l; jointMeasure x v] = _ at h
  rw [h]
  have he := residual_kernel x hx hinj (hv l) (hv j)
  simpa only [div_eq_mul_inv, one_mul, mul_one, add_comm, mul_comm] using he

theorem residual_gaussian (x : Fin n → ℝ) (v : Fin m → ℝ) :
    HasGaussianLaw (cauchyResidual x v) (jointMeasure x v) :=
  (joint_residual_gaussian (weights x v) (joint_gaussian x v)).snd

theorem joint_coordinate_mean (x : Fin n → ℝ) (v : Fin m → ℝ) (i : Fin n ⊕ Fin m) :
    (∫ z : EuclideanSpace ℝ (Fin n ⊕ Fin m), z i ∂jointMeasure x v) = 0 := by
  unfold jointMeasure
  have h := ContinuousLinearMap.integral_comp_id_comm
    (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin n ⊕ Fin m)) (cauchy (Sum.elim x v)))
    IsGaussian.integrable_id (EuclideanSpace.proj (𝕜 := ℝ) i)
  simpa only [EuclideanSpace.coe_proj, integral_id_multivariateGaussian, map_zero] using h

theorem residual_mean (x : Fin n → ℝ) (v : Fin m → ℝ) (j : Fin m) :
    (∫ z, cauchyResidual x v z j ∂jointMeasure x v) = 0 := by
  have hX (k : Fin n) := ((joint_gaussian x v).fst.eval k).integrable
  have hY := ((joint_gaussian x v).snd.eval j).integrable
  have hW (k : Fin n) : Integrable (fun z ↦ weights x v j k * sample z k) (jointMeasure x v) :=
    (hX k).const_mul _
  change (∫ z, evaluation z j - ∑ k, weights x v j k * sample z k ∂jointMeasure x v) = 0
  rw [integral_sub hY (integrable_finset_sum Finset.univ (fun k _ ↦ hW k)),
    integral_finsetSum Finset.univ (fun k _ ↦ hW k)]
  simp only [sample, evaluation, integral_const_mul, joint_coordinate_mean,
    mul_zero, Finset.sum_const_zero, sub_self]

theorem residual_law (x : Fin n → ℝ) (v : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (hv : ∀ j, 0 < v j) :
    (jointMeasure x v).map (cauchyResidual x v) =
      (multivariateGaussian 0 (cauchy v)).map
        (fun z ↦ fun j ↦ blaschke x (v j) * z j) := by
  have hY : HasGaussianLaw (fun z : EuclideanSpace ℝ (Fin m) ↦
      fun j ↦ blaschke x (v j) * z j) (multivariateGaussian 0 (cauchy v)) := by
    have h : HasGaussianLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (cauchy v)) :=
      IsGaussian.hasGaussianLaw_id
    let A : EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → ℝ) :=
      ContinuousLinearMap.pi (fun j ↦ blaschke x (v j) • EuclideanSpace.proj j)
    exact h.map_fun A
  apply Erdos524.GaussianVectorLaw.map_eq_of_mean_covariance (residual_gaussian x v) hY
  · unfold cauchyResidual Erdos524.FiniteGaussianRegression.residual sample evaluation
    fun_prop
  · fun_prop
  · intro j
    rw [residual_mean, integral_const_mul, Erdos524.FiniteGaussianTailBound.gaussian_coordinate_mean,
      mul_zero]
  · intro j l
    rw [actual_residual_covariance x v hx hinj hv,
      covariance_const_mul_left, covariance_const_mul_right,
      covariance_eval_multivariateGaussian (posSemidef_cauchy_fin v hv)]
    unfold cauchy
    ring

theorem sample_law (x : Fin n → ℝ) (v : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hv : ∀ j, 0 < v j) :
    (jointMeasure x v).map (sample (n := n) (m := m)) =
      (multivariateGaussian 0 (cauchy x)).map ofLp := by
  have hY : HasGaussianLaw (ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))
      (multivariateGaussian 0 (cauchy x)) := by
    have h : HasGaussianLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) (cauchy x)) :=
      IsGaussian.hasGaussianLaw_id
    exact h.map_fun (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).toContinuousLinearMap
  apply Erdos524.GaussianVectorLaw.map_eq_of_mean_covariance (joint_gaussian x v).fst hY
  · unfold sample; fun_prop
  · fun_prop
  · intro i
    exact (joint_coordinate_mean x v (Sum.inl i)).trans
      (Erdos524.FiniteGaussianTailBound.gaussian_coordinate_mean (cauchy x) i).symm
  · intro i j
    exact (joint_covariance x v hx hv (Sum.inl i) (Sum.inl j)).trans
      (covariance_eval_multivariateGaussian (posSemidef_cauchy_fin x hx) i j).symm

theorem evaluation_law (x : Fin n → ℝ) (v : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hv : ∀ j, 0 < v j) :
    (jointMeasure x v).map (evaluation (n := n) (m := m)) =
      (multivariateGaussian 0 (cauchy v)).map ofLp := by
  have hY : HasGaussianLaw (ofLp : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ))
      (multivariateGaussian 0 (cauchy v)) := by
    have h : HasGaussianLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (cauchy v)) :=
      IsGaussian.hasGaussianLaw_id
    exact h.map_fun (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)).toContinuousLinearMap
  apply Erdos524.GaussianVectorLaw.map_eq_of_mean_covariance (joint_gaussian x v).snd hY
  · unfold evaluation; fun_prop
  · fun_prop
  · intro i
    exact (joint_coordinate_mean x v (Sum.inr i)).trans
      (Erdos524.FiniteGaussianTailBound.gaussian_coordinate_mean (cauchy v) i).symm
  · intro i j
    exact (joint_covariance x v hx hv (Sum.inr i) (Sum.inr j)).trans
      (covariance_eval_multivariateGaussian (posSemidef_cauchy_fin v hv) i j).symm

theorem residual_subvector_law {k : ℕ} (x : Fin n → ℝ) (v : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (hv : ∀ j, 0 < v j)
    (f : Fin k → Fin m) :
    (jointMeasure x v).map (fun z ↦ fun i ↦ cauchyResidual x v z (f i)) =
      (jointMeasure x (fun i ↦ v (f i))).map (cauchyResidual x (fun i ↦ v (f i))) := by
  have hX : HasGaussianLaw (fun z ↦ fun i ↦ cauchyResidual x v z (f i)) (jointMeasure x v) :=
    (residual_gaussian x v).map_fun (ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj (f i)))
  apply Erdos524.GaussianVectorLaw.map_eq_of_mean_covariance hX (residual_gaussian x _)
  · unfold cauchyResidual Erdos524.FiniteGaussianRegression.residual sample evaluation
    fun_prop
  · unfold cauchyResidual Erdos524.FiniteGaussianRegression.residual sample evaluation
    fun_prop
  · intro i
    rw [residual_mean, residual_mean]
  · intro i j
    rw [actual_residual_covariance x v hx hinj hv,
      actual_residual_covariance x _ hx hinj (fun i ↦ hv (f i))]

end Erdos524.CauchyGaussianRegression
