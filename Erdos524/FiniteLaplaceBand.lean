import Erdos524.FiniteLaplaceRegression

/-! Uniform finite-dimensional shell bounds on a bounded Laplace parameter interval. -/

namespace Erdos524.FiniteLaplaceBand

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal
open Erdos524.FiniteLaplaceRegression Erdos524.AffineGaussianBand
open Erdos524.GaussianBoxDensity Erdos524.LaplaceKernelComparison

variable {n : ℕ}

noncomputable def fiberSet (u : Fin (n + 1) → ℝ) (δ : ℝ) : Set (ℝ × (Fin (n + 1) → ℝ)) :=
  {p | ∀ i, |zeroCoefficient (u i) * p.1 + p.2 i| ≤ δ}

theorem measurable_fiberSet (u : Fin (n + 1) → ℝ) (δ : ℝ) : MeasurableSet (fiberSet u δ) := by
  simp only [fiberSet, Set.setOf_forall]
  exact MeasurableSet.iInter (fun i ↦ measurableSet_le (by fun_prop) measurable_const)

theorem laplace_box_fiber_integral (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 ≤ u i) (δ : ℝ) :
    (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' box (fun _ ↦ δ)) =
      ∫⁻ r, (gaussianReal 0 1) {g : ℝ | ∀ i, |zeroCoefficient (u i) * g + r i| ≤ δ}
        ∂(jointMeasure u).map (laplaceResidual u) := by
  have hmR : Measurable (laplaceResidual u) := by
    unfold laplaceResidual Erdos524.FiniteGaussianRegression.residual sample evaluation
    fun_prop
  have hmG : Measurable (base (n := n)) := by unfold base; fun_prop
  haveI := (residual_gaussian u).isGaussian_map
  have hprod := IndepFun.map_prod_eq_prod_map_map hmG.aemeasurable hmR.aemeasurable
    (base_residual_independent u hu)
  rw [base_law u hu] at hprod
  have hf := congrArg (fun μ : Measure (ℝ × (Fin (n + 1) → ℝ)) ↦ μ (fiberSet u δ)) hprod
  rw [Measure.map_apply (hmG.prodMk hmR) (measurable_fiberSet u δ),
    Measure.prod_apply_symm (measurable_fiberSet u δ)] at hf
  have he := congrArg (fun μ : Measure (Fin (n + 1) → ℝ) ↦ μ (box (fun _ ↦ δ))) (evaluation_law u hu)
  rw [Measure.map_apply (by unfold evaluation; fun_prop) (measurableSet_box _),
    Measure.map_apply (by fun_prop) (measurableSet_box _)] at he
  have hset : evaluation ⁻¹' box (fun _ ↦ δ) =
      (fun z ↦ (base z, laplaceResidual u z)) ⁻¹' fiberSet u δ := by
    ext z
    simp only [Set.mem_preimage, box, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
      fiberSet, Set.mem_setOf_eq]
    simp_rw [reconstruction u z, abs_le]
  rw [hset] at he
  exact he.symm.trans hf

theorem finite_laplace_cube_increment (u : Fin (n + 1) → ℝ)
    {T ε : ℝ} (hu : ∀ i, 0 ≤ u i) (hT : ∀ i, u i ≤ T) (hε : 0 ≤ ε) (δ : ℝ) :
    (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' box (fun _ ↦ δ + ε)) ≤
      (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' box (fun _ ↦ δ)) +
        ENNReal.ofReal (2 * ε / Real.exp (-T)) := by
  haveI := (residual_gaussian u).isGaussian_map
  rw [laplace_box_fiber_integral u hu (δ + ε), laplace_box_fiber_integral u hu δ]
  calc
    _ ≤ ∫⁻ r, ((gaussianReal 0 1) {g : ℝ | ∀ i, |zeroCoefficient (u i) * g + r i| ≤ δ} +
        ENNReal.ofReal (2 * ε / Real.exp (-T))) ∂(jointMeasure u).map (laplaceResidual u) := by
      apply lintegral_mono
      intro r
      exact affine_gaussian_cube_increment (fun i ↦ zeroCoefficient (u i)) r (Real.exp_pos _)
        (fun i ↦ zeroCoefficient_lower (hu i) (hT i)) hε δ
    _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const]; simp

end Erdos524.FiniteLaplaceBand
