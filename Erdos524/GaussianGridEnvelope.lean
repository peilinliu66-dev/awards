import Erdos524.GaussianGridProbability

namespace Erdos524.GaussianGridEnvelope
open MeasureTheory ProbabilityTheory Filter Set WithLp
open Erdos524.GaussianGridProbability Erdos524.GaussianGridOscillation Erdos524.LaplaceKernelComparison
open Erdos524.FiniteSmallBallEnvelope Erdos524.FiniteSmallBallBasic Erdos524.GramGaussianCoupling

theorem kernelProbability_eq_cube {n : ℕ} (u : Fin (n+1) → ℝ) (r : ℝ) :
    kernelProbability u r=((multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' Erdos524.GaussianBoxDensity.box (fun _ => r))).toReal := by
  unfold kernelProbability gramBoxProbability Measure.real
  congr 1
  congr 1
  ext z
  simp only [Set.mem_setOf_eq,Set.mem_preimage,Erdos524.GaussianBoxDensity.box,Set.mem_pi,Set.mem_univ,
    true_implies,Set.mem_Icc,abs_le]

theorem kernelProbability_nonneg {m : ℕ} (u : Fin m → ℝ) (r : ℝ) : 0≤kernelProbability u r := measureReal_nonneg

theorem kernelProbability_le_one {m : ℕ} (u : Fin m → ℝ) (r : ℝ) : kernelProbability u r≤1 := by
  have h := measureReal_mono (μ := multivariateGaussian 0 (finiteKernel u)) (Set.subset_univ {z : EuclideanSpace ℝ (Fin m) | ∀ i, |z i|≤r})
  simpa only [probReal_univ,kernelProbability,gramBoxProbability,finiteKernel] using h

theorem grid_probability_le_envelope (J : ℕ) {h η r : ℝ} (hh : 0<h) (hη : 0<η) (hrη : 0<r+η) :
    kernelProbability (gridPoints J h) r≤smallBallReal (r+η)+Real.sqrt (2*(Real.exp 1)^2*h)/η+
      Real.exp 1/((r+η)*Real.sqrt ((J:ℝ)*h+1)) := by
  let E := Real.sqrt (2*(Real.exp 1)^2*h)/η+Real.exp 1/((r+η)*Real.sqrt ((J:ℝ)*h+1))
  have hb : kernelProbability (gridPoints J h) r-E≤smallBallReal (r+η) := by
    apply (ENNReal.ofReal_le_iff_le_toReal (finiteSmallBall_ne_top (r+η))).mp
    change ENNReal.ofReal (kernelProbability (gridPoints J h) r-E)≤⨅ (n : ℕ) (u : Fin (n+1) → NNReal),
      (multivariateGaussian 0 (finiteKernel (fun i => (u i:ℝ)))) (ofLp ⁻¹' Erdos524.GaussianBoxDensity.box (fun _ => r+η))
    apply le_iInf
    intro n
    apply le_iInf
    intro u
    apply (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mpr
    have hx := grid_probability_le_arbitrary J hh hη hrη (fun i => (u i:ℝ)) (fun i => (u i).property)
    rw [kernelProbability_eq_cube (fun i => (u i:ℝ)) (r+η)] at hx
    dsimp only [E]
    linarith
  dsimp only [E] at hb
  linarith

theorem probability_square_budget {x y E : ℝ} (hx0 : 0≤x) (hx1 : x≤1) (hy0 : 0≤y) (hy1 : y≤1)
    (hE : 0≤E) (hxy : x≤y+E) : x^2≤y^2+2*E := by
  have hd : x-y≤E := by linarith
  have hs : x+y≤2 := by linarith
  have hp := mul_le_mul hd hs (add_nonneg hx0 hy0) hE
  nlinarith

theorem grid_probability_sq_le_envelope (J : ℕ) {h η r : ℝ} (hh : 0<h) (hη : 0<η) (hrη : 0<r+η) :
    (kernelProbability (gridPoints J h) r)^2≤(smallBallReal (r+η))^2+
      2*(Real.sqrt (2*(Real.exp 1)^2*h)/η+Real.exp 1/((r+η)*Real.sqrt ((J:ℝ)*h+1))) := by
  apply probability_square_budget (kernelProbability_nonneg _ _) (kernelProbability_le_one _ _)
    (show 0≤smallBallReal (r+η) from ENNReal.toReal_nonneg) (smallBallReal_le_one _) (by positivity)
  have h := grid_probability_le_envelope J hh hη hrη
  linarith

end Erdos524.GaussianGridEnvelope
