import Erdos524.GaussianPolynomialLaw

namespace Erdos524.GaussianPolynomialComparison
open MeasureTheory ProbabilityTheory WithLp
open Erdos524.GaussianPolynomialLaw Erdos524.PolynomialLaplaceGrid
open Erdos524.LaplaceStepKernel Erdos524.LaplaceKernelComparison Erdos524.GramGaussianCoupling
open Erdos524.FiniteCouplingComparison

noncomputable def gaussianPolynomialBox (N : ℕ) {d : ℕ} (u : Fin d → ℝ) (r : ℝ) : ℝ :=
  (Measure.pi (fun _ : Fin N => gaussianReal 0 1)).real {z | ∀ j, |normalizedLaplace N z (u j)|≤r}

theorem gaussianPolynomialBox_eq {N d : ℕ} (hN : 0<N) (u : Fin d → ℝ) (r : ℝ) :
    gaussianPolynomialBox N u r=gramBoxProbability (fun j => stepLaplace N (u j)) intervalMeasure r := by
  have hm := congrArg (fun ν : Measure (Fin d → ℝ) => ν.real (box id r)) (gaussian_normalizedLaplace_law hN u)
  have hb : MeasurableSet (box (id : (Fin d → ℝ) → Fin d → ℝ) r) := box_measurable id (by intro j; fun_prop) r
  simp only [Measure.real] at hm
  rw [Measure.map_apply (by unfold normalizedLaplace; fun_prop) hb,Measure.map_apply (by fun_prop) hb] at hm
  exact hm

theorem gaussianPolynomialBox_upper {N d : ℕ} (hN : 0<N) (u : Fin d → ℝ)
    (hu : ∀ j, 0≤u j) {η : ℝ} (hη : 0<η) (r : ℝ) :
    gaussianPolynomialBox N u r≤gramBoxProbability (fun j => laplace (u j)) intervalMeasure (r+η)+
      (∑ j, (u j)^2)/((N:ℝ)^2*η^2) := by
  rw [gaussianPolynomialBox_eq hN]
  exact step_gaussian_probability_comparison hN u hu hη r

theorem gaussianPolynomialBox_lower {N d : ℕ} (hN : 0<N) (u : Fin d → ℝ)
    (hu : ∀ j, 0≤u j) {η : ℝ} (hη : 0<η) (r : ℝ) :
    gramBoxProbability (fun j => laplace (u j)) intervalMeasure (r-η)-
      (∑ j, (u j)^2)/((N:ℝ)^2*η^2)≤gaussianPolynomialBox N u r := by
  rw [gaussianPolynomialBox_eq hN]
  have h := gram_box_probability_comparison (fun j => laplace (u j)) (fun j => stepLaplace N (u j))
    (fun j => memLp_laplace_interval (hu j)) (fun j => memLp_stepLaplace N (hu j)) hη (r-η)
  have hb (j : Fin d) : (∫ s, (laplace (u j) s-stepLaplace N (u j) s)^2 ∂intervalMeasure)≤(u j)^2/(N:ℝ)^2 := by
    have he : (fun s => (laplace (u j) s-stepLaplace N (u j) s)^2)=
        (fun s => (stepLaplace N (u j) s-laplace (u j) s)^2) := by funext s; ring
    rw [he]
    exact stepLaplace_squared_error hN (hu j)
  have hs := div_le_div_of_nonneg_right (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j)) (sq_nonneg η)
  have he : (∑ j, (u j)^2/(N:ℝ)^2)/η^2=(∑ j, (u j)^2)/((N:ℝ)^2*η^2) := by rw [← Finset.sum_div]; field_simp
  rw [he] at hs
  have hr : r-η+η=r := by ring
  rw [hr] at h
  linarith

end Erdos524.GaussianPolynomialComparison
