import Erdos524.TwoSidedGaussianPolynomialLaw

namespace Erdos524.PhaseGaussianComparison
open MeasureTheory ProbabilityTheory Matrix WithLp
open Erdos524.TwoSidedGaussianPolynomialLaw Erdos524.GramGaussianCoupling
open Erdos524.TwoSidedLaplaceKernels Erdos524.TwoColorKernel Erdos524.FiniteCouplingComparison

noncomputable def phaseGaussianBox (M : ℕ) {d : ℕ} (σ u : Fin d → ℝ) (r : ℝ) : ℝ :=
  (Measure.pi (fun _ : Fin (2*M) => gaussianReal 0 1)).real {z | ∀ j, |(phaseMatrix σ u*ᵥz) j|≤r}

theorem phaseGaussianBox_eq {M d : ℕ} (hM : 0<M) (σ u : Fin d → ℝ)
    (hσ : ∀ j, (σ j)^2=1) (hu : ∀ j, 0≤u j) (r : ℝ) :
    phaseGaussianBox M σ u r=gramBoxProbability (fun j => stepPair M (σ j) (u j)) colorMeasure r := by
  have hm := congrArg (fun ν : Measure (Fin d → ℝ) => ν.real (box id r)) (gaussian_phase_polynomial_law hM σ u hσ hu)
  have hb : MeasurableSet (box (id : (Fin d → ℝ) → Fin d → ℝ) r) := box_measurable id (by intro j; fun_prop) r
  simp only [Measure.real] at hm
  rw [Measure.map_apply (by fun_prop) hb,Measure.map_apply (by fun_prop) hb] at hm
  exact hm

theorem phaseGaussianBox_upper {M d : ℕ} (hM : 0<M) (σ u : Fin d → ℝ)
    (hσ : ∀ j, (σ j)^2=1) (hu : ∀ j, 0≤u j) {η : ℝ} (hη : 0<η) (r : ℝ) :
    phaseGaussianBox M σ u r≤gramBoxProbability (fun j => exactPair (σ j) (u j)) colorMeasure (r+η)+
      (∑ j, (u j)^2)/((M:ℝ)^2*η^2) := by
  rw [phaseGaussianBox_eq hM σ u hσ hu]
  have h := gram_box_probability_comparison (fun j => stepPair M (σ j) (u j)) (fun j => exactPair (σ j) (u j))
    (fun j => memLp_stepPair M (σ j) (hu j)) (fun j => memLp_exactPair (σ j) (hu j)) hη r
  apply h.trans
  apply add_le_add le_rfl
  calc
    _ ≤ (∑ j, (u j)^2/(M:ℝ)^2)/η^2 := div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun j _ => stepPair_squared_error hM (hσ j) (hu j))) (sq_nonneg η)
    _ = _ := by rw [← Finset.sum_div]; field_simp

theorem phaseGaussianBox_lower {M d : ℕ} (hM : 0<M) (σ u : Fin d → ℝ)
    (hσ : ∀ j, (σ j)^2=1) (hu : ∀ j, 0≤u j) {η : ℝ} (hη : 0<η) (r : ℝ) :
    gramBoxProbability (fun j => exactPair (σ j) (u j)) colorMeasure (r-η)-
      (∑ j, (u j)^2)/((M:ℝ)^2*η^2)≤phaseGaussianBox M σ u r := by
  rw [phaseGaussianBox_eq hM σ u hσ hu]
  have h := gram_box_probability_comparison (fun j => exactPair (σ j) (u j)) (fun j => stepPair M (σ j) (u j))
    (fun j => memLp_exactPair (σ j) (hu j)) (fun j => memLp_stepPair M (σ j) (hu j)) hη (r-η)
  have hb (j : Fin d) : (∫ z, (exactPair (σ j) (u j) z-stepPair M (σ j) (u j) z)^2 ∂colorMeasure)≤(u j)^2/(M:ℝ)^2 := by
    have he : (fun z => (exactPair (σ j) (u j) z-stepPair M (σ j) (u j) z)^2)=
        (fun z => (stepPair M (σ j) (u j) z-exactPair (σ j) (u j) z)^2) := by funext z; ring
    rw [he]
    exact stepPair_squared_error hM (hσ j) (hu j)
  have hs := div_le_div_of_nonneg_right (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j)) (sq_nonneg η)
  have he : (∑ j, (u j)^2/(M:ℝ)^2)/η^2=(∑ j, (u j)^2)/((M:ℝ)^2*η^2) := by rw [← Finset.sum_div]; field_simp
  rw [he] at hs
  have hr : r-η+η=r := by ring
  rw [hr] at h
  linarith

end Erdos524.PhaseGaussianComparison
