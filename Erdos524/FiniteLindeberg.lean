import Erdos524.HybridReplacement
import Erdos524.LinearStatistic
import Erdos524.SingleCoordinateReplacement

namespace Erdos524.FiniteLindeberg
open MeasureTheory ProbabilityTheory
open Erdos524.ProductCoordinateReplacement Erdos524.LinearStatistic
open Erdos524.SingleCoordinateReplacement Erdos524.SignGaussianMoments
open Erdos524.SmoothedSoftMaximum Erdos524.SmoothCutoff Erdos524.SoftMaximum

theorem smoothStatistic_insert {n d : ℕ} (b η r : ℝ) (c : Fin (n+1) → Fin d → ℝ)
    (i : Fin (n+1)) (t : ℝ) (y : Fin n → ℝ) :
    smoothStatistic b η r c (insertCoordinate i t y)=
      smoothedPath b η r (linearStatistic (fun j => c (i.succAbove j)) y) (c i) t := by
  unfold smoothStatistic smoothedPath softPath
  rw [linearStatistic_insert]

theorem finite_sign_gaussian_replacement {n d : ℕ} (hd : 0<d)
    {b η C : ℝ} (hb : 1≤b) (hη : 0<η) (hC : 0≤C)
    (hcut : ∀ j : Fin 4, ∀ z : ℝ, ‖iteratedDeriv (j.val+1) cutoff z‖≤C)
    (r : ℝ) (c : Fin (n+1) → Fin d → ℝ) (a : Fin (n+1) → ℝ)
    (ha : ∀ i, 0≤a i) (hc : ∀ i j, |c i j|≤a i) :
    |(∫ z, smoothStatistic b η r c z ∂Measure.pi (fun _ : Fin (n+1) => signLaw))-
      (∫ z, smoothStatistic b η r c z ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))|≤
      ((75/6:ℝ)*C*b^3/η^4)*(∑ i, (a i)^4) := by
  have h := integral_pi_replacement (fun _ : Fin (n+1) => signLaw)
    (fun _ : Fin (n+1) => gaussianReal 0 1)
    (smoothStatistic b η r c) (smoothStatistic_continuous hd b η r c).measurable
    (smoothStatistic_norm_le_one b η r c)
    (fun i => (75/6:ℝ)*C*b^3*(a i)^4/η^4) (by
      intro i y
      simp_rw [smoothStatistic_insert]
      exact smoothedPath_sign_gaussian hd hb hη (ha i) hC hcut r _ _ (hc i))
  calc
    _ ≤ _ := h
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring

theorem exists_universal_replacement_constant : ∃ D : ℝ, 0<D ∧
    ∀ {n d : ℕ}, 0<d → ∀ {b η : ℝ}, 1≤b → 0<η →
    ∀ (r : ℝ) (c : Fin (n+1) → Fin d → ℝ) (a : Fin (n+1) → ℝ),
    (∀ i, 0≤a i) → (∀ i j, |c i j|≤a i) →
    |(∫ z, smoothStatistic b η r c z ∂Measure.pi (fun _ : Fin (n+1) => signLaw))-
      (∫ z, smoothStatistic b η r c z ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))|≤
      D*b^3/η^4*(∑ i, (a i)^4) := by
  obtain ⟨C,hC,hcut⟩ := exists_cutoff_derivative_bound
  refine ⟨(75/6:ℝ)*C,by positivity,?_⟩
  intro n d hd b η hb hη r c a ha hc
  exact finite_sign_gaussian_replacement hd hb hη (by linarith) hcut r c a ha hc

end Erdos524.FiniteLindeberg
