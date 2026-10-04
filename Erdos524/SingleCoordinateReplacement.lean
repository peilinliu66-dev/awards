import Erdos524.SmoothedSoftMaximum
import Erdos524.SignGaussianMoments

namespace Erdos524.SingleCoordinateReplacement
open MeasureTheory ProbabilityTheory Filter
open Erdos524.SmoothCutoff Erdos524.SmoothedSoftMaximum
open Erdos524.SignGaussianMoments Erdos524.MatchedMomentComparison

 theorem smoothedPath_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0<n) (b η r : ℝ) (x v : Fin n → ℝ) :
    Integrable (smoothedPath b η r x v) μ := by
  apply Integrable.of_bound ((smoothedPath_contDiff hn b η r x v 0).continuous.aestronglyMeasurable) 1
  apply Eventually.of_forall
  intro t
  have h := smoothedPath_mem_Icc b η r x v t
  rw [Real.norm_eq_abs,abs_of_nonneg h.1]
  exact h.2

theorem smoothedPath_sign_gaussian {n : ℕ} (hn : 0<n) {b η a C : ℝ}
    (hb : 1≤b) (hη : 0<η) (ha : 0≤a) (hC : 0≤C)
    (hcut : ∀ j : Fin 4, ∀ z : ℝ, ‖iteratedDeriv (j.val+1) cutoff z‖≤C)
    (r : ℝ) (x v : Fin n → ℝ) (hv : ∀ i, |v i|≤a) :
    |(∫ t, smoothedPath b η r x v t ∂signLaw)-
      (∫ t, smoothedPath b η r x v t ∂gaussianReal 0 1)|≤
      (75/6:ℝ)*C*b^3*a^4/η^4 := by
  have hm : ∀ t : ℝ, |iteratedDeriv 4 (smoothedPath b η r x v) t|≤75*C*b^3*a^4/η^4 :=
    fourth_derivative_bound hn hb hη ha hC hcut r x v hv
  have h := integral_compare_three_moments signLaw (gaussianReal 0 1)
    (smoothedPath_contDiff hn b η r x v 4)
    (smoothedPath_integrable signLaw hn b η r x v)
    (smoothedPath_integrable (gaussianReal 0 1) hn b η r x v)
    (fun k _ => integrable_signLaw (fun t : ℝ => t^k))
    (fun k _ => integrable_gaussian_pow k) sign_gaussian_first_three hm
  have hs : (∫ t : ℝ, t^4 ∂signLaw)=1 := by rw [integral_signLaw]; norm_num
  rw [hs,gaussian_moment_four] at h
  calc
    _ ≤ _ := h
    _ = _ := by ring

end Erdos524.SingleCoordinateReplacement
