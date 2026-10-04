import Erdos524.UpperEnvelopeLower
import Erdos524.LogarithmicLiminf

/-! Transfer from the canonical product law to any measurable independent Rademacher sequence. -/
namespace Erdos524.ArbitrarySignModel
open MeasureTheory ProbabilityTheory Filter
open Erdos524.RandomPolynomialModel Erdos524.SignGaussianMoments

variable {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'} [IsProbabilityMeasure μ]
variable (ε : ℕ → Ω' → ℝ) (hm : ∀ i, Measurable (ε i))
  (hi : iIndepFun ε μ) (hl : ∀ i, μ.map (ε i)=signLaw)

include hm hi hl
theorem sequence_law : μ.map (fun ω i => ε i ω)=P := by
  have h := hi.map_fun_eq_infinitePi_map hm
  simpa only [hl,P] using h

theorem ae_upper_envelope :
    ∀ᵐ ω ∂μ, limsup (fun N => fullNorm (fun i => ε i ω) N /
      Real.sqrt (2*(N:ℝ)*Real.log (Real.log (N:ℝ)))) atTop=1 := by
  have h := Erdos524.UpperEnvelopeLower.ae_upper_normalized_limsup_eq_one
  rw [← sequence_law ε hm hi hl] at h
  exact ae_of_ae_map (Measurable.of_eval hm).aemeasurable h

theorem ae_logarithmic_envelope :
    ∀ᵐ ω ∂μ, liminf (fun N => Real.log (fullNorm (fun i => ε i ω) N/Real.sqrt (N:ℝ)) /
      (Real.log (Real.log (N:ℝ)))^(1/3:ℝ)) atTop=-(3*Real.pi^2/4)^(1/3:ℝ) := by
  have h := Erdos524.LogarithmicLiminf.ae_logarithmic_liminf
  rw [← sequence_law ε hm hi hl] at h
  exact ae_of_ae_map (Measurable.of_eval hm).aemeasurable h

end Erdos524.ArbitrarySignModel
