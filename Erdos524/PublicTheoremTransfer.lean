import Erdos524.Main
import Erdos524.ArbitrarySignModel

/-! The public original endpoints on any probability space carrying measurable independent signs. -/

namespace Erdos524

open Filter MeasureTheory ProbabilityTheory
open Erdos524.SignGaussianMoments

variable {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'} [IsProbabilityMeasure μ]

theorem erdos_524_of_independent_signs (ε : ℕ → Ω' → ℝ)
    (hm : ∀ i, Measurable (ε i)) (hi : iIndepFun ε μ) (hl : ∀ i, μ.map (ε i) = signLaw) :
    ∀ᵐ ω ∂μ,
      (liminf (fun N : ℕ ↦ Real.log (littlewoodMaximum (fun i ↦ ε i ω) N / Real.sqrt (N : ℝ)) /
        (Real.log (Real.log (N : ℝ))) ^ (1 / 3 : ℝ)) atTop = -(3 * Real.pi ^ 2 / 4) ^ (1 / 3 : ℝ)) ∧
      (limsup (fun N : ℕ ↦ littlewoodMaximum (fun i ↦ ε i ω) N /
        Real.sqrt ((N : ℝ) * Real.log (Real.log (N : ℝ)))) atTop = Real.sqrt 2) := by
  have h := erdos_524
  rw [← ArbitrarySignModel.sequence_law ε hm hi hl] at h
  exact ae_of_ae_map (Measurable.of_eval hm).aemeasurable h

theorem erdos_524_inverse_of_independent_signs (ε : ℕ → Ω' → ℝ)
    (hm : ∀ i, Measurable (ε i)) (hi : iIndepFun ε μ) (hl : ∀ i, μ.map (ε i) = signLaw) :
    ∀ᵐ ω ∂μ,
      liminf (fun N : ℕ ↦ littlewoodMaximum (fun i ↦ ε i ω) N /
        (Real.sqrt (N : ℝ) * FiniteSmallBallInverse.smallBallInverse ((Real.sqrt (Real.log (N : ℝ)))⁻¹))) atTop = 1 := by
  have h := erdos_524_inverse_refinement
  rw [← ArbitrarySignModel.sequence_law ε hm hi hl] at h
  exact ae_of_ae_map (Measurable.of_eval hm).aemeasurable h

end Erdos524
