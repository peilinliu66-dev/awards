import Erdos524.FiniteAnderson
import Mathlib.MeasureTheory.Measure.Prod

/-! Adding independent noise to a centered finite Gaussian linear image. -/

namespace Erdos524.IndependentNoiseComparison

open Set MeasureTheory ProbabilityTheory
open Erdos524.FiniteAnderson

variable {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The added independent noise may have any probability distribution.
The product measure explicitly encodes independence. -/
theorem pi_gaussian_add_independent_noise_le
    (L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin m → ℝ))
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    {f : Ω → (Fin m → ℝ)} (hf : Measurable f)
    {K : Set (Fin m → ℝ)} (hclosedK : IsClosed K) (hconvexK : Convex ℝ K)
    (hnegK : ∀ ⦃y⦄, y ∈ K → -y ∈ K) :
    ((Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)).prod ν)
        {p | L p.1 + f p.2 ∈ K} ≤
      (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) {x | L x ∈ K} := by
  have hs : MeasurableSet {p : (Fin (n + 1) → ℝ) × Ω | L p.1 + f p.2 ∈ K} :=
    hclosedK.measurableSet.preimage
      ((L.measurable.comp measurable_fst).add (hf.comp measurable_snd))
  rw [Measure.prod_apply_symm hs]
  calc
    (∫⁻ y, (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1))
        {x | L x + f y ∈ K} ∂ν) ≤
      ∫⁻ y, (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) {x | L x ∈ K} ∂ν := by
        exact lintegral_mono fun y ↦ pi_gaussian_linear_shift_le L hclosedK hconvexK hnegK (f y)
    _ = (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) {x | L x ∈ K} := by simp

end Erdos524.IndependentNoiseComparison
