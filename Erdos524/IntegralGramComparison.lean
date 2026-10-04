import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Tactic

/-! Integral Gram matrices and covariance domination by domination of measures. -/

namespace Erdos524.IntegralGramComparison

open MeasureTheory Matrix
open scoped RealInnerProductSpace Matrix

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

noncomputable def integralGram (f : ι → Ω → ℝ) (μ : Measure Ω) : Matrix ι ι ℝ :=
  fun i j ↦ ∫ ω, f i ω * f j ω ∂μ

theorem integralGram_eq_gram (f : ι → Ω → ℝ) (μ : Measure Ω)
    (hf : ∀ i, MemLp (f i) 2 μ) :
    integralGram f μ = Matrix.gram ℝ (fun i ↦ (hf i).toLp (f i)) := by
  ext i j
  change (∫ ω, f i ω * f j ω ∂μ) =
    ⟪(hf i).toLp (f i), (hf j).toLp (f j)⟫
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hf i).coeFn_toLp, (hf j).coeFn_toLp] with ω hi hj
  simp [hi, hj, mul_comm]

theorem integralGram_posSemidef (f : ι → Ω → ℝ) (μ : Measure Ω)
    (hf : ∀ i, MemLp (f i) 2 μ) : (integralGram f μ).PosSemidef := by
  rw [integralGram_eq_gram f μ hf]
  exact Matrix.posSemidef_gram ℝ _

theorem integralGram_sub (f : ι → Ω → ℝ) {μ ν : Measure Ω} [IsFiniteMeasure μ]
    (hμν : μ ≤ ν) (hf : ∀ i, MemLp (f i) 2 ν) :
    integralGram f ν - integralGram f μ = integralGram f (ν - μ) := by
  ext i j
  have hprod : Integrable (fun ω ↦ f i ω * f j ω) ν := (hf i).integrable_mul (hf j)
  have hm := hprod.mono_measure hμν
  have hd := hprod.mono_measure (Measure.sub_le : ν - μ ≤ ν)
  have he : (∫ ω, f i ω * f j ω ∂ν) =
      (∫ ω, f i ω * f j ω ∂(ν - μ)) + (∫ ω, f i ω * f j ω ∂μ) := by
    calc
      (∫ ω, f i ω * f j ω ∂ν) =
          ∫ ω, f i ω * f j ω ∂(ν - μ + μ) := by rw [Measure.sub_add_cancel_of_le hμν]
      _ = _ := integral_add_measure hd hm
  change (∫ ω, f i ω * f j ω ∂ν) - (∫ ω, f i ω * f j ω ∂μ) =
    ∫ ω, f i ω * f j ω ∂(ν - μ)
  linarith

theorem integralGram_mono (f : ι → Ω → ℝ) {μ ν : Measure Ω} [IsFiniteMeasure μ]
    (hμν : μ ≤ ν) (hf : ∀ i, MemLp (f i) 2 ν) :
    (integralGram f ν - integralGram f μ).PosSemidef := by
  rw [integralGram_sub f hμν hf]
  exact integralGram_posSemidef f (ν - μ)
    (fun i ↦ MemLp.mono_measure Measure.sub_le (hf i))

end Erdos524.IntegralGramComparison
