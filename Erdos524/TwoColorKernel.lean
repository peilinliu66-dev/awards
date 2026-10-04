import Erdos524.OffsetStepKernel
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

namespace Erdos524.TwoColorKernel
open MeasureTheory Set
open Erdos524.LaplaceKernelComparison

noncomputable def colorMeasure : Measure (Fin 2 × ℝ) := (Measure.count : Measure (Fin 2)).prod intervalMeasure

instance : IsFiniteMeasure colorMeasure := by unfold colorMeasure; infer_instance

noncomputable def pairFunction (f g : ℝ → ℝ) (z : Fin 2 × ℝ) : ℝ := if z.1=0 then f z.2 else g z.2

theorem pairFunction_memLp {f g : ℝ → ℝ} (hf : MemLp f 2 intervalMeasure) (hg : MemLp g 2 intervalMeasure) :
    MemLp (pairFunction f g) 2 colorMeasure := by
  classical
  have h0 : MeasurableSet {z : Fin 2 × ℝ | z.1=0} := measurableSet_eq_fun measurable_fst measurable_const
  exact MemLp.piecewise h0.nullMeasurableSet
    ((hf.comp_snd (Measure.count : Measure (Fin 2))).mono_measure Measure.restrict_le_self)
    ((hg.comp_snd (Measure.count : Measure (Fin 2))).mono_measure Measure.restrict_le_self)

theorem integral_pairFunction {f g : ℝ → ℝ} (hf : MemLp f 2 intervalMeasure) (hg : MemLp g 2 intervalMeasure) :
    (∫ z, pairFunction f g z ∂colorMeasure)=(∫ s, f s ∂intervalMeasure)+(∫ s, g s ∂intervalMeasure) := by
  have hi := (pairFunction_memLp hf hg).integrable (by norm_num : (1:ENNReal)≤2)
  change (∫ z, pairFunction f g z ∂(Measure.count : Measure (Fin 2)).prod intervalMeasure)=_
  rw [integral_prod _ hi,integral_count,Fin.sum_univ_two]
  simp [pairFunction]

theorem integral_pair_product {f g h k : ℝ → ℝ}
    (hf : MemLp f 2 intervalMeasure) (hg : MemLp g 2 intervalMeasure)
    (hh : MemLp h 2 intervalMeasure) (hk : MemLp k 2 intervalMeasure) :
    (∫ z, pairFunction f g z*pairFunction h k z ∂colorMeasure)=
      (∫ s, f s*h s ∂intervalMeasure)+(∫ s, g s*k s ∂intervalMeasure) := by
  have hi : Integrable (fun z => pairFunction f g z*pairFunction h k z) colorMeasure :=
    (pairFunction_memLp hf hg).integrable_mul (pairFunction_memLp hh hk)
  change (∫ z, pairFunction f g z*pairFunction h k z ∂(Measure.count : Measure (Fin 2)).prod intervalMeasure)=_
  rw [integral_prod _ hi,integral_count,Fin.sum_univ_two]
  simp [pairFunction]

end Erdos524.TwoColorKernel
