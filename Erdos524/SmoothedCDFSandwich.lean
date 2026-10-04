import Erdos524.LinearStatistic
import Mathlib.MeasureTheory.Integral.Indicator

namespace Erdos524.SmoothedCDFSandwich
open MeasureTheory Filter Set
open Erdos524.LinearStatistic Erdos524.SoftMaximum Erdos524.SmoothCutoff

noncomputable def coordBox {N d : ℕ} (c : Fin N → Fin d → ℝ) (r : ℝ) : Set (Fin N → ℝ) :=
  {z | ∀ j, linearStatistic c z j≤r}

theorem coordBox_measurable {N d : ℕ} (c : Fin N → Fin d → ℝ) (r : ℝ) : MeasurableSet (coordBox c r) := by
  have he : coordBox c r=⋂ j : Fin d, {z | linearStatistic c z j≤r} := by ext z; simp [coordBox]
  rw [he]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le ((continuous_apply j).comp (linearStatistic_continuous c)).measurable measurable_const

theorem smoothStatistic_one {N d : ℕ} (hd : 0<d) {b η r : ℝ} (hb : 0<b)
    (hη : 0<η) (hlog : Real.log d≤b) (c : Fin N → Fin d → ℝ) (z : Fin N → ℝ)
    (hz : z∈coordBox c (r-η)) : smoothStatistic b η r c z=1 := by
  have hs := softMax_le hd (div_pos hb hη) (linearStatistic c z) (r-η) hz
  have he : Real.log d/(b/η)≤η := by
    apply (div_le_iff₀ (div_pos hb hη)).mpr
    have hid : η*(b/η)=b := by field_simp
    rwa [hid]
  apply cutoff_one
  apply div_nonpos_of_nonpos_of_nonneg _ hη.le
  linarith

theorem smoothStatistic_zero {N d : ℕ} {b η r : ℝ} (hb : 0<b)
    (hη : 0<η) (c : Fin N → Fin d → ℝ) (z : Fin N → ℝ)
    (hz : z∉coordBox c (r+η)) : smoothStatistic b η r c z=0 := by
  have hz' : ∃ j, r+η<linearStatistic c z j := by simpa [coordBox,not_forall] using hz
  obtain ⟨j,hj⟩ := hz'
  have hs := coord_le_softMax (div_pos hb hη) (linearStatistic c z) j
  apply cutoff_zero
  apply (le_div_iff₀ hη).mpr
  linarith

theorem smoothStatistic_integral_sandwich {N d : ℕ} (hd : 0<d)
    {b η r : ℝ} (hb : 0<b) (hη : 0<η) (hlog : Real.log d≤b)
    (c : Fin N → Fin d → ℝ) (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ] :
    μ.real (coordBox c (r-η))≤∫ z, smoothStatistic b η r c z ∂μ ∧
      (∫ z, smoothStatistic b η r c z ∂μ)≤μ.real (coordBox c (r+η)) := by
  have hf : Integrable (smoothStatistic b η r c) μ :=
    Integrable.of_bound (smoothStatistic_continuous hd b η r c).aestronglyMeasurable 1
      (Eventually.of_forall (smoothStatistic_norm_le_one b η r c))
  constructor
  · rw [← integral_indicator_one (coordBox_measurable c (r-η))]
    apply integral_mono_ae ((integrable_const (1:ℝ)).indicator (coordBox_measurable c (r-η))) hf
    apply Eventually.of_forall
    intro z
    by_cases hz : z∈coordBox c (r-η)
    · simp [Set.indicator_of_mem hz,smoothStatistic_one hd hb hη hlog c z hz]
    · simp only [Set.indicator_of_notMem hz]
      exact (cutoff_mem_Icc _).1
  · rw [← integral_indicator_one (coordBox_measurable c (r+η))]
    apply integral_mono_ae hf ((integrable_const (1:ℝ)).indicator (coordBox_measurable c (r+η)))
    apply Eventually.of_forall
    intro z
    by_cases hz : z∈coordBox c (r+η)
    · simp only [Set.indicator_of_mem hz,Pi.one_apply]
      exact (cutoff_mem_Icc _).2
    · simp [Set.indicator_of_notMem hz,smoothStatistic_zero hb hη c z hz]

end Erdos524.SmoothedCDFSandwich
