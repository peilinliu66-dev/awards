import Erdos524.TruncatedLogTanh

namespace Erdos524.CDFDiscrepancy
open Set MeasureTheory

theorem measureReal_Ioc_eq (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a≤b) :
    μ.real (Ioc a b)=μ.real (Iic b)-μ.real (Iic a) := by
  have he : Ioc a b=Iic b \ Iic a := by ext x; simp
  rw [he]
  exact measureReal_sdiff (Iic_subset_Iic.mpr hab) measurableSet_Iic

theorem measureReal_Icc_eq (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a≤b) :
    μ.real (Icc a b)=μ.real (Iic b)-μ.real (Iic a)+μ.real {a} := by
  rw [← Ioc_union_left hab,measureReal_union,measureReal_Ioc_eq μ hab]
  · exact disjoint_singleton_right.mpr (by simp)
  · exact measurableSet_singleton _

theorem interval_discrepancy_of_cdf (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {D A : ℝ} (hD : 0≤D) (hA : 0≤A)
    (hcdf : ∀ s : ℝ, |μ.real (Iic s)-ν.real (Iic s)|≤D)
    (hatom : ∀ s : ℝ, |μ.real {s}-ν.real {s}|≤A) :
    ∀ a b : ℝ, |μ.real (Icc a b)-ν.real (Icc a b)|≤2*D+A := by
  intro a b
  by_cases hab : a≤b
  · rw [measureReal_Icc_eq μ hab,measureReal_Icc_eq ν hab,abs_le]
    have ha := abs_le.mp (hcdf a)
    have hb := abs_le.mp (hcdf b)
    have hs := abs_le.mp (hatom a)
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2,hs.1,hs.2]
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hab)]
    simp
    linarith

theorem truncated_discrepancy_of_cdf (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {D A τ : ℝ} (hD : 0≤D) (hA : 0≤A) (hτ : 0<τ)
    (hcdf : ∀ s : ℝ, |μ.real (Iic s)-ν.real (Iic s)|≤D)
    (hatom : ∀ s : ℝ, |μ.real {s}-ν.real {s}|≤A) (t : ℝ) :
    |(∫ x, Erdos524.CauchyKernel.truncatedPotential τ (x-t) ∂μ)-
      (∫ x, Erdos524.CauchyKernel.truncatedPotential τ (x-t) ∂ν)|≤
      (2*D+A)*Erdos524.CauchyKernel.logTanhPotential τ :=
  Erdos524.CauchyKernel.truncatedPotential_integral_discrepancy μ ν hτ (by positivity)
    (interval_discrepancy_of_cdf μ ν hD hA hcdf hatom) t

end Erdos524.CDFDiscrepancy
