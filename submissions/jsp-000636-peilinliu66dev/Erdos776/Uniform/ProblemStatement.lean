import Erdos776.Uniform.ThresholdTable
import Erdos776.Uniform.ProblemDefinitions

namespace Erdos776.Uniform

/-- The piecewise value is the last failing ground-set size for every `r ≥ 4`. -/
theorem erdos776_lastFailure (r : ℕ) (hr : 4 ≤ r) :
    ProblemLastFailure r (erdosThresholdFromFour r) := by
  by_cases hr10 : r ≤ 10
  · simpa [erdosThresholdFromFour, hr10] using
      problemLastFailure_of_fullMiddleProfileThresholdAt hr (by omega)
        (fullMiddleProfileThresholdAt_of_ge_4_le_10 r hr hr10)
  · have hr11 : 11 ≤ r := by omega
    have hfull := (fullMiddleProfileThreshold_iff_at r).mp
      (fullMiddleProfileThreshold_of_ge_11 r hr11)
    simpa [erdosThresholdFromFour, hr10] using
      problemLastFailure_of_fullMiddleProfileThresholdAt hr (by omega) hfull

/-- Final theorem in the published formulation: the displayed piecewise value
is the least threshold in Erdős Problem 776 for every `r ≥ 4`. -/
theorem erdos776_threshold (r : ℕ) (hr : 4 ≤ r) :
    ProblemThreshold r (erdosThresholdFromFour r) :=
  problemThreshold_of_lastFailure (erdos776_lastFailure r hr)

end Erdos776.Uniform
