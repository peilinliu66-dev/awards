import Erdos776.Uniform.FiniteCertificate
import Erdos776.Uniform.SmallRangeCertificate

/-!
# The formalized threshold table from `r = 4` onward

The finite small-range theorem and the uniform theorem are packaged into one
piecewise least-threshold result.  The separately attributed values `r=2,3`
are not asserted here.
-/

namespace Erdos776.Uniform

/-- The threshold formula in the range covered by this formalization. -/
def erdosThresholdFromFour (r : ℕ) : ℕ :=
  if r ≤ 10 then 2 * r + 4 else 2 * r + 5

/-- The original least Erdős threshold agrees with the piecewise formula for `r ≥ 4`. -/
theorem isErdosThreshold_of_ge_4 (r : ℕ) (hr : 4 ≤ r) :
    IsErdosThreshold r (erdosThresholdFromFour r) := by
  by_cases hr10 : r ≤ 10
  · simpa [erdosThresholdFromFour, hr10] using
      isErdosThreshold_of_ge_4_le_10 r hr hr10
  · have hr11 : 11 ≤ r := by omega
    simpa [erdosThresholdFromFour, hr10] using
      isErdosThreshold_of_ge_11 r hr11

end Erdos776.Uniform
