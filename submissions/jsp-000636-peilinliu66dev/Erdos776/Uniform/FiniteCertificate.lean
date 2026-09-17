import Erdos776.Uniform.SmallUniformKernelCertificate
import Erdos776.Uniform.FiniteProfileChecker
import Erdos776.Uniform.GlobalThreshold
import Erdos776.Uniform.LowerWindow.FiniteCertificate

/-!
# Finite uniform certificate for `11 ≤ r < 29`

The Boolean certificate contains only bounded-shadow evaluations.  The
preceding soundness theorems turn its two components into actual upper-core
data and an actual full-profile obstruction.  The existing free-core and
padding constructions then supply every larger ground size.
-/

namespace Erdos776.Uniform

theorem finiteChecks_eq_true_of_ge_11_le_28
    {r : ℕ} (hr11 : 11 ≤ r) (hr28 : r ≤ 28) :
    upperCoreCheck r = true ∧ fullProfileOverflowCheck r = true := by
  have hall : ∀ d ∈ List.range 18,
      (upperCoreCheck (11 + d) && fullProfileOverflowCheck (11 + d)) = true := by
    simpa [smallUniformFiniteCheck] using
      (List.all_eq_true.mp smallUniformFiniteCheck_verified)
  let d := r - 11
  have hd : d ∈ List.range 18 := by
    simp [d]
    omega
  have h := hall d hd
  have hparts : upperCoreCheck (11 + d) = true ∧
      fullProfileOverflowCheck (11 + d) = true := by
    simpa only [Bool.and_eq_true] using h
  simpa only [d, show 11 + (r - 11) = r by omega] using hparts

/-- The finite checker supplies upper-core data throughout the small uniform range. -/
theorem hasUpperCoreData_of_ge_11_le_28
    (r : ℕ) (hr11 : 11 ≤ r) (hr28 : r ≤ 28) :
    HasUpperCoreData r := by
  exact upperCoreCheck_sound (by omega)
    (finiteChecks_eq_true_of_ge_11_le_28 hr11 hr28).1

/-- Direct recurrence overflow supplies the threshold obstruction. -/
theorem not_fullMiddleProfileExists_of_ge_11_le_28
    (r : ℕ) (hr11 : 11 ≤ r) (hr28 : r ≤ 28) :
    ¬ FullMiddleProfileExists (2 * r + 5) r := by
  exact fullProfileOverflowCheck_sound
    (finiteChecks_eq_true_of_ge_11_le_28 hr11 hr28).2

/-- The full middle-profile threshold for `11 ≤ r ≤ 28`. -/
theorem fullMiddleProfileThreshold_of_ge_11_le_28
    (r : ℕ) (hr11 : 11 ≤ r) (hr28 : r ≤ 28) :
    FullMiddleProfileThreshold r := by
  have hupper := hasUpperCoreData_of_ge_11_le_28 r hr11 hr28
  exact fullMiddleProfileThreshold_of_components
    (not_fullMiddleProfileExists_of_ge_11_le_28 r hr11 hr28)
    (hasSuitableFreeCore_of_upperCoreData r (by omega) hupper)

/-- The finite certificate and the all-`r ≥ 29` theorem meet without a gap. -/
theorem fullMiddleProfileThreshold_of_ge_11
    (r : ℕ) (hr : 11 ≤ r) :
    FullMiddleProfileThreshold r := by
  by_cases hr29 : 29 ≤ r
  · exact fullMiddleProfileThreshold_of_ge_29 r hr29
  · exact fullMiddleProfileThreshold_of_ge_11_le_28 r hr (by omega)

/-- The least global Erdős threshold for every `r ≥ 11`. -/
theorem isErdosThreshold_of_ge_11
    (r : ℕ) (hr : 11 ≤ r) :
    IsErdosThreshold r (2 * r + 5) := by
  exact isErdosThreshold_of_fullMiddleProfileThreshold (by omega)
    (fullMiddleProfileThreshold_of_ge_11 r hr)

end Erdos776.Uniform
