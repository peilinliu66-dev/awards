import Erdos776.Uniform.LowerWindow.FiniteChecker

/-! One fixed native-evaluated chunk of the upstream lower-window certificate.
Uses Lean's native evaluation trust boundary, disclosed in the submission. -/
namespace Erdos776.Uniform

theorem lowerWindowNative221_certificate :
    (List.range 32).all (fun d => lowerWindowCheck (221 + d)) = true := by
  native_decide

theorem lowerWindowNative221 (r : ℕ) (hlo : 221 ≤ r) (hhi : r ≤ 252) :
    lowerWindowCheck r = true := by
  have hall := List.all_eq_true.mp lowerWindowNative221_certificate
  have hd : r - 221 ∈ List.range 32 := by
    simp only [List.mem_range]
    omega
  simpa only [show 221 + (r - 221) = r by omega] using hall (r - 221) hd

end Erdos776.Uniform
#print axioms Erdos776.Uniform.lowerWindowNative221_certificate
