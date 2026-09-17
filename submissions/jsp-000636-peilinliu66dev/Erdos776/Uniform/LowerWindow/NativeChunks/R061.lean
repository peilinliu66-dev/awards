import Erdos776.Uniform.LowerWindow.FiniteChecker

/-! One fixed native-evaluated chunk of the upstream lower-window certificate.
Uses Lean's native evaluation trust boundary, disclosed in the submission. -/
namespace Erdos776.Uniform

theorem lowerWindowNative061_certificate :
    (List.range 32).all (fun d => lowerWindowCheck (61 + d)) = true := by
  native_decide

theorem lowerWindowNative061 (r : ℕ) (hlo : 61 ≤ r) (hhi : r ≤ 92) :
    lowerWindowCheck r = true := by
  have hall := List.all_eq_true.mp lowerWindowNative061_certificate
  have hd : r - 61 ∈ List.range 32 := by
    simp only [List.mem_range]
    omega
  simpa only [show 61 + (r - 61) = r by omega] using hall (r - 61) hd

end Erdos776.Uniform
#print axioms Erdos776.Uniform.lowerWindowNative061_certificate
