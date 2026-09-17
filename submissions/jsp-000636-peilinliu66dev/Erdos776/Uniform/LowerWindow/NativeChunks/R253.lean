import Erdos776.Uniform.LowerWindow.FiniteChecker

/-! One fixed native-evaluated chunk of the upstream lower-window certificate.
Uses Lean's native evaluation trust boundary, disclosed in the submission. -/
namespace Erdos776.Uniform

theorem lowerWindowNative253_certificate :
    (List.range 32).all (fun d => lowerWindowCheck (253 + d)) = true := by
  native_decide

theorem lowerWindowNative253 (r : ℕ) (hlo : 253 ≤ r) (hhi : r ≤ 284) :
    lowerWindowCheck r = true := by
  have hall := List.all_eq_true.mp lowerWindowNative253_certificate
  have hd : r - 253 ∈ List.range 32 := by
    simp only [List.mem_range]
    omega
  simpa only [show 253 + (r - 253) = r by omega] using hall (r - 253) hd

end Erdos776.Uniform
#print axioms Erdos776.Uniform.lowerWindowNative253_certificate
