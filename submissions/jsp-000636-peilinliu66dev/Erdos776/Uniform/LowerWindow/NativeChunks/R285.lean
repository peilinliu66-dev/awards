import Erdos776.Uniform.LowerWindow.FiniteChecker

/-! One fixed native-evaluated chunk of the upstream lower-window certificate.
Uses Lean's native evaluation trust boundary, disclosed in the submission. -/
namespace Erdos776.Uniform

theorem lowerWindowNative285_certificate :
    (List.range 32).all (fun d => lowerWindowCheck (285 + d)) = true := by
  native_decide

theorem lowerWindowNative285 (r : ℕ) (hlo : 285 ≤ r) (hhi : r ≤ 316) :
    lowerWindowCheck r = true := by
  have hall := List.all_eq_true.mp lowerWindowNative285_certificate
  have hd : r - 285 ∈ List.range 32 := by
    simp only [List.mem_range]
    omega
  simpa only [show 285 + (r - 285) = r by omega] using hall (r - 285) hd

end Erdos776.Uniform
#print axioms Erdos776.Uniform.lowerWindowNative285_certificate
