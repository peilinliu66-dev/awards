import Erdos776.Uniform.LowerWindow.FiniteChecker

/-! One fixed native-evaluated chunk of the upstream lower-window certificate.
Uses Lean's native evaluation trust boundary, disclosed in the submission. -/
namespace Erdos776.Uniform

theorem lowerWindowNative029_certificate :
    (List.range 32).all (fun d => lowerWindowCheck (29 + d)) = true := by
  native_decide

theorem lowerWindowNative029 (r : ℕ) (hlo : 29 ≤ r) (hhi : r ≤ 60) :
    lowerWindowCheck r = true := by
  have hall := List.all_eq_true.mp lowerWindowNative029_certificate
  have hd : r - 29 ∈ List.range 32 := by
    simp only [List.mem_range]
    omega
  simpa only [show 29 + (r - 29) = r by omega] using hall (r - 29) hd

end Erdos776.Uniform
#print axioms Erdos776.Uniform.lowerWindowNative029_certificate
