import Erdos776.Uniform.LowerWindow.FiniteChecker

/-! One fixed native-evaluated chunk of the upstream lower-window certificate.
Uses Lean's native evaluation trust boundary, disclosed in the submission. -/
namespace Erdos776.Uniform

theorem lowerWindowNative189_certificate :
    (List.range 32).all (fun d => lowerWindowCheck (189 + d)) = true := by
  native_decide

theorem lowerWindowNative189 (r : ℕ) (hlo : 189 ≤ r) (hhi : r ≤ 220) :
    lowerWindowCheck r = true := by
  have hall := List.all_eq_true.mp lowerWindowNative189_certificate
  have hd : r - 189 ∈ List.range 32 := by
    simp only [List.mem_range]
    omega
  simpa only [show 189 + (r - 189) = r by omega] using hall (r - 189) hd

end Erdos776.Uniform
#print axioms Erdos776.Uniform.lowerWindowNative189_certificate
