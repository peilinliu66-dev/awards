import Erdos776.Uniform.LowerWindow.FiniteChecker

/-! One fixed native-evaluated chunk of the upstream lower-window certificate.
Uses Lean's native evaluation trust boundary, disclosed in the submission. -/
namespace Erdos776.Uniform

theorem lowerWindowNative157_certificate :
    (List.range 32).all (fun d => lowerWindowCheck (157 + d)) = true := by
  native_decide

theorem lowerWindowNative157 (r : ℕ) (hlo : 157 ≤ r) (hhi : r ≤ 188) :
    lowerWindowCheck r = true := by
  have hall := List.all_eq_true.mp lowerWindowNative157_certificate
  have hd : r - 157 ∈ List.range 32 := by
    simp only [List.mem_range]
    omega
  simpa only [show 157 + (r - 157) = r by omega] using hall (r - 157) hd

end Erdos776.Uniform
#print axioms Erdos776.Uniform.lowerWindowNative157_certificate
