import Erdos776.Uniform.LowerWindow.FiniteChecker

/-! One fixed native-evaluated chunk of the upstream lower-window certificate.
Uses Lean's native evaluation trust boundary, disclosed in the submission. -/
namespace Erdos776.Uniform

theorem lowerWindowNative093_certificate :
    (List.range 32).all (fun d => lowerWindowCheck (93 + d)) = true := by
  native_decide

theorem lowerWindowNative093 (r : ℕ) (hlo : 93 ≤ r) (hhi : r ≤ 124) :
    lowerWindowCheck r = true := by
  have hall := List.all_eq_true.mp lowerWindowNative093_certificate
  have hd : r - 93 ∈ List.range 32 := by
    simp only [List.mem_range]
    omega
  simpa only [show 93 + (r - 93) = r by omega] using hall (r - 93) hd

end Erdos776.Uniform
#print axioms Erdos776.Uniform.lowerWindowNative093_certificate
