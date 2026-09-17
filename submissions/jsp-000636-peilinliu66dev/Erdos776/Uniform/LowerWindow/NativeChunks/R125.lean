import Erdos776.Uniform.LowerWindow.FiniteChecker

/-! One fixed native-evaluated chunk of the upstream lower-window certificate.
Uses Lean's native evaluation trust boundary, disclosed in the submission. -/
namespace Erdos776.Uniform

theorem lowerWindowNative125_certificate :
    (List.range 32).all (fun d => lowerWindowCheck (125 + d)) = true := by
  native_decide

theorem lowerWindowNative125 (r : ℕ) (hlo : 125 ≤ r) (hhi : r ≤ 156) :
    lowerWindowCheck r = true := by
  have hall := List.all_eq_true.mp lowerWindowNative125_certificate
  have hd : r - 125 ∈ List.range 32 := by
    simp only [List.mem_range]
    omega
  simpa only [show 125 + (r - 125) = r by omega] using hall (r - 125) hd

end Erdos776.Uniform
#print axioms Erdos776.Uniform.lowerWindowNative125_certificate
