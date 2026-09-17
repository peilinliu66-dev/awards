import Erdos776.Uniform.LowerWindow.FiniteChecker

/-! One fixed native-evaluated chunk of the upstream lower-window certificate.
Uses Lean's native evaluation trust boundary, disclosed in the submission. -/
namespace Erdos776.Uniform

theorem lowerWindowNative317_certificate :
    (List.range 32).all (fun d => lowerWindowCheck (317 + d)) = true := by
  native_decide

theorem lowerWindowNative317 (r : ℕ) (hlo : 317 ≤ r) (hhi : r ≤ 348) :
    lowerWindowCheck r = true := by
  have hall := List.all_eq_true.mp lowerWindowNative317_certificate
  have hd : r - 317 ∈ List.range 32 := by
    simp only [List.mem_range]
    omega
  simpa only [show 317 + (r - 317) = r by omega] using hall (r - 317) hd

end Erdos776.Uniform
#print axioms Erdos776.Uniform.lowerWindowNative317_certificate
