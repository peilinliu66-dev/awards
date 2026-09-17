import Erdos776.Uniform.LowerWindow.FiniteChecker

/-! One fixed native-evaluated chunk of the upstream lower-window certificate.
Uses Lean's native evaluation trust boundary, disclosed in the submission. -/
namespace Erdos776.Uniform

theorem lowerWindowNative349_certificate :
    (List.range 29).all (fun d => lowerWindowCheck (349 + d)) = true := by
  native_decide

theorem lowerWindowNative349 (r : ℕ) (hlo : 349 ≤ r) (hhi : r ≤ 377) :
    lowerWindowCheck r = true := by
  have hall := List.all_eq_true.mp lowerWindowNative349_certificate
  have hd : r - 349 ∈ List.range 29 := by
    simp only [List.mem_range]
    omega
  simpa only [show 349 + (r - 349) = r by omega] using hall (r - 349) hd

end Erdos776.Uniform
#print axioms Erdos776.Uniform.lowerWindowNative349_certificate
