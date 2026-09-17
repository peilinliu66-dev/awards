import Erdos776.Uniform.LowerWindow.FiniteChecker
import Erdos776.Uniform.LowerWindow.PhaseAssembly
import Erdos776.Uniform.LowerWindow.NativeChunks.All

/-!
# Native-evaluated finite lower-window certificate with a proved soundness bridge

The Boolean certificate covers exactly the range between the uniform L4
endpoint and the symbolic phase theorem.  Its evaluator uses only bounded
cascade searches; the theorem `lowerWindowCheck_sound` is the trust bridge.
-/

namespace Erdos776.Uniform

/-- One finite Boolean computation for all `29 ≤ r ≤ 377`. -/
def lowerWindowFiniteBaseCheck : Bool :=
  (List.range 349).all fun d => lowerWindowCheck (29 + d)

theorem lowerWindowFiniteBaseCheck_verified :
    lowerWindowFiniteBaseCheck = true := by
  exact lowerWindowNativeAll

theorem lowerWindowCheck_eq_true_of_range
    {r : ℕ} (hr29 : 29 ≤ r) (hr377 : r ≤ 377) :
    lowerWindowCheck r = true := by
  have hall : ∀ d ∈ List.range 349, lowerWindowCheck (29 + d) = true := by
    simpa [lowerWindowFiniteBaseCheck] using
      (List.all_eq_true.mp lowerWindowFiniteBaseCheck_verified)
  let d := r - 29
  have hd : d ∈ List.range 349 := by
    simp [d]
    omega
  have h := hall d hd
  simpa [d, show 29 + (r - 29) = r by omega] using h

/-- The finite certificate proves the exact lower-window capacity predicate. -/
theorem lowerWindowFits_of_ge_29_le_377
    (r : ℕ) (hr29 : 29 ≤ r) (hr377 : r ≤ 377) :
    LowerWindowFits r := by
  exact lowerWindowCheck_sound (by omega)
    (lowerWindowCheck_eq_true_of_range hr29 hr377)

/-- Finite checking and the symbolic phase theorem meet without a gap. -/
theorem lowerWindowFits_of_ge_29 (r : ℕ) (hr : 29 ≤ r) :
    LowerWindowFits r := by
  by_cases hfinite : r ≤ 377
  · exact lowerWindowFits_of_ge_29_le_377 r hr hfinite
  · exact lowerWindowFits_of_ge_378 r (by omega)

/-- The full middle-profile threshold for the complete `r ≥ 29` range. -/
theorem fullMiddleProfileThreshold_of_ge_29 (r : ℕ) (hr : 29 ≤ r) :
    FullMiddleProfileThreshold r := by
  exact fullMiddleProfileThreshold_of_lowerWindowFits r hr
    (lowerWindowFits_of_ge_29 r hr)

/-- The least global Erdős threshold for every `r ≥ 29`. -/
theorem isErdosThreshold_of_ge_29 (r : ℕ) (hr : 29 ≤ r) :
    IsErdosThreshold r (2 * r + 5) := by
  exact isErdosThreshold_of_lowerWindowFits r hr
    (lowerWindowFits_of_ge_29 r hr)

end Erdos776.Uniform

#print axioms Erdos776.Uniform.lowerWindowFiniteBaseCheck_verified
#print axioms Erdos776.Uniform.isErdosThreshold_of_ge_29
