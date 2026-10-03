/-
Original proof replacements for the interface statements of
Theofil Xeff, theofilxeff/erdos_131, commit
aeafec6479cf23b584a65fce6cb6dc1005be3b1f.
No author-project proof body is redistributed in this overlay.
Compiled and audited; see BUILD_REPORT.json. The copied statement surface is attributed to its source.
-/
import Erdos131Research.Zonotope
import Nondividing.Box
import Nondividing.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace Nondividing.External

def InZonotope {d : ℕ} (A : Finset (Fin d → ℤ)) (z : Fin d → ℝ) : Prop :=
  ∃ t : (Fin d → ℤ) → ℝ,
    (∀ a ∈ A, 0 ≤ t a ∧ t a ≤ 1) ∧
    z = fun i => ∑ a ∈ A, t a * (a i : ℝ)

/-- Proved interface replacement; see Erdos131Research.Zonotope. -/
theorem zonotope_rounding
    {d : ℕ} (A : Finset (Fin d → ℤ)) (M : Fin d → ℕ)
    (hA : A ⊆ coordinateBox M) {z : Fin d → ℝ}
    (hz : InZonotope A z) :
    ∃ S : Finset (Fin d → ℤ), S ⊆ A ∧
      ∀ i,
        |z i - ∑ a ∈ S, (a i : ℝ)| ≤
          Real.sqrt (d * (A ∪ {0}).card) * (2 * M i + 1) := by
  exact Erdos131Research.zonotope_rounding A M hA hz

end Nondividing.External

