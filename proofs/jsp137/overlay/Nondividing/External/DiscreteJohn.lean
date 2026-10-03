/-
Original proof replacements for the interface statements of
Theofil Xeff, theofilxeff/erdos_131, commit
aeafec6479cf23b584a65fce6cb6dc1005be3b1f.
No author-project proof body is redistributed in this overlay.
Compiled and audited; see BUILD_REPORT.json. The copied statement surface is attributed to its source.
-/
import Erdos131Research.John
import Nondividing.GAP
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace Nondividing.External

def realPoint {d : ℕ} (z : Fin d → ℤ) : Fin d → ℝ :=
  fun i => z i

def integerRealSpan {d : ℕ} (A : Finset (Fin d → ℤ)) :
    Submodule ℝ (Fin d → ℝ) :=
  Submodule.span ℝ (realPoint '' (A : Set (Fin d → ℤ)))

/-- Proved interface replacement; see Erdos131Research.John. -/
theorem discrete_john (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, 0 < C ∧
      ∀ (h : ℕ) (H : Submodule ℝ (Fin d → ℝ))
        (K : Set (Fin d → ℝ)) (A : Finset (Fin d → ℤ)),
        Module.finrank ℝ H = h →
        IsCompact K →
        Convex ℝ K →
        K.Nonempty →
        (∀ x, x ∈ K ↔ -x ∈ K) →
        K ⊆ H →
        (∀ z, z ∈ A ↔ realPoint z ∈ K) →
        integerRealSpan A = H →
        ∃ P : GAP d h,
          (∀ i, realPoint (P.step i) ∈ H) ∧
          P.Proper ∧
          P.dilatedCarrier c ⊆ A ∧
          A ⊆ P.carrier ∧
          P.carrier.card ≤ C * A.card := by
  exact Erdos131Research.discrete_john d

end Nondividing.External

