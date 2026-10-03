/-
Original proof replacements for the interface statements of
Theofil Xeff, theofilxeff/erdos_131, commit
aeafec6479cf23b584a65fce6cb6dc1005be3b1f.
No author-project proof body is redistributed in this overlay.
Compiled and audited; see BUILD_REPORT.json. The copied statement surface is attributed to its source.
-/
import Erdos131Research.ConvexDensity
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Nondividing.External

def closedUpperHalfspace {r : ℕ}
    (ell : Module.Dual ℝ (Fin r → ℝ)) (t : ℝ) : Set (Fin r → ℝ) :=
  {x | t ≤ ell x}

def SetMuConvexPosition {r : ℕ} (μ : ℝ) (A : Finset (Fin r → ℝ)) : Prop :=
  ∀ p ∈ A, ∃ ell : Module.Dual ℝ (Fin r → ℝ), ∃ t : ℝ,
    p ∈ closedUpperHalfspace ell t ∧
    (((A : Set (Fin r → ℝ)) ∩ closedUpperHalfspace ell t).ncard : ℝ)
      ≤ μ * A.card

/-- Proved interface replacement; see Erdos131Research.ConvexDensity. -/
theorem convex_density_set
    (r : ℕ) (hr : 1 ≤ r) (eps : ℝ) (heps : 0 < eps) :
    ∃ tau μ₀ : ℝ, 0 < tau ∧ tau < 1 ∧ 0 < μ₀ ∧
      ∀ μ : ℝ, 0 < μ → μ < μ₀ → ∃ n₀ : ℕ,
      ∀ (Omega : Set (Fin r → ℝ)) (A : Finset (Fin r → ℝ)),
        n₀ ≤ A.card →
        IsCompact Omega →
        Convex ℝ Omega →
        (interior Omega).Nonempty →
        (A : Set (Fin r → ℝ)) ⊆ Omega →
        SetMuConvexPosition μ A →
        ∃ eta : ℝ, μ ≤ eta ∧ eta ≤ Real.rpow μ tau ∧
        ∃ Omega' : Set (Fin r → ℝ),
          MeasurableSet Omega' ∧
          Convex ℝ Omega' ∧
          Omega' ⊆ Omega ∧
          MeasureTheory.volume Omega' ≤
            ENNReal.ofReal eta * MeasureTheory.volume Omega ∧
          (eta ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps)) * A.card ≤
            (((A : Set (Fin r → ℝ)) ∩ Omega').ncard : ℝ) := by
  exact Erdos131Research.convex_density_set r hr eps heps

end Nondividing.External

