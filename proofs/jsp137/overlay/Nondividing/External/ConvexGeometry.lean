/- Proved replacements of the attributed E5 interface. Compiled and audited; see BUILD_REPORT.json.
The difference-body constant is intentionally coarse and dimension-only. -/
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Nondividing.External.DiscreteJohn
import Erdos131Research.ConvexBodyLimits
import Erdos131Research.LatticeVolume
import Erdos131Research.DifferenceVolume

namespace Nondividing.External

open Filter MeasureTheory


theorem blaschke_selection {d : ℕ}
    (K : ℕ → ConvexBody (Fin d → ℝ)) (C : ConvexBody (Fin d → ℝ))
    (hKC : ∀ n, K n ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ L : ConvexBody (Fin d → ℝ), Tendsto (K ∘ φ) atTop (nhds L) :=
  Erdos131Research.blaschke_selection K C hKC

theorem convexBody_volume_tendsto {d : ℕ}
    {K : ℕ → ConvexBody (Fin d → ℝ)} {L : ConvexBody (Fin d → ℝ)}
    (hK : Tendsto K atTop (nhds L)) :
    Tendsto (fun n => volume (K n : Set (Fin d → ℝ))) atTop
      (nhds (volume (L : Set (Fin d → ℝ)))) :=
  Erdos131Research.convexBody_volume_tendsto hK

theorem rogers_shephard {d : ℕ} (K : ConvexBody (Fin d → ℝ)) :
    volume ((K + (-1 : ℝ) • K : ConvexBody (Fin d → ℝ)) :
      Set (Fin d → ℝ)) ≤
      (Erdos131Research.rogersConstant d : ENNReal) *
        volume (K : Set (Fin d → ℝ)) :=
  Erdos131Research.rogers_shephard K

theorem full_rank_lattice_points_le_volume (d : ℕ) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (K : ConvexBody (Fin d → ℝ)) (A : Finset (Fin d → ℤ)),
        (∀ x ∈ (K : Set (Fin d → ℝ)), -x ∈ K) →
        (∀ z, z ∈ A ↔ realPoint z ∈ K) →
        Submodule.span ℝ (realPoint '' (A : Set (Fin d → ℤ))) = ⊤ →
        (A.card : ENNReal) ≤ (C : ENNReal) *
          volume (K : Set (Fin d → ℝ)) :=
  Erdos131Research.full_rank_lattice_points_le_volume d

end Nondividing.External

