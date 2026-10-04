import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Length preservation in a convex one-dimensional fiber

The compiled scalar measure step for coordinate symmetrization. The
finite-dimensional Fubini assembly and Anderson comparison are separate
modules, with their own build and axiom-audit evidence.
-/

namespace Erdos524.OneDimensionalFibers

open Set MeasureTheory

def halfDifference (A : Set ℝ) : Set ℝ :=
  {x | ∃ u ∈ A, ∃ v ∈ A, (u - v) / 2 = x}

theorem halfDifference_Icc (a b : ℝ) :
    halfDifference (Icc a b) = Icc ((a - b) / 2) ((b - a) / 2) := by
  ext x
  constructor
  · rintro ⟨u, ⟨hau, hub⟩, v, ⟨hav, hvb⟩, rfl⟩
    constructor <;> linarith
  · rintro ⟨hxlo, hxhi⟩
    refine ⟨(a + b) / 2 + x, ⟨?_, ?_⟩,
      (a + b) / 2 - x, ⟨?_, ?_⟩, ?_⟩
    all_goals linarith

theorem volume_halfDifference_Icc (a b : ℝ) :
    volume (halfDifference (Icc a b)) = volume (Icc a b) := by
  rw [halfDifference_Icc, Real.volume_Icc, Real.volume_Icc]
  congr 1
  ring

theorem halfDifference_empty : halfDifference (∅ : Set ℝ) = ∅ := by
  ext x
  simp [halfDifference]

/-- No measurable choice of interval endpoints is required: this equality
is proved separately for every compact convex fiber before integration. -/
theorem volume_halfDifference {A : Set ℝ}
    (hcompact : IsCompact A) (hconvex : Convex ℝ A) :
    volume (halfDifference A) = volume A := by
  by_cases hne : A.Nonempty
  · have hA : A = Icc (sInf A) (sSup A) :=
      eq_Icc_of_connected_compact ⟨hne, hconvex.isPreconnected⟩ hcompact
    rw [hA]
    exact volume_halfDifference_Icc _ _
  · have hA : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hA, halfDifference_empty]

end Erdos524.OneDimensionalFibers
