/- Attributed source interface with an original proved adapter. Compiled and audited; see BUILD_REPORT.json. -/
import Erdos131Research.CFP
import Nondividing.GAP
import Nondividing.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Nondividing.External

/-- `s(C)=|C|/(log |C|)^2`, kept real so GAP dilation uses the manuscript's
floor convention. -/
noncomputable def structureScale (m : ℕ) : ℝ :=
  m / (Real.log m) ^ 2

/-- Proved CFP interface, with the original real logarithmic scale. -/
theorem cfp_structure
    (ell : ℕ) (beta : ℝ) (hbeta : 1 < beta) :
    ∃ c : ℝ, 0 < c ∧ ∃ D m₀ : ℕ,
      ∀ (C : Finset (Fin ell → ℤ)) (M : Fin ell → ℕ),
        m₀ ≤ C.card →
        C ⊆ coordinateBox M →
        ((coordinateBox M).card : ℝ) ≤
          Real.rpow (C.card : ℝ) beta →
        ∃ Chat : Finset (Fin ell → ℤ),
          Chat ⊆ C ∧
          ((C \ Chat).card : ℝ) ≤
            c⁻¹ * C.card / Real.log C.card ∧
        ∃ e : ℕ, e ≤ D ∧ ∃ P : GAP ell e,
          Chat ∪ {0} ⊆ P.carrier ∧
        ∃ C₀ : Finset (Fin ell → ℤ),
          C₀ ⊆ Chat ∧
          (C₀.card : ℝ) ≤ structureScale C.card ∧
        ∃ q : Fin ell → ℤ,
          q ∈ P.dilatedCarrier (structureScale C.card) ∧
          (∀ z ∈ P.dilatedCarrier (c * structureScale C.card),
            q + z ∈ subsetSums C₀) ∧
          Set.InjOn P.evalHom
            (P.dilatedCoeffBox (c * structureScale C.card) : Set (Fin e → ℤ)) := by
  exact Erdos131Research.cfp_structure ell beta hbeta

end Nondividing.External

