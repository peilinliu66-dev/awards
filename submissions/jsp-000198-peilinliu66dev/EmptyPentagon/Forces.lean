/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Forces.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions

noncomputable section
namespace Horton

/-- Every set of exactly `n` points in general position contains an empty convex `k`-gon. -/
def ForcesEmptyKGon (k n : ℕ) : Prop :=
  ∀ S : Finset Point, S.card = n → GeneralPosition S →
    ∃ V : Finset Point, V.card = k ∧ EmptyConvexPolygon S V

end Horton
