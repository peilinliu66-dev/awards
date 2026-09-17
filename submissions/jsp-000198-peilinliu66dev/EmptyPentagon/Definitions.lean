import Mathlib

noncomputable section
namespace Horton

abbrev Point := ℝ × ℝ

def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

def GeneralPosition (S : Finset Point) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
    a ≠ b → a ≠ c → b ≠ c → orient a b c ≠ 0

def EmptyConvexPolygon (S V : Finset Point) : Prop :=
  V ⊆ S ∧
    ConvexIndependent ℝ (fun v : (V : Set Point) => (v : Point)) ∧
    ∀ p ∈ S, p ∉ V → p ∉ interior (convexHull ℝ (V : Set Point))

end Horton
