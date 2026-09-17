/-
Copyright (c) 2026 JSP-000198 formalization contributors.
Released under the MIT license; see Prize/LICENSE_MIT.
Adapted from tester-lean/jsp-000198-horton-lean,
commit 313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0.
Mathematical construction: J. D. Horton.
Local port to Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/

import Prize.Horton.Basic

namespace Prize.Horton

open Prize.Geometry

/-- Indices in the `b`-th parity class, renumbered for the child configuration. -/
def childIndices (S : Finset ℕ) (b : ℕ) : Finset ℕ :=
  (S.filter fun i => i % 2 = b).image fun i => i / 2

theorem mem_childIndices {S : Finset ℕ} {b i : ℕ} (hb : b < 2) :
    i ∈ childIndices S b ↔ 2 * i + b ∈ S := by
  simp only [childIndices, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨j, ⟨hj, hjb⟩, hji⟩
    have heq : j = 2 * i + b := by omega
    exact heq ▸ hj
  · intro hi
    exact ⟨2 * i + b, ⟨hi, by omega⟩, by omega⟩

theorem card_childIndices (S : Finset ℕ) (b : ℕ) :
    (childIndices S b).card = (S.filter fun i => i % 2 = b).card := by
  apply Finset.card_image_iff.mpr
  intro i hi j hj heq
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  dsimp at heq hi' hj'
  omega

theorem card_children (S : Finset ℕ) :
    (childIndices S 0).card + (childIndices S 1).card = S.card := by
  rw [card_childIndices, card_childIndices]
  have heq : (S.filter fun i => i % 2 = 1) = (S.filter fun i => ¬i % 2 = 0) := by
    ext i
    simp only [Finset.mem_filter]
    have hmod : i % 2 = 1 ↔ ¬i % 2 = 0 := by omega
    exact and_congr_right fun _ => hmod
  rw [heq]
  exact Finset.card_filter_add_card_filter_not (fun i => i % 2 = 0)

theorem childIndices_bound {S : Finset ℕ} {depth b : ℕ} (hb : b < 2)
    (hS : ∀ i ∈ S, i < 2 ^ (depth + 1)) :
    ∀ i ∈ childIndices S b, i < 2 ^ depth := by
  intro i hi
  have h := hS _ ((mem_childIndices hb).mp hi)
  rw [pow_succ] at h
  omega

/-- The interior of every triangle on selected indices contains no other indexed point.
This follows from a genuine empty convex polygon when `p` is injective. -/
def TriangleEmpty (depth : ℕ) (p : ℕ → Point) (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ t < 2 ^ depth,
    p t ∈ interior (convexHull ℝ ({p a, p b, p c} : Set Point)) → t = a ∨ t = b ∨ t = c

theorem TriangleEmpty.child {depth : ℕ} {p : ℕ → Point} {S : Finset ℕ}
    (h : TriangleEmpty (depth + 1) p S) {r : ℕ} (hr : r < 2) :
    TriangleEmpty depth (fun i => p (2 * i + r)) (childIndices S r) := by
  intro a ha b hb c hc t ht htri
  have hta : 2 * t + r < 2 ^ (depth + 1) := by rw [pow_succ]; omega
  have heq := h _ ((mem_childIndices hr).mp ha) _ ((mem_childIndices hr).mp hb)
    _ ((mem_childIndices hr).mp hc) _ hta htri
  omega

end Prize.Horton
