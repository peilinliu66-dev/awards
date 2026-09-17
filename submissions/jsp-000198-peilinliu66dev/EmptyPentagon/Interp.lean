/-
Ported from CollinYuanjieRen/awards, PR #283, commit
b8bb4f7803f921a7970abc880291ad9372111360,
submissions/jsp-000198-smallk-cyr/EmptyPentagon/.
Original Lean formalization: CollinYuanjieRen, with disclosed Claude Code assistance.
Copyright (c) 2026 The Justin Sun Prize contributors.
MIT license: see LICENSE in this directory. Changes for Lean 4.33.1 are
recorded in PORT_STATUS.md; theorem statements and mathematical meaning are retained.
Triangle-interior material also credits the MIT-licensed Horton campaign;
see LICENSE-HORTON and the original source comment.
-/

import EmptyPentagon.Definitions

noncomputable section
namespace Horton

/-- Orientation is affine in its last argument. -/
theorem orient_affine_comb (u v a b c : Point) (α β γ : ℝ) (h : α + β + γ = 1) :
    orient u v (α • a + β • b + γ • c) =
      α * orient u v a + β * orient u v b + γ * orient u v c := by
  have hγ : γ = 1 - α - β := by linarith
  subst hγ
  simp only [orient, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  ring

/-- A strict orientation certificate yields strictly positive barycentric coordinates. -/
theorem barycentric_of_orient_pos (a b c p : Point) (habc : 0 < orient a b c)
    (h1 : 0 < orient a b p) (h2 : 0 < orient b c p) (h3 : 0 < orient c a p) :
    ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧ p = α • a + β • b + γ • c := by
  have hD : orient a b c ≠ 0 := ne_of_gt habc
  refine ⟨orient b c p / orient a b c, orient c a p / orient a b c,
    orient a b p / orient a b c, div_pos h2 habc, div_pos h3 habc, div_pos h1 habc, ?_, ?_⟩
  · field_simp
    simp only [orient]
    ring
  · ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      simp only [orient]
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      simp only [orient]
      ring

/-- Points of a closed triangle are nonnegative barycentric combinations of its vertices. -/
theorem exists_barycentric_of_mem_convexHull_triangle (a b c p : Point)
    (hp : p ∈ convexHull ℝ ({a, b, c} : Set Point)) :
    ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧ p = α • a + β • b + γ • c := by
  rw [convexHull_insert (Set.insert_nonempty b {c}), convexHull_pair, mem_convexJoin] at hp
  obtain ⟨x, hx, q, hq, hpq⟩ := hp
  rw [Set.mem_singleton_iff] at hx
  subst hx
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hq
  obtain ⟨u, w, hu, hw, huw, rfl⟩ := hpq
  refine ⟨u, w * s, w * t, hu, mul_nonneg hw hs, mul_nonneg hw ht, ?_, ?_⟩
  · linear_combination huw + w * hst
  · simp only [smul_add, mul_smul, add_assoc]

/-- A point of a closed triangle avoiding its three edge lines is strictly inside it. -/
theorem orient_pos_of_mem_convexHull_triangle (a b c p : Point) (habc : 0 < orient a b c)
    (hp : p ∈ convexHull ℝ ({a, b, c} : Set Point))
    (h1 : orient a b p ≠ 0) (h2 : orient b c p ≠ 0) (h3 : orient c a p ≠ 0) :
    0 < orient a b p ∧ 0 < orient b c p ∧ 0 < orient c a p := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩ :=
    exists_barycentric_of_mem_convexHull_triangle a b c p hp
  have e1 : orient a b (α • a + β • b + γ • c) = γ * orient a b c := by
    rw [orient_affine_comb a b a b c α β γ hsum]
    simp only [orient]
    ring
  have e2 : orient b c (α • a + β • b + γ • c) = α * orient b c a := by
    rw [orient_affine_comb b c a b c α β γ hsum]
    simp only [orient]
    ring
  have e3 : orient c a (α • a + β • b + γ • c) = β * orient c a b := by
    rw [orient_affine_comb c a a b c α β γ hsum]
    simp only [orient]
    ring
  have hbca : orient b c a = orient a b c := by simp only [orient]; ring
  have hcab : orient c a b = orient a b c := by simp only [orient]; ring
  rw [e1] at h1 ⊢
  rw [e2, hbca] at h2 ⊢
  rw [e3, hcab] at h3 ⊢
  refine ⟨?_, ?_, ?_⟩
  · exact lt_of_le_of_ne (mul_nonneg hγ habc.le) (Ne.symm h1)
  · exact lt_of_le_of_ne (mul_nonneg hα habc.le) (Ne.symm h2)
  · exact lt_of_le_of_ne (mul_nonneg hβ habc.le) (Ne.symm h3)

end Horton
