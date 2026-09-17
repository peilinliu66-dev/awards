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

/-- Positive cyclic side orientations characterize points strictly inside a triangle.
Proof reused verbatim from the sibling JSP-000198 Horton campaign (same definitions). -/
theorem mem_interior_triangle_of_orient_pos (a b c p : Point)
    (habc : 0 < orient a b c) (habp : 0 < orient a b p)
    (hbcp : 0 < orient b c p) (hcap : 0 < orient c a p) :
    p ∈ interior (convexHull ℝ ({a, b, c} : Set Point)) := by
  let U : Set Point :=
    {q | 0 < orient a b q ∧ 0 < orient b c q ∧ 0 < orient c a q}
  have hU_open : IsOpen U := by
    dsimp [U]
    change IsOpen ({q | 0 < orient a b q} ∩
      ({q | 0 < orient b c q} ∩ {q | 0 < orient c a q}))
    exact (isOpen_lt continuous_const (by unfold orient; fun_prop)).inter
      ((isOpen_lt continuous_const (by unfold orient; fun_prop)).inter
        (isOpen_lt continuous_const (by unfold orient; fun_prop)))
  have hU_sub : U ⊆ convexHull ℝ ({a, b, c} : Set Point) := by
    intro q hq
    let w : Fin 3 → ℝ := fun i ↦
      match i with
      | 0 => orient b c q / orient a b c
      | 1 => orient c a q / orient a b c
      | 2 => orient a b q / orient a b c
    let z : Fin 3 → Point := fun i ↦
      match i with
      | 0 => a
      | 1 => b
      | 2 => c
    apply mem_convexHull_of_exists_fintype w z
    · intro i
      rcases hq with ⟨habq, hbcq, hcaq⟩
      fin_cases i
      · exact div_nonneg hbcq.le habc.le
      · exact div_nonneg hcaq.le habc.le
      · exact div_nonneg habq.le habc.le
    · simp [Fin.sum_univ_succ, w]
      field_simp [ne_of_gt habc]
      simp only [orient]
      ring
    · intro i
      fin_cases i <;> simp [z]
    · ext <;> simp [Fin.sum_univ_succ, w, z]
      · field_simp [ne_of_gt habc]
        simp only [orient]
        ring
      · field_simp [ne_of_gt habc]
        simp only [orient]
        ring
  exact interior_maximal hU_sub hU_open ⟨habp, hbcp, hcap⟩

end Horton
