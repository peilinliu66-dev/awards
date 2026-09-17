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

/-- The orientation determinant vanishes exactly on collinear triples. -/
theorem orient_eq_zero_iff_collinear (a b c : Point) :
    orient a b c = 0 ↔ Collinear ℝ ({a, b, c} : Set Point) := by
  have ha : a ∈ ({a, b, c} : Set Point) := by simp
  rw [collinear_iff_of_mem ha]
  constructor
  · intro h
    unfold orient at h
    by_cases hab : a = b
    · -- Degenerate triple `{a, a, c}`: parametrize by the direction `c - a`.
      subst hab
      refine ⟨c - a, fun p hp => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
    -- Otherwise parametrize the line through `a` and `b`; `c` lies on it by `h`.
    refine ⟨b - a, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    by_cases h1 : b.1 - a.1 = 0
    · -- Vertical direction: `b.2 ≠ a.2`, and `h` forces `p.1 = a.1`.
      have h2 : b.2 - a.2 ≠ 0 := by
        intro h2
        exact hab (Prod.ext (by linarith) (by linarith))
      have hp1 : p.1 - a.1 = 0 := by
        have : (b.2 - a.2) * (p.1 - a.1) = 0 := by rw [h1] at h; linarith
        exact (mul_eq_zero.mp this).resolve_left h2
      refine ⟨(p.2 - a.2) / (b.2 - a.2), ?_⟩
      have ht : (p.2 - a.2) / (b.2 - a.2) * (b.2 - a.2) = p.2 - a.2 := div_mul_cancel₀ _ h2
      ext
      · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
        linear_combination hp1 - (p.2 - a.2) / (b.2 - a.2) * h1
      · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
        linear_combination -ht
    · refine ⟨(p.1 - a.1) / (b.1 - a.1), ?_⟩
      have ht : (p.1 - a.1) / (b.1 - a.1) * (b.1 - a.1) = p.1 - a.1 := div_mul_cancel₀ _ h1
      ext
      · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
        linear_combination -ht
      · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
        refine mul_left_cancel₀ h1 ?_
        linear_combination h - (b.2 - a.2) * ht
  · rintro ⟨v, hv⟩
    obtain ⟨r, hr⟩ := hv b (by simp)
    obtain ⟨s, hs⟩ := hv c (by simp)
    unfold orient
    rw [hr, hs]
    simp only [vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- General position is the usual "no three collinear" condition. -/
theorem generalPosition_iff_not_collinear (S : Finset Point) :
    GeneralPosition S ↔ ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set Point) := by
  unfold GeneralPosition
  simp only [ne_eq, orient_eq_zero_iff_collinear]

end Horton
