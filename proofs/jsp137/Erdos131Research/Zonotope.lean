/-
Copyright (c) 2026. Released under Apache 2.0.
Original anisotropic adapter for the separately obtained deterministic
rounding proof Erdos186.Zonotope.exists_subset_sum_approximation.
Compiled and audited; Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
-/
import Nondividing.Box
import ErdosProblems.Erdos186.Zonotope

open scoped BigOperators
namespace Erdos131Research
noncomputable section

def InZonotope {d : ℕ} (A : Finset (Fin d → ℤ)) (z : Fin d → ℝ) : Prop :=
  ∃ t : (Fin d → ℤ) → ℝ,
    (∀ a ∈ A, 0 ≤ t a ∧ t a ≤ 1) ∧
    z = fun i => ∑ a ∈ A, t a * (a i : ℝ)

theorem zonotope_rounding {d : ℕ} (A : Finset (Fin d → ℤ)) (M : Fin d → ℕ)
    (hA : A ⊆ Nondividing.coordinateBox M) {z : Fin d → ℝ}
    (hz : InZonotope A z) :
    ∃ S : Finset (Fin d → ℤ), S ⊆ A ∧
      ∀ i, |z i - ∑ a ∈ S, (a i : ℝ)| ≤
        Real.sqrt (d * (A ∪ {0}).card) * (2 * M i + 1) := by
  classical
  obtain ⟨t, ht, rfl⟩ := hz
  let w : Fin d → ℝ := fun i => 2 * (M i : ℝ) + 1
  have hw : ∀ i, 0 < w i := fun i => by dsimp [w]; positivity
  let v : (Fin d → ℤ) → Fin d → ℝ := fun a i => (a i : ℝ) / w i
  have hv : ∀ a ∈ A, ∀ i, |v a i| ≤ 1 := by
    intro a ha i
    have hab := (Nondividing.mem_coordinateBox.mp (hA ha)) i
    have hlo : -(M i : ℝ) ≤ (a i : ℝ) := by exact_mod_cast hab.1
    have hhi : (a i : ℝ) ≤ (M i : ℝ) := by exact_mod_cast hab.2
    have habs : |(a i : ℝ)| ≤ M i := abs_le.mpr ⟨hlo, hhi⟩
    dsimp only [v]
    rw [abs_div, abs_of_pos (hw i), div_le_one (hw i)]
    exact habs.trans (by dsimp [w]; nlinarith [show (0 : ℝ) ≤ (M i : ℝ) by positivity])
  obtain ⟨S, hSA, hS⟩ :=
    Erdos186.Zonotope.exists_subset_sum_approximation A t v 1 ht (by norm_num) hv
  refine ⟨S, hSA, ?_⟩
  intro i
  have hid : (∑ a ∈ A, t a * v a i) - ∑ a ∈ S, v a i =
      ((∑ a ∈ A, t a * (a i : ℝ)) - ∑ a ∈ S, (a i : ℝ)) / w i := by
    simp only [v, mul_div_assoc, Finset.sum_div, sub_div]
  have herr := hS i
  rw [hid, abs_div, abs_of_pos (hw i), mul_one] at herr
  have herr' := (div_le_iff₀ (hw i)).mp herr
  have hcard : A.card ≤ (A ∪ {0}).card :=
    Finset.card_le_card (Finset.subset_union_left)
  have hsqrt : Real.sqrt (((d * A.card : ℕ) : ℝ)) ≤
      Real.sqrt (((d * (A ∪ {0}).card : ℕ) : ℝ)) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.mul_le_mul_left d hcard
  simpa only [Nat.cast_mul, w] using
    herr'.trans (mul_le_mul_of_nonneg_right hsqrt (hw i).le)

end
end Erdos131Research

#print axioms Erdos131Research.zonotope_rounding
