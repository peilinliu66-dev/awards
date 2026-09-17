/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Parabola.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Forces

noncomputable section
namespace Horton

/-- Points on the parabola `y = x^2` with distinct abscissae are in general position. -/
theorem exists_generalPosition_card (n : ℕ) :
    ∃ S : Finset Point, S.card = n ∧ GeneralPosition S := by
  have hinj : Function.Injective (fun i : ℕ => (((i : ℝ), (i : ℝ) ^ 2) : Point)) := by
    intro i j hij
    exact Nat.cast_injective (congrArg Prod.fst hij)
  refine ⟨(Finset.range n).image (fun i : ℕ => (((i : ℝ), (i : ℝ) ^ 2) : Point)), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  · intro a ha b hb c hc hab hac hbc
    simp only [Finset.mem_image, Finset.mem_range] at ha hb hc
    obtain ⟨i, -, rfl⟩ := ha
    obtain ⟨j, -, rfl⟩ := hb
    obtain ⟨k, -, rfl⟩ := hc
    have hij : (i : ℝ) ≠ j := fun h => hab (Prod.ext h (by rw [h]))
    have hik : (i : ℝ) ≠ k := fun h => hac (Prod.ext h (by rw [h]))
    have hjk : (j : ℝ) ≠ k := fun h => hbc (Prod.ext h (by rw [h]))
    have key :
        orient ((i : ℝ), (i : ℝ) ^ 2) ((j : ℝ), (j : ℝ) ^ 2) ((k : ℝ), (k : ℝ) ^ 2) =
          ((j : ℝ) - i) * ((k : ℝ) - i) * ((k : ℝ) - j) := by
      simp only [orient]
      ring
    rw [key]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hij.symm) (sub_ne_zero.mpr hik.symm))
      (sub_ne_zero.mpr hjk.symm)

/-- A forced empty `k`-gon needs at least `k` points. -/
theorem ForcesEmptyKGon.le {k n : ℕ} (h : ForcesEmptyKGon k n) : k ≤ n := by
  obtain ⟨S, hS, hgen⟩ := exists_generalPosition_card n
  obtain ⟨V, hV, hVS⟩ := h S hS hgen
  rw [← hV, ← hS]
  exact Finset.card_le_card hVS.1

end Horton
