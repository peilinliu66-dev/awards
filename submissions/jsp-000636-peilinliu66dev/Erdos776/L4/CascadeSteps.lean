import Erdos776.Combinatorics.NumericShadow
import Erdos776.L4.ReverseEnvelope

/-!
# Cascade evaluations used by L4

This file instantiates the generic numerical Kruskal--Katona bridge with the
specific cascades in `docs/L4_PROOF.md`.
-/

namespace Erdos776.L4

open Erdos776.KruskalKatona

/-- The concrete numerical shadow on the `r+4` point ground set. -/
noncomputable def l4Shadow (r : ℕ) : ℕ → ℕ → ℕ :=
  kkShadow (r + 4)

theorem l4Shadow_mono (r : ℕ) : ∀ k, Monotone (l4Shadow r k) := by
  intro k
  exact kkShadow_mono (r + 4) k

private theorem top_step_one (r : ℕ) :
    l4Shadow r (r + 1) r = (r + 2).choose 2 - 1 := by
  let digits := diagonalDigits (r + 1) r
  have hcanon : IsCanonical (r + 1) digits :=
    isCanonical_diagonalDigits (by omega)
  have hbound : BoundedFamily (r + 4) (cascadeFamily (r + 1) digits) := by
    intro s hs
    apply mem_cascadeFamily_lt_of_digits_lt _ hs
    intro d hd
    exact (mem_diagonalDigits_le hd).trans_lt (by omega)
  have heval := kkShadow_eq_cascadeShadowValue hcanon hbound
  have hvalue : cascadeValue (r + 1) digits = r :=
    cascadeValue_diagonalDigits (by omega)
  have hshadow : cascadeShadowValue (r + 1) digits = (r + 2).choose 2 - 1 := by
    simpa [digits] using cascadeShadowValue_diagonalDigits_drop_one (r + 1)
  change kkShadow (r + 4) (r + 1) r = (r + 2).choose 2 - 1
  rw [hvalue, hshadow] at heval
  exact heval

private theorem top_step_two (r : ℕ) (hr : 2 ≤ r) :
    l4Shadow r r (topRValue r) =
      (r + 2).choose (r - 1) + r.choose 2 := by
  let digits := (r + 2) :: diagonalDigits (r - 1) (r - 1)
  have htail : IsCanonical (r - 1) (diagonalDigits (r - 1) (r - 1)) :=
    isCanonical_diagonalDigits le_rfl
  have hcanon : IsCanonical r digits := by
    rw [show r = (r - 1) + 1 by omega]
    rw [isCanonical_succ_cons]
    refine ⟨by omega, ?_, htail⟩
    intro d hd
    exact lt_of_le_of_lt (mem_diagonalDigits_le hd) (by omega)
  have hsym : (r + 2).choose r = (r + 2).choose 2 := by
    simpa only [show r + 2 - 2 = r by omega] using
      (Nat.choose_symm (n := r + 2) (k := 2) (by omega))
  have hvalue : cascadeValue r digits = topRValue r := by
    simp only [digits, cascadeValue_cons]
    rw [cascadeValue_diagonalDigits le_rfl, hsym]
    rfl
  have hshadow : cascadeShadowValue r digits =
      (r + 2).choose (r - 1) + r.choose 2 := by
    simp only [digits, cascadeShadowValue_cons]
    rw [show cascadeValue (r - 2) (diagonalDigits (r - 1) (r - 1)) =
        cascadeShadowValue (r - 1) (diagonalDigits (r - 1) (r - 1)) by rfl,
      cascadeShadowValue_diagonalDigits_full]
    congr 2
    omega
  have hcanon' : IsCanonical r ((r + 2) :: diagonalDigits (r - 1) (r - 1)) := by
    simpa [digits] using hcanon
  have heval := kkShadow_eq_cascadeShadowValue_of_head hcanon' (by omega : r + 2 < r + 4)
  change kkShadow (r + 4) r (topRValue r) =
    (r + 2).choose (r - 1) + r.choose 2
  rw [← hvalue]
  change kkShadow (r + 4) r (cascadeValue r ((r + 2) :: diagonalDigits (r - 1) (r - 1))) = _
  rw [heval]
  exact hshadow

private theorem top_five_canonical (r : ℕ) (hr : 15 ≤ r) :
    IsCanonical (r - 1) [r + 2, r, r - 2, r - 4, r - 5] := by
  rw [show r - 1 = (r - 2) + 1 by omega]
  rw [isCanonical_succ_cons]
  refine ⟨by omega, ?_, ?_⟩
  · simp
    omega
  rw [show r - 2 = (r - 3) + 1 by omega]
  rw [isCanonical_succ_cons]
  refine ⟨by omega, ?_, ?_⟩
  · simp
    omega
  rw [show r - 3 = (r - 4) + 1 by omega]
  rw [isCanonical_succ_cons]
  refine ⟨by omega, ?_, ?_⟩
  · simp
    omega
  rw [show r - 4 = (r - 5) + 1 by omega]
  rw [isCanonical_succ_cons]
  refine ⟨by omega, ?_, ?_⟩
  · simp
  rw [show r - 5 = (r - 6) + 1 by omega]
  rw [isCanonical_succ_cons]
  exact ⟨by omega, by simp, by simp⟩

private theorem top_step_three (r : ℕ) (hr : 15 ≤ r) :
    l4Shadow r (r - 1) (topRm1Value r) =
      (r + 2).choose (r - 2) + r.choose (r - 3) +
        (r - 2).choose (r - 4) + (r - 4) + (r - 5) := by
  let digits := [r + 2, r, r - 2, r - 4, r - 5]
  have hcanon : IsCanonical (r - 1) digits := top_five_canonical r hr
  have hr2 : r.choose (r - 2) = r.choose 2 := by
    simpa only using (Nat.choose_symm (n := r) (k := 2) (by omega))
  have hr3 : (r - 2).choose (r - 3) = r - 2 := by
    simpa only [Nat.choose_one_right, show r - 2 - 1 = r - 3 by omega] using (Nat.choose_symm (n := r - 2) (k := 1) (by omega))
  have hr4 : (r - 4).choose (r - 5) = r - 4 := by
    simpa only [Nat.choose_one_right, show r - 4 - 1 = r - 5 by omega] using (Nat.choose_symm (n := r - 4) (k := 1) (by omega))
  have hr5 : (r - 5).choose (r - 6) = r - 5 := by
    simpa only [Nat.choose_one_right, show r - 5 - 1 = r - 6 by omega] using (Nat.choose_symm (n := r - 5) (k := 1) (by omega))
  have hvalue : cascadeValue (r - 1) digits = topRm1Value r := by
    simp only [digits, cascadeValue_cons, cascadeValue_nil]
    rw [show r - 1 - 1 = r - 2 by omega,
      show r - 2 - 1 = r - 3 by omega,
      show r - 3 - 1 = r - 4 by omega,
      show r - 4 - 1 = r - 5 by omega,
      hr2, hr3, Nat.choose_self, Nat.choose_self]
    unfold topRm1Value
    omega
  have hshadow : cascadeShadowValue (r - 1) digits =
      (r + 2).choose (r - 2) + r.choose (r - 3) +
        (r - 2).choose (r - 4) + (r - 4) + (r - 5) := by
    simp only [digits, cascadeShadowValue, cascadeValue_cons, cascadeValue_nil]
    rw [show r - 1 - 1 = r - 2 by omega,
      show r - 2 - 1 = r - 3 by omega,
      show r - 3 - 1 = r - 4 by omega,
      show r - 4 - 1 = r - 5 by omega,
      show r - 5 - 1 = r - 6 by omega,
      hr4, hr5]
    omega
  have hcanon' : IsCanonical (r - 1) [r + 2, r, r - 2, r - 4, r - 5] := by
    simpa [digits] using hcanon
  have heval := kkShadow_eq_cascadeShadowValue_of_head hcanon' (by omega : r + 2 < r + 4)
  change kkShadow (r + 4) (r - 1) (topRm1Value r) = _
  rw [← hvalue]
  change kkShadow (r + 4) (r - 1)
      (cascadeValue (r - 1) [r + 2, r, r - 2, r - 4, r - 5]) = _
  rw [heval]
  exact hshadow

/-- The three exact top cascade evaluations in Lemma L4-T. -/
theorem l4_topStepIdentities (r : ℕ) (hr : 29 ≤ r) :
    TopStepIdentities (l4Shadow r) r := by
  exact ⟨top_step_one r, top_step_two r (by omega), top_step_three r (by omega)⟩

end Erdos776.L4
