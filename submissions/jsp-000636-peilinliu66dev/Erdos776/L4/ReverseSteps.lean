import Erdos776.L4.CascadeSteps
import Mathlib.Tactic.NormNum

/-!
# The reverse-step cascade calculations in L4
-/

namespace Erdos776.L4

open Erdos776.KruskalKatona

private theorem l4Shadow_eval
    {r k a m q : ℕ} {digits : List ℕ}
    (hcanon : IsCanonical k (a :: digits))
    (ha : a < r + 4)
    (hvalue : cascadeValue k (a :: digits) = m)
    (hshadow : cascadeShadowValue k (a :: digits) = q) :
    l4Shadow r k m = q := by
  have heval := kkShadow_eq_cascadeShadowValue_of_head hcanon ha
  rw [hvalue, hshadow] at heval
  exact heval

private theorem reverse_shadow_3 (r : ℕ) (hr : 29 ≤ r) :
    l4Shadow r 3 (Ghat r 3 + 1) = (r + 3).choose 2 + 3 + 1 := by
  apply l4Shadow_eval (a := r + 3) (digits := [3, 1])
  · simp [IsCanonical]
    omega
  · omega
  · simp [Ghat, cascadeValue]
  · simp [cascadeShadowValue, cascadeValue]

private theorem reverse_step_3 (r : ℕ) (hr : 29 ≤ r) :
    Ghat r 2 < r + l4Shadow r 3 (Ghat r 3 + 1) := by
  rw [reverse_shadow_3 r hr]
  have hp : (r + 4).choose 2 = r + 3 + (r + 3).choose 2 := by
    simpa [Nat.choose_one_right] using Nat.choose_succ_succ (r + 3) 1
  simp only [Ghat, if_pos]
  omega

private theorem reverse_shadow_4 (r : ℕ) (hr : 29 ≤ r) :
    l4Shadow r 4 (Ghat r 4 + 1) =
      (r + 2).choose 3 + (r + 1).choose 2 + 4 + 1 := by
  apply l4Shadow_eval (a := r + 2) (digits := [r + 1, 4, 1])
  · simp [IsCanonical]
    omega
  · omega
  · simp [Ghat, cascadeValue]
    norm_num [Nat.choose]
    omega
  · simp [cascadeShadowValue, cascadeValue]
    norm_num [Nat.choose]
    omega

private theorem reverse_step_4 (r : ℕ) (hr : 29 ≤ r) :
    Ghat r 3 < r + l4Shadow r 4 (Ghat r 4 + 1) := by
  rw [reverse_shadow_4 r hr]
  have hp3 : (r + 3).choose 3 = (r + 2).choose 2 + (r + 2).choose 3 := by
    simpa using Nat.choose_succ_succ (r + 2) 2
  have hp2 : (r + 2).choose 2 = r + 1 + (r + 1).choose 2 := by
    simpa [Nat.choose_one_right] using Nat.choose_succ_succ (r + 1) 1
  simp [Ghat]
  omega

private theorem reverse_shadow_5 (r : ℕ) (hr : 29 ≤ r) :
    l4Shadow r 5 (Ghat r 5 + 1) =
      (r + 2).choose 4 + r.choose 3 + (r - 1).choose 2 + 5 + 1 := by
  apply l4Shadow_eval (a := r + 2) (digits := [r, r - 1, 5, 1])
  · simp [IsCanonical]
    omega
  · omega
  · simp [Ghat, cascadeValue]
    norm_num [Nat.choose]
    omega
  · simp [cascadeShadowValue, cascadeValue]
    norm_num [Nat.choose]
    omega

private theorem reverse_step_5 (r : ℕ) (hr : 29 ≤ r) :
    Ghat r 4 < r + l4Shadow r 5 (Ghat r 5 + 1) := by
  rw [reverse_shadow_5 r hr]
  have hp3 : (r + 1).choose 3 = r.choose 2 + r.choose 3 := by
    simpa using Nat.choose_succ_succ r 2
  have hp2 : r.choose 2 = r - 1 + (r - 1).choose 2 := by
    simpa only [Nat.succ_eq_add_one, show r - 1 + 1 = r by omega,
      Nat.choose_one_right] using Nat.choose_succ_succ (r - 1) 1
  simp [Ghat]
  omega

private theorem reverse_shadow_6 (r : ℕ) (hr : 29 ≤ r) :
    l4Shadow r 6 (Ghat r 6 + 1) =
      (r + 2).choose 5 + r.choose 4 + (r - 2).choose 3 +
        (r - 3).choose 2 + 7 + 1 := by
  apply l4Shadow_eval (a := r + 2) (digits := [r, r - 2, r - 3, 7, 1])
  · simp [IsCanonical]
    omega
  · omega
  · simp [Ghat, cascadeValue]
    norm_num [Nat.choose]
    omega
  · simp [cascadeShadowValue, cascadeValue]
    norm_num [Nat.choose]
    omega

private theorem reverse_step_6 (r : ℕ) (hr : 29 ≤ r) :
    Ghat r 5 < r + l4Shadow r 6 (Ghat r 6 + 1) := by
  rw [reverse_shadow_6 r hr]
  have hp3 : (r - 1).choose 3 = (r - 2).choose 2 + (r - 2).choose 3 := by
    simpa only [Nat.succ_eq_add_one, show r - 2 + 1 = r - 1 by omega] using
      Nat.choose_succ_succ (r - 2) 2
  have hp2 : (r - 2).choose 2 = r - 3 + (r - 3).choose 2 := by
    simpa [Nat.choose_one_right, show r - 3 + 1 = r - 2 by omega] using
      Nat.choose_succ_succ (r - 3) 1
  simp [Ghat]
  omega

private theorem reverse_shadow_7 (r : ℕ) (hr : 29 ≤ r) :
    l4Shadow r 7 (Ghat r 7 + 1) =
      (r + 2).choose 6 + r.choose 5 + (r - 2).choose 4 +
        (r - 4).choose 3 + (r - 5).choose 2 + 16 + 1 := by
  apply l4Shadow_eval (a := r + 2)
      (digits := [r, r - 2, r - 4, r - 5, 16, 1])
  · simp [IsCanonical]
    omega
  · omega
  · simp [Ghat, cascadeValue]
    norm_num [Nat.choose]
    omega
  · simp [cascadeShadowValue, cascadeValue]
    norm_num [Nat.choose]
    omega

private theorem reverse_step_7 (r : ℕ) (hr : 29 ≤ r) :
    Ghat r 6 < r + l4Shadow r 7 (Ghat r 7 + 1) := by
  rw [reverse_shadow_7 r hr]
  have hp3 : (r - 3).choose 3 = (r - 4).choose 2 + (r - 4).choose 3 := by
    simpa only [Nat.succ_eq_add_one, show r - 4 + 1 = r - 3 by omega] using
      Nat.choose_succ_succ (r - 4) 2
  have hp2 : (r - 4).choose 2 = r - 5 + (r - 5).choose 2 := by
    simpa [Nat.choose_one_right, show r - 5 + 1 = r - 4 by omega] using
      Nat.choose_succ_succ (r - 5) 1
  simp [Ghat]
  omega

private theorem reverse_shadow_8 (r : ℕ) (hr : 29 ≤ r) :
    l4Shadow r 8 (Ghat r 8 + 1) =
      (r + 2).choose 7 + r.choose 6 + (r - 2).choose 5 +
        (r - 4).choose 4 + (r - 5).choose 3 + (23 : ℕ).choose 2 + 2 := by
  apply l4Shadow_eval (a := r + 2)
      (digits := [r, r - 2, r - 4, r - 5, 23, 2])
  · simp [IsCanonical]
    omega
  · omega
  · simp [Ghat, cascadeValue]
    norm_num [Nat.choose]
    omega
  · simp [cascadeShadowValue, cascadeValue]
    norm_num [Nat.choose]
    omega

private theorem reverse_step_8 (r : ℕ) (hr : 29 ≤ r) :
    Ghat r 7 < r + l4Shadow r 8 (Ghat r 8 + 1) := by
  rw [reverse_shadow_8 r hr]
  simp [Ghat]
  norm_num [Nat.choose]
  omega

private theorem canonical_seven
    {k a b c d e f g : ℕ}
    (hk : 7 ≤ k)
    (ha : k ≤ a) (hb : k - 1 ≤ b) (hc : k - 2 ≤ c)
    (hd : k - 3 ≤ d) (he : k - 4 ≤ e) (hf : k - 5 ≤ f)
    (hg : k - 6 ≤ g)
    (hab : b < a) (hbc : c < b) (hcd : d < c)
    (hde : e < d) (hef : f < e) (hfg : g < f) :
    IsCanonical k [a, b, c, d, e, f, g] := by
  apply (isCanonical_cons_of_pos (by omega)).2
  refine ⟨ha, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 1)).2
  refine ⟨hb, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 2)).2
  refine ⟨hc, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 3)).2
  refine ⟨hd, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 4)).2
  refine ⟨he, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 5)).2
  refine ⟨hf, by simpa, ?_⟩
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 6)).2
  exact ⟨hg, by simp, by simp⟩

private theorem reverse_shadow_9_28
    (r i : ℕ) (hr : 29 ≤ r) (hi9 : 9 ≤ i) (hi28 : i ≤ 28) :
    l4Shadow r i (Ghat r i + 1) =
      (r + 2).choose (i - 1) + r.choose (i - 2) +
        (r - 2).choose (i - 3) + (r - 4).choose (i - 4) +
        (r - 5).choose (i - 5) + (23 : ℕ).choose (i - 6) + (i - 6) := by
  have hcanon :
      IsCanonical i [r + 2, r, r - 2, r - 4, r - 5, 23, i - 6] := by
    apply canonical_seven (by omega) <;> omega
  have hlast : (i - 6).choose (i - 7) = i - 6 := by
    simpa only [show i - 6 - 1 = i - 7 by omega, Nat.choose_one_right] using
      (Nat.choose_symm (n := i - 6) (k := 1) (by omega))
  apply l4Shadow_eval (a := r + 2)
      (digits := [r, r - 2, r - 4, r - 5, 23, i - 6])
  · exact hcanon
  · omega
  · simp only [cascadeValue_cons, cascadeValue_nil]
    simp only [Ghat, if_neg (show i ≠ 2 by omega), if_neg (show i ≠ 3 by omega),
      if_neg (show i ≠ 4 by omega), if_neg (show i ≠ 5 by omega),
      if_neg (show i ≠ 6 by omega), if_neg (show i ≠ 7 by omega)]
    rw [show i - 1 - 1 = i - 2 by omega,
      show i - 2 - 1 = i - 3 by omega,
      show i - 3 - 1 = i - 4 by omega,
      show i - 4 - 1 = i - 5 by omega,
      show i - 5 - 1 = i - 6 by omega,
      Nat.choose_self]
    omega
  · simp only [cascadeShadowValue, cascadeValue_cons, cascadeValue_nil]
    rw [show i - 1 - 1 = i - 2 by omega,
      show i - 2 - 1 = i - 3 by omega,
      show i - 3 - 1 = i - 4 by omega,
      show i - 4 - 1 = i - 5 by omega,
      show i - 5 - 1 = i - 6 by omega,
      show i - 6 - 1 = i - 7 by omega, hlast]
    omega

private theorem reverse_step_9_28
    (r i : ℕ) (hr : 29 ≤ r) (hi9 : 9 ≤ i) (hi28 : i ≤ 28) :
    Ghat r (i - 1) < r + l4Shadow r i (Ghat r i + 1) := by
  rw [reverse_shadow_9_28 r i hr hi9 hi28]
  simp only [Ghat, if_neg (show i - 1 ≠ 2 by omega),
    if_neg (show i - 1 ≠ 3 by omega), if_neg (show i - 1 ≠ 4 by omega),
    if_neg (show i - 1 ≠ 5 by omega), if_neg (show i - 1 ≠ 6 by omega),
    if_neg (show i - 1 ≠ 7 by omega)]
  rw [show i - 1 - 1 = i - 2 by omega,
    show i - 1 - 2 = i - 3 by omega,
    show i - 1 - 3 = i - 4 by omega,
    show i - 1 - 4 = i - 5 by omega,
    show i - 1 - 5 = i - 6 by omega]
  omega

private theorem canonical_six
    {k a b c d e f : ℕ}
    (hk : 6 ≤ k)
    (ha : k ≤ a) (hb : k - 1 ≤ b) (hc : k - 2 ≤ c)
    (hd : k - 3 ≤ d) (he : k - 4 ≤ e) (hf : k - 5 ≤ f)
    (hab : b < a) (hbc : c < b) (hcd : d < c)
    (hde : e < d) (hef : f < e) :
    IsCanonical k [a, b, c, d, e, f] := by
  apply (isCanonical_cons_of_pos (by omega)).2
  refine ⟨ha, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 1)).2
  refine ⟨hb, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 2)).2
  refine ⟨hc, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 3)).2
  refine ⟨hd, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 4)).2
  refine ⟨he, by simpa, ?_⟩
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 5)).2
  exact ⟨hf, by simp, by simp⟩

private theorem reverse_shadow_29 (r : ℕ) (hr : 31 ≤ r) :
    l4Shadow r 29 (Ghat r 29 + 1) =
      (r + 2).choose 28 + r.choose 27 + (r - 2).choose 26 +
        (r - 4).choose 25 + (r - 5).choose 24 + 24 := by
  have hcanon : IsCanonical 29 [r + 2, r, r - 2, r - 4, r - 5, 24] := by
    apply canonical_six <;> omega
  have hlast : (24 : ℕ).choose 23 = 24 := by
    norm_num [Nat.choose]
  apply l4Shadow_eval (a := r + 2)
      (digits := [r, r - 2, r - 4, r - 5, 24])
  · exact hcanon
  · omega
  · simp only [cascadeValue_cons, cascadeValue_nil]
    simp only [Ghat, if_neg (by decide : 29 ≠ 2), if_neg (by decide : 29 ≠ 3),
      if_neg (by decide : 29 ≠ 4), if_neg (by decide : 29 ≠ 5),
      if_neg (by decide : 29 ≠ 6), if_neg (by decide : 29 ≠ 7)]
    norm_num [Nat.choose]
    omega
  · simp only [cascadeShadowValue, cascadeValue_cons, cascadeValue_nil]
    norm_num [Nat.choose]
    omega

private theorem reverse_step_29 (r : ℕ) (hr : 31 ≤ r) :
    Ghat r 28 < r + l4Shadow r 29 (Ghat r 29 + 1) := by
  rw [reverse_shadow_29 r hr]
  norm_num [Ghat, Nat.choose]
  omega

private theorem reverse_shadow_ge_30
    (r i : ℕ) (hi : 30 ≤ i) (hir : i ≤ r - 2) :
    l4Shadow r i (Ghat r i + 1) =
      (r + 2).choose (i - 1) + r.choose (i - 2) +
        (r - 2).choose (i - 3) + (r - 4).choose (i - 4) +
        (r - 5).choose (i - 5) + (i - 5) := by
  have hcanon :
      IsCanonical i [r + 2, r, r - 2, r - 4, r - 5, i - 5] := by
    apply canonical_six <;> omega
  have hlast : (i - 5).choose (i - 6) = i - 5 := by
    simpa only [show i - 5 - 1 = i - 6 by omega, Nat.choose_one_right] using
      (Nat.choose_symm (n := i - 5) (k := 1) (by omega))
  have hzero : (23 : ℕ).choose (i - 5) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  apply l4Shadow_eval (a := r + 2)
      (digits := [r, r - 2, r - 4, r - 5, i - 5])
  · exact hcanon
  · omega
  · simp only [cascadeValue_cons, cascadeValue_nil]
    simp only [Ghat, if_neg (show i ≠ 2 by omega), if_neg (show i ≠ 3 by omega),
      if_neg (show i ≠ 4 by omega), if_neg (show i ≠ 5 by omega),
      if_neg (show i ≠ 6 by omega), if_neg (show i ≠ 7 by omega)]
    rw [show i - 1 - 1 = i - 2 by omega,
      show i - 2 - 1 = i - 3 by omega,
      show i - 3 - 1 = i - 4 by omega,
      show i - 4 - 1 = i - 5 by omega,
      Nat.choose_self, hzero]
    omega
  · simp only [cascadeShadowValue, cascadeValue_cons, cascadeValue_nil]
    rw [show i - 1 - 1 = i - 2 by omega,
      show i - 2 - 1 = i - 3 by omega,
      show i - 3 - 1 = i - 4 by omega,
      show i - 4 - 1 = i - 5 by omega,
      show i - 5 - 1 = i - 6 by omega, hlast]
    omega

private theorem reverse_step_ge_30
    (r i : ℕ) (hi : 30 ≤ i) (hir : i ≤ r - 2) :
    Ghat r (i - 1) < r + l4Shadow r i (Ghat r i + 1) := by
  rw [reverse_shadow_ge_30 r i hi hir]
  have hzero : (23 : ℕ).choose (i - 6) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  simp only [Ghat, if_neg (show i - 1 ≠ 2 by omega),
    if_neg (show i - 1 ≠ 3 by omega), if_neg (show i - 1 ≠ 4 by omega),
    if_neg (show i - 1 ≠ 5 by omega), if_neg (show i - 1 ≠ 6 by omega),
    if_neg (show i - 1 ≠ 7 by omega)]
  rw [show i - 1 - 1 = i - 2 by omega,
    show i - 1 - 2 = i - 3 by omega,
    show i - 1 - 3 = i - 4 by omega,
    show i - 1 - 4 = i - 5 by omega,
    show i - 1 - 5 = i - 6 by omega, hzero]
  omega

/-- Every reverse-step inequality in Lemma RS for the concrete shadow. -/
theorem l4_reverseSteps (r : ℕ) (hr : 29 ≤ r) :
    ReverseSteps (l4Shadow r) r := by
  intro i hi hir
  by_cases hi8 : i ≤ 8
  · have hcases : i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact reverse_step_3 r hr
    · exact reverse_step_4 r hr
    · exact reverse_step_5 r hr
    · exact reverse_step_6 r hr
    · exact reverse_step_7 r hr
    · exact reverse_step_8 r hr
  · have hi9 : 9 ≤ i := by omega
    by_cases hi28 : i ≤ 28
    · exact reverse_step_9_28 r i hr hi9 hi28
    · by_cases hi29 : i = 29
      · subst i
        exact reverse_step_29 r (by omega)
      · exact reverse_step_ge_30 r i (by omega) hir

/--
The fully concrete recurrence form of L4.  All monotonicity, reverse-step and
top-step premises of `not_l4_chain` have now been discharged.
-/
theorem l4_no_recurrence (r : ℕ) (hr : 29 ≤ r) :
    ¬ ∃ c : ℕ → ℕ,
      IsL4Chain (l4Shadow r) r c ∧
      c 2 ≤ (r + 4).choose 2 :=
  not_l4_chain (l4Shadow r) r hr (l4Shadow_mono r)
    (l4_reverseSteps r hr) (l4_topStepIdentities r hr)

end Erdos776.L4
