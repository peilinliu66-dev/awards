import Erdos776.Combinatorics.NormalShadow

/-!
# Diagonal cascade transfer

This file proves identity (16.1) of `UNIFORM_THEOREM.md`.  A diagonal run of
binomial digits can be placed above an arbitrary canonical tail; one shadow
step lowers the shell and applies the ordinary canonical shadow to the tail.
-/

namespace Erdos776.KruskalKatona

@[simp] theorem length_diagonalDigits (a len : ℕ) :
    (diagonalDigits a len).length = len := by
  induction len generalizing a with
  | zero => rfl
  | succ len ih =>
      simp [diagonalDigits, ih]

theorem choose_diagonal_mono (A b t : ℕ) :
    A.choose b ≤ (A + t).choose (b + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hp := Nat.choose_succ_succ (A + t) (b + t)
      rw [show A + (t + 1) = A + t + 1 by omega,
        show b + (t + 1) = b + t + 1 by omega, hp]
      omega

/-- The value of the diagonal shell before attaching its residual tail. -/
theorem cascadeValue_diagonal_shell (A b t : ℕ) :
    cascadeValue (b + t) (diagonalDigits (A + t - 1) t) =
      (A + t).choose (b + t) - A.choose b := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hAt : A + (t + 1) - 1 = A + t := by omega
      rw [hAt, diagonalDigits_succ, cascadeValue_cons,
        show b + (t + 1) - 1 = b + t by omega, ih]
      have hp := Nat.choose_succ_succ (A + t) (b + t)
      rw [show A + (t + 1) = A + t + 1 by omega,
        show b + (t + 1) = b + t + 1 by omega, hp]
      have hmono := choose_diagonal_mono A b t
      simp only [Nat.succ_eq_add_one]
      omega

/-- The same shell after lowering every lower binomial index once. -/
theorem cascadeValue_diagonal_shell_shadow
    (A b t : ℕ) (hb : 1 ≤ b) :
    cascadeValue (b + t - 1) (diagonalDigits (A + t - 1) t) =
      (A + t).choose (b + t - 1) - A.choose (b - 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hAt : A + (t + 1) - 1 = A + t := by omega
      rw [hAt, diagonalDigits_succ, cascadeValue_cons,
        show b + (t + 1) - 1 - 1 = b + t - 1 by omega, ih]
      have hp : (A + t + 1).choose (b + t) =
          (A + t).choose (b + t - 1) + (A + t).choose (b + t) := by
        simpa only [Nat.succ_eq_add_one,
          show b + t - 1 + 1 = b + t by omega] using
            Nat.choose_succ_succ (A + t) (b + t - 1)
      rw [show A + (t + 1) = A + t + 1 by omega,
        show b + (t + 1) - 1 = b + t by omega, hp]
      have hmono : A.choose (b - 1) ≤
          (A + t).choose (b + t - 1) := by
        simpa [show b - 1 + t = b + t - 1 by omega] using
          choose_diagonal_mono A (b - 1) t
      omega

/-- The explicit canonical digits for the transferred shell and residual. -/
def transferDigits (A b t x : ℕ) : List ℕ :=
  diagonalDigits (A + t - 1) t ++ canonicalDigits b x

theorem cascadeValue_transferDigits
    (A b t x : ℕ) (hb : 1 ≤ b) :
    cascadeValue (b + t) (transferDigits A b t x) =
      (A + t).choose (b + t) - A.choose b + x := by
  rw [transferDigits, cascadeValue_append, length_diagonalDigits,
    show b + t - t = b by omega, cascadeValue_diagonal_shell,
    cascadeValue_canonicalDigits hb]

theorem cascadeShadowValue_transferDigits
    (A b t x : ℕ) (hb : 1 ≤ b) :
    cascadeShadowValue (b + t) (transferDigits A b t x) =
      (A + t).choose (b + t - 1) - A.choose (b - 1) +
        canonicalShadow b x := by
  unfold cascadeShadowValue canonicalShadow transferDigits
  rw [cascadeValue_append, length_diagonalDigits,
    show b + t - 1 - t = b - 1 by omega,
    cascadeValue_diagonal_shell_shadow A b t hb]
  rfl

theorem isCanonical_transferDigits
    {A b t x : ℕ} (hb : 1 ≤ b) (hbA : b < A)
    (hx : x < A.choose b) :
    IsCanonical (b + t) (transferDigits A b t x) := by
  induction t with
  | zero =>
      simpa [transferDigits] using isCanonical_canonicalDigits hb
  | succ t ih =>
      have hAt : A + (t + 1) - 1 = A + t := by omega
      rw [transferDigits, hAt, diagonalDigits_succ, List.cons_append]
      rw [show b + (t + 1) = (b + t) + 1 by omega,
        isCanonical_succ_cons]
      refine ⟨by omega, ?_, ?_⟩
      · intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · exact (mem_diagonalDigits_le hd).trans_lt (by omega)
        · exact (canonicalDigits_all_lt hb hx d hd).trans_le (by omega)
      · simpa [transferDigits] using ih

/--
**Diagonal transfer identity (16.1).**  The strict residual bound prevents a
carry into the diagonal shell, so shadowing acts independently on the shell
and residual cascade.
-/
theorem canonicalShadow_diagonal_transfer
    {A b t x : ℕ} (hb : 1 ≤ b) (hbA : b < A)
    (hx : x < A.choose b) :
    canonicalShadow (b + t)
        ((A + t).choose (b + t) - A.choose b + x) =
      (A + t).choose (b + t - 1) - A.choose (b - 1) +
        canonicalShadow b x := by
  let digits := transferDigits A b t x
  have hcanon : IsCanonical (b + t) digits :=
    isCanonical_transferDigits hb hbA hx
  have hvalue : cascadeValue (b + t) digits =
      (A + t).choose (b + t) - A.choose b + x :=
    cascadeValue_transferDigits A b t x hb
  have hnormal : canonicalDigits (b + t)
      ((A + t).choose (b + t) - A.choose b + x) = digits :=
    (canonicalDigits_unique hcanon hvalue).symm
  rw [canonicalShadow, hnormal]
  exact cascadeShadowValue_transferDigits A b t x hb

/-- Peel one complete binomial shell followed by a subcritical residual. -/
theorem canonicalShadow_add_shell
    {B k x : ℕ} (hk : 2 ≤ k) (hkB : k ≤ B)
    (hx : x < B.choose (k - 1)) :
    canonicalShadow k (B.choose k + x) =
      B.choose (k - 1) + canonicalShadow (k - 1) x := by
  have htransfer := canonicalShadow_diagonal_transfer
    (A := B) (b := k - 1) (t := 1) (x := x)
    (by omega) (by omega) hx
  have hpIn : (B + 1).choose k =
      B.choose (k - 1) + B.choose k := by
    simpa only [Nat.succ_eq_add_one, show k - 1 + 1 = k by omega] using
      Nat.choose_succ_succ B (k - 1)
  have hpOut : (B + 1).choose (k - 1) =
      B.choose (k - 2) + B.choose (k - 1) := by
    simpa only [Nat.succ_eq_add_one,
      show k - 2 + 1 = k - 1 by omega] using
      Nat.choose_succ_succ B (k - 2)
  have harg : (B + 1).choose k - B.choose (k - 1) + x =
      B.choose k + x := by omega
  have hout : (B + 1).choose (k - 1) - B.choose (k - 2) =
      B.choose (k - 1) := by omega
  simpa only [show k - 1 + 1 = k by omega,
    show k - 1 - 1 = k - 2 by omega, harg, hout] using htransfer

end Erdos776.KruskalKatona
