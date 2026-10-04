import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
Finite algebra for the positive Cauchy kernel. The determinant recursion is
proved by a one-coordinate Schur complement; no determinant identity is assumed.
-/

namespace Erdos524.CauchyKernel

open Matrix
open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def cauchy (x : ι → ℝ) : Matrix ι ι ℝ := fun i j ↦ 1 / (x i + x j)

theorem schur_entry (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    1 / (x + y) - (1 / (x + z)) * (z + z) * (1 / (z + y)) =
      ((x - z) / (x + z)) * (1 / (x + y)) * ((y - z) / (y + z)) := by
  have hxy : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have hxz : x + z ≠ 0 := ne_of_gt (add_pos hx hz)
  have hzy : z + y ≠ 0 := ne_of_gt (add_pos hz hy)
  have hyz : y + z ≠ 0 := ne_of_gt (add_pos hy hz)
  field_simp
  <;> ring

/-- Adding one positive kernel parameter multiplies the determinant by a
pivot and the square of its Cauchy elimination factors. Distinctness is not
needed: repeated parameters correctly give a zero determinant. -/
theorem det_cauchy_sum_unit (z : ℝ) (x : ι → ℝ)
    (hz : 0 < z) (hx : ∀ i, 0 < x i) :
    (cauchy (Sum.elim (fun _ : Unit ↦ z) x)).det =
      (1 / (z + z)) * (∏ i, (x i - z) / (x i + z)) ^ 2 * (cauchy x).det := by
  let A : Matrix Unit Unit ℝ := fun _ _ ↦ 1 / (z + z)
  let B : Matrix Unit ι ℝ := fun _ j ↦ 1 / (z + x j)
  let C : Matrix ι Unit ℝ := fun i _ ↦ 1 / (x i + z)
  let D : Matrix ι ι ℝ := cauchy x
  let d : ι → ℝ := fun i ↦ (x i - z) / (x i + z)
  have hzz : z + z ≠ 0 := ne_of_gt (add_pos hz hz)
  letI : Invertible A := {
    invOf := fun _ _ ↦ z + z
    invOf_mul_self := by
      ext i j
      change (∑ _ : Unit, (z + z) * (1 / (z + z))) = (1 : Matrix Unit Unit ℝ) i j
      simp [hzz]
    mul_invOf_self := by
      ext i j
      change (∑ _ : Unit, (1 / (z + z)) * (z + z)) = (1 : Matrix Unit Unit ℝ) i j
      simp [hzz]
  }
  have hinv : (⅟A : Matrix Unit Unit ℝ) = fun _ _ ↦ z + z := rfl
  have hblocks : cauchy (Sum.elim (fun _ : Unit ↦ z) x) =
      Matrix.fromBlocks A B C D := by
    ext i j
    cases i <;> cases j <;> rfl
  have hschur : D - C * ⅟A * B = diagonal d * D * diagonal d := by
    rw [hinv]
    ext i j
    simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    change 1 / (x i + x j) -
      (∑ _ : Unit, (∑ _ : Unit, (1 / (x i + z)) * (z + z)) * (1 / (z + x j))) =
        ((x i - z) / (x i + z)) * (1 / (x i + x j)) * ((x j - z) / (x j + z))
    simp only [Fintype.sum_unique]
    exact schur_entry (x i) (x j) z (hx i) (hx j) hz
  rw [hblocks, Matrix.det_fromBlocks₁₁, hschur, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_unique]
  change (1 / (z + z)) * ((∏ i, d i) * (cauchy x).det * (∏ i, d i)) = _
  dsimp [d]
  ring

def headEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ ↦ 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv := by
    intro i
    cases i with
    | inl u => cases u; rfl
    | inr j => rfl
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl

theorem det_cauchy_fin_succ {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 < x i) :
    (cauchy x).det =
      (1 / (x 0 + x 0)) * (∏ i : Fin n, (x i.succ - x 0) / (x i.succ + x 0)) ^ 2 *
        (cauchy (fun i : Fin n ↦ x i.succ)).det := by
  have h := det_cauchy_sum_unit (x 0) (fun i : Fin n ↦ x i.succ)
    (hx 0) (fun i ↦ hx i.succ)
  have he : cauchy (Sum.elim (fun _ : Unit ↦ x 0) (fun i : Fin n ↦ x i.succ)) =
      (cauchy x).submatrix (headEquiv n) (headEquiv n) := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [he, Matrix.det_submatrix_equiv_self] at h
  exact h

/-- The complete finite symmetric Cauchy determinant formula. -/
theorem det_cauchy_fin {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    (cauchy x).det = (∏ i, 1 / (x i + x i)) *
      ∏ i, ∏ j, if i < j then ((x j - x i) / (x j + x i)) ^ 2 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [det_cauchy_fin_succ x hx, ih (fun i ↦ x i.succ) (fun i ↦ hx i.succ)]
    simp only [Fin.prod_univ_succ, Fin.succ_pos, ite_true, Fin.not_lt_zero,
      ite_false, Fin.succ_lt_succ_iff, one_mul]
    rw [Finset.prod_pow]
    ring

theorem det_cauchy_fin_pos {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) : 0 < (cauchy x).det := by
  rw [det_cauchy_fin x hx]
  apply mul_pos
  · exact Finset.prod_pos fun i _ ↦ one_div_pos.mpr (add_pos (hx i) (hx i))
  · apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j _
    split_ifs with hij
    · apply sq_pos_of_ne_zero
      apply div_ne_zero
      · exact sub_ne_zero.mpr (fun h ↦ (ne_of_gt hij) (hinj h))
      · exact ne_of_gt (add_pos (hx j) (hx i))
    · norm_num

noncomputable def normalized (x : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ Real.sqrt (x i) * (1 / (x i + x j)) * Real.sqrt (x j)

theorem normalized_eq_diagonal (x : ι → ℝ) :
    normalized x = diagonal (fun i ↦ Real.sqrt (x i)) * cauchy x *
      diagonal (fun i ↦ Real.sqrt (x i)) := by
  ext i j
  simp [normalized, cauchy]

theorem det_normalized_eq (x : ι → ℝ) :
    (normalized x).det = (∏ i, Real.sqrt (x i)) ^ 2 * (cauchy x).det := by
  rw [normalized_eq_diagonal, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal]
  ring

/-- The normalized covariance has diagonal entries 1/2; its determinant is
the pairwise Cauchy product times 2 to the negative dimension. -/
theorem det_normalized_fin {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    (normalized x).det = (1 / 2 : ℝ) ^ n *
      ∏ i, ∏ j, if i < j then ((x j - x i) / (x j + x i)) ^ 2 else 1 := by
  have hsq : (∏ i, Real.sqrt (x i)) ^ 2 = ∏ i, x i := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    exact Real.sq_sqrt (hx i).le
  have hprod : (∏ i, x i) * (∏ i, 1 / (x i + x i)) = (1 / 2 : ℝ) ^ n := by
    rw [← Finset.prod_mul_distrib]
    have hi (i : Fin n) : x i * (1 / (x i + x i)) = (1 / 2 : ℝ) := by
      have hxi : x i ≠ 0 := ne_of_gt (hx i)
      have hsum : x i + x i ≠ 0 := ne_of_gt (add_pos (hx i) (hx i))
      field_simp
      ring
    simp_rw [hi]
    simp
  rw [det_normalized_eq, hsq, det_cauchy_fin x hx, ← mul_assoc, hprod]

theorem det_normalized_fin_pos {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) :
    0 < (normalized x).det := by
  rw [det_normalized_eq]
  apply mul_pos
  · exact sq_pos_of_pos (Finset.prod_pos fun i _ ↦ Real.sqrt_pos.mpr (hx i))
  · exact det_cauchy_fin_pos x hx hinj

def pivotEquiv {n : ℕ} (i : Fin (n + 1)) : Unit ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ ↦ i) i.succAbove
  invFun := Fin.succAboveCases i (Sum.inl ()) (fun j ↦ Sum.inr j)
  left_inv := by
    intro j
    cases j with
    | inl u => cases u; simp
    | inr k => simp
  right_inv := by
    intro j
    refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j <;> simp

theorem det_cauchy_pivot {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 < x i) (i : Fin (n + 1)) :
    (cauchy x).det = (1 / (x i + x i)) *
      (∏ k : Fin n, (x (i.succAbove k) - x i) / (x (i.succAbove k) + x i)) ^ 2 *
      (cauchy (fun k : Fin n ↦ x (i.succAbove k))).det := by
  have h := det_cauchy_sum_unit (x i) (fun k : Fin n ↦ x (i.succAbove k))
    (hx i) (fun k ↦ hx (i.succAbove k))
  have he : cauchy (Sum.elim (fun _ : Unit ↦ x i)
      (fun k : Fin n ↦ x (i.succAbove k))) =
      (cauchy x).submatrix (pivotEquiv i) (pivotEquiv i) := by
    ext j k
    cases j <;> cases k <;> rfl
  rw [he, Matrix.det_submatrix_equiv_self] at h
  exact h

/-- Exact inverse diagonal, using the same finite pivot factors as the
determinant recursion. -/
theorem inverse_diagonal {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (i : Fin (n + 1)) :
    (cauchy x)⁻¹ i i = (x i + x i) /
      (∏ k : Fin n, (x (i.succAbove k) - x i) / (x (i.succAbove k) + x i)) ^ 2 := by
  have htailinj : Function.Injective (fun k : Fin n ↦ x (i.succAbove k)) := by
    intro j k hjk
    exact i.succAbove_right_injective (hinj hjk)
  have htail : (cauchy (fun k : Fin n ↦ x (i.succAbove k))).det ≠ 0 :=
    (det_cauchy_fin_pos _ (fun k ↦ hx (i.succAbove k)) htailinj).ne'
  have hsum : x i + x i ≠ 0 := ne_of_gt (add_pos (hx i) (hx i))
  have hp : (∏ k : Fin n, (x (i.succAbove k) - x i) /
      (x (i.succAbove k) + x i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact div_ne_zero (sub_ne_zero.mpr (fun h ↦ Fin.succAbove_ne i k (hinj h)))
      (ne_of_gt (add_pos (hx (i.succAbove k)) (hx i)))
  have hsign : (-1 : ℝ) ^ ((i : ℕ) + (i : ℕ)) = 1 := by
    simp [← two_mul, pow_mul]
  have hcofactor : (cauchy x).adjugate i i =
      (cauchy (fun k : Fin n ↦ x (i.succAbove k))).det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, hsign, one_mul]
    rfl
  rw [Matrix.inv_def]
  change Ring.inverse ((cauchy x).det) * (cauchy x).adjugate i i = _
  rw [Ring.inverse_eq_inv, hcofactor, det_cauchy_pivot x hx i]
  field_simp

theorem det_normalized_pivot {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 < x i) (i : Fin (n + 1)) :
    (normalized x).det = (1 / 2 : ℝ) *
      (∏ k : Fin n, (x (i.succAbove k) - x i) / (x (i.succAbove k) + x i)) ^ 2 *
      (normalized (fun k : Fin n ↦ x (i.succAbove k))).det := by
  have hsum : x i + x i ≠ 0 := ne_of_gt (add_pos (hx i) (hx i))
  have hxi : x i ≠ 0 := ne_of_gt (hx i)
  simp only [det_normalized_eq]
  rw [det_cauchy_pivot x hx i,
    Fin.prod_univ_succAbove (fun j ↦ Real.sqrt (x j)) i,
    mul_pow, Real.sq_sqrt (hx i).le]
  field_simp [hxi]
  ring

theorem normalized_inverse_diagonal {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (i : Fin (n + 1)) :
    (normalized x)⁻¹ i i = (2 : ℝ) /
      (∏ k : Fin n, (x (i.succAbove k) - x i) / (x (i.succAbove k) + x i)) ^ 2 := by
  have htailinj : Function.Injective (fun k : Fin n ↦ x (i.succAbove k)) := by
    intro j k hjk
    exact i.succAbove_right_injective (hinj hjk)
  have htail : (normalized (fun k : Fin n ↦ x (i.succAbove k))).det ≠ 0 :=
    (det_normalized_fin_pos _ (fun k ↦ hx (i.succAbove k)) htailinj).ne'
  have hp : (∏ k : Fin n, (x (i.succAbove k) - x i) /
      (x (i.succAbove k) + x i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact div_ne_zero (sub_ne_zero.mpr (fun h ↦ Fin.succAbove_ne i k (hinj h)))
      (ne_of_gt (add_pos (hx (i.succAbove k)) (hx i)))
  have hsign : (-1 : ℝ) ^ ((i : ℕ) + (i : ℕ)) = 1 := by
    simp [← two_mul, pow_mul]
  have hcofactor : (normalized x).adjugate i i =
      (normalized (fun k : Fin n ↦ x (i.succAbove k))).det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, hsign, one_mul]
    rfl
  rw [Matrix.inv_def]
  change Ring.inverse ((normalized x).det) * (normalized x).adjugate i i = _
  rw [Ring.inverse_eq_inv, hcofactor, det_normalized_pivot x hx i]
  field_simp

end Erdos524.CauchyKernel
