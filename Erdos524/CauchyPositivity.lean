import Erdos524.CauchyKernel
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-! Positive semidefiniteness of the Cauchy covariance, proved by finite
Schur induction. Distinct parameters then give positive definiteness through
the already proved nonzero determinant. -/

namespace Erdos524.CauchyKernel

open Matrix
open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem posSemidef_cauchy_sum_unit (z : ℝ) (x : ι → ℝ)
    (hz : 0 < z) (hx : ∀ i, 0 < x i) (hD : (cauchy x).PosSemidef) :
    (cauchy (Sum.elim (fun _ : Unit ↦ z) x)).PosSemidef := by
  let A : Matrix Unit Unit ℝ := fun _ _ ↦ 1 / (z + z)
  let B : Matrix Unit ι ℝ := fun _ j ↦ 1 / (z + x j)
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
  have hAdiag : A = diagonal (fun _ : Unit ↦ 1 / (z + z)) := by
    ext i j
    simp [A, Matrix.diagonal]
  have hA : A.PosDef := by
    rw [hAdiag]
    exact Matrix.PosDef.diagonal fun _ ↦ one_div_pos.mpr (add_pos hz hz)
  have hblocks : cauchy (Sum.elim (fun _ : Unit ↦ z) x) =
      Matrix.fromBlocks A B Bᴴ D := by
    ext i j
    cases i <;> cases j <;>
      simp [cauchy, A, B, D, Matrix.fromBlocks, Matrix.conjTranspose, Matrix.transpose, add_comm]
  have hschur : D - Bᴴ * A⁻¹ * B = diagonal d * D * diagonal d := by
    rw [← Matrix.invOf_eq_nonsing_inv, hinv]
    ext i j
    simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    change 1 / (x i + x j) -
      (∑ _ : Unit, (∑ _ : Unit, (1 / (z + x i)) * (z + z)) * (1 / (z + x j))) =
        ((x i - z) / (x i + z)) * (1 / (x i + x j)) * ((x j - z) / (x j + z))
    simp only [Fintype.sum_unique]
    simpa only [add_comm] using schur_entry (x i) (x j) z (hx i) (hx j) hz
  have hs : (D - Bᴴ * A⁻¹ * B).PosSemidef := by
    rw [hschur]
    simpa only [Matrix.diagonal_conjTranspose, star_trivial] using
      hD.conjTranspose_mul_mul_same (diagonal d)
  rw [hblocks]
  exact (Matrix.PosDef.fromBlocks₁₁ B D hA).mpr hs

theorem posSemidef_cauchy_fin {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) : (cauchy x).PosSemidef := by
  induction n with
  | zero =>
    have he : cauchy x = (0 : Matrix (Fin 0) (Fin 0) ℝ) := Subsingleton.elim _ _
    rw [he]
    exact Matrix.PosSemidef.zero
  | succ n ih =>
    have h := posSemidef_cauchy_sum_unit (x 0) (fun i : Fin n ↦ x i.succ)
      (hx 0) (fun i ↦ hx i.succ) (ih _ (fun i ↦ hx i.succ))
    have he : cauchy (Sum.elim (fun _ : Unit ↦ x 0) (fun i : Fin n ↦ x i.succ)) =
        (cauchy x).submatrix (headEquiv n) (headEquiv n) := by
      ext i j
      cases i <;> cases j <;> rfl
    rw [he] at h
    exact (Matrix.posSemidef_submatrix_equiv (headEquiv n)).mp h

theorem posDef_cauchy_fin {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) : (cauchy x).PosDef :=
  (posSemidef_cauchy_fin x hx).posDef_iff_det_ne_zero.mpr
    (det_cauchy_fin_pos x hx hinj).ne'

theorem posSemidef_normalized_fin {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) : (normalized x).PosSemidef := by
  rw [normalized_eq_diagonal]
  simpa only [Matrix.diagonal_conjTranspose, star_trivial] using
    (posSemidef_cauchy_fin x hx).conjTranspose_mul_mul_same
      (diagonal (fun i ↦ Real.sqrt (x i)))

theorem posDef_normalized_fin {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) : (normalized x).PosDef :=
  (posSemidef_normalized_fin x hx).posDef_iff_det_ne_zero.mpr
    (det_normalized_fin_pos x hx hinj).ne'

end Erdos524.CauchyKernel
