import Erdos524.LaplaceKernelComparison
import Erdos524.PSDTracePerturbation
import Erdos524.CauchyPositivity
import Erdos524.SeparatedGridInverse

/-! Exact finite-interval cutoff error and its controlled relative PSD size. -/

namespace Erdos524.FiniteKernelPerturbation

open Matrix
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator
open Erdos524.CauchyKernel Erdos524.LaplaceKernelComparison Erdos524.PSDTracePerturbation

variable {n : ℕ}

noncomputable def normalizedFiniteKernel (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i ↦ Real.sqrt (u i)) * finiteKernel u * diagonal (fun i ↦ Real.sqrt (u i))

noncomputable def cutoffError (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i ↦ Real.exp (-u i)) * normalized u * diagonal (fun i ↦ Real.exp (-u i))

theorem normalizedFiniteKernel_eq_sub (u : Fin n → ℝ) (hu : ∀ i, 0 < u i) :
    normalizedFiniteKernel u = normalized u - cutoffError u := by
  ext i j
  simp only [normalizedFiniteKernel, cutoffError, Matrix.sub_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [finiteKernel_apply, if_neg (ne_of_gt (add_pos (hu i) (hu j)))]
  have he : Real.exp (-(u i + u j)) = Real.exp (-u i) * Real.exp (-u j) := by
    rw [show -(u i + u j) = -u i + -u j by ring, Real.exp_add]
  rw [he]
  unfold normalized
  ring

theorem cutoffError_posSemidef (u : Fin n → ℝ) (hu : ∀ i, 0 < u i) :
    (cutoffError u).PosSemidef := by
  simpa only [cutoffError, Matrix.diagonal_conjTranspose, star_trivial] using
    (posSemidef_normalized_fin u hu).conjTranspose_mul_mul_same
      (diagonal (fun i ↦ Real.exp (-u i)))

theorem normalized_diagonal (u : Fin n → ℝ) (hu : ∀ i, 0 < u i) (i : Fin n) :
    normalized u i i = (1 / 2 : ℝ) := by
  have hsum : u i + u i ≠ 0 := by linarith [hu i]
  have hu0 : u i ≠ 0 := ne_of_gt (hu i)
  have hs := Real.sq_sqrt (hu i).le
  unfold normalized
  field_simp [hu0]
  nlinarith

theorem cutoffError_diagonal (u : Fin n → ℝ) (hu : ∀ i, 0 < u i) (i : Fin n) :
    cutoffError u i i = Real.exp (-2 * u i) / 2 := by
  simp only [cutoffError, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [normalized_diagonal u hu i]
  have he : (Real.exp (-u i)) ^ 2 = Real.exp (-2 * u i) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-u i) * (1 / 2) * Real.exp (-u i) = (Real.exp (-u i)) ^ 2 / 2 := by ring
    _ = _ := by rw [he]

theorem cutoffError_diagonal_le (u : Fin n → ℝ) (hu : ∀ i, 0 < u i)
    (v : ℝ) (hmin : ∀ i, v ≤ u i) (i : Fin n) :
    cutoffError u i i ≤ Real.exp (-2 * v) / 2 := by
  rw [cutoffError_diagonal u hu i]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Real.exp_le_exp.mpr (by linarith [hmin i])

theorem normalizedFiniteKernel_half_gap (u : Fin (n + 1) → ℝ)
    (hu : ∀ i, 0 < u i) (hinj : Function.Injective u)
    (v : ℝ) (hmin : ∀ i, v ≤ u i)
    (hbudget : (n + 1 : ℝ) * Real.exp (-2 * v) * (normalized u)⁻¹.trace ≤ 1) :
    (normalizedFiniteKernel u - (1 / 2 : ℝ) • normalized u).PosSemidef := by
  have hb : (n + 1 : ℝ) * (Real.exp (-2 * v) / 2) * (normalized u)⁻¹.trace ≤ 1 / 2 := by
    nlinarith [hbudget]
  have h := half_gap_of_diagonal_bound (posDef_normalized_fin u hu hinj)
    (cutoffError_posSemidef u hu) (Real.exp (-2 * v) / 2)
    (cutoffError_diagonal_le u hu v hmin) hb
  rw [← normalizedFiniteKernel_eq_sub u hu] at h
  exact h

theorem separated_normalizedFiniteKernel_half_gap (t : Fin (n + 1) → ℝ)
    {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j : Fin (n + 1), i < j → ((j : ℝ) - (i : ℝ)) / r ≤ t j - t i)
    (v : ℝ) (hmin : ∀ i, v ≤ Real.exp (t i))
    (hsmall : 2 * (n + 1 : ℝ) ^ 2 * Real.exp (r * Real.pi ^ 2 - 2 * v) ≤ 1) :
    (normalizedFiniteKernel (fun i ↦ Real.exp (t i)) -
      (1 / 2 : ℝ) • normalized (fun i ↦ Real.exp (t i))).PosSemidef := by
  have ht := separated_inverse_trace_le t hr hsep
  have hprod := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ (n + 1 : ℝ) * Real.exp (-2 * v) by positivity)
  have he : ((n + 1 : ℝ) * Real.exp (-2 * v)) *
      ((n + 1 : ℝ) * 2 * Real.exp (r * Real.pi ^ 2)) =
        2 * (n + 1 : ℝ) ^ 2 * Real.exp (r * Real.pi ^ 2 - 2 * v) := by
    rw [show r * Real.pi ^ 2 - 2 * v = r * Real.pi ^ 2 + (-2 * v) by ring, Real.exp_add]
    ring
  rw [he] at hprod
  exact normalizedFiniteKernel_half_gap _ (fun i ↦ Real.exp_pos _)
    (Real.exp_injective.comp (separated_grid_strictMono t hr hsep).injective)
    v hmin (hprod.trans hsmall)

end Erdos524.FiniteKernelPerturbation
