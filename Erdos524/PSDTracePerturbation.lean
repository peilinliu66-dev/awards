import Erdos524.GaussianCovarianceCoordinates

/-! Relative PSD perturbation bounds from inverse trace, without eigenvalue estimates. -/

namespace Erdos524.PSDTracePerturbation

open Matrix
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator
open Erdos524.GaussianCovarianceCoordinates Erdos524.GaussianLevelSets

variable {n : ℕ}

theorem energy_mulVec_le_trace_gram (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : Fin (n + 1) → ℝ) : energy (A *ᵥ x) ≤ (Aᵀ * A).trace * energy x := by
  have hrow (i : Fin (n + 1)) :
      (∑ j, A i j * x j) ^ 2 ≤ (∑ j, (A i j) ^ 2) * ∑ j, (x j) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j ↦ A i j) x
  calc
    energy (A *ᵥ x) = ∑ i, (∑ j, A i j * x j) ^ 2 := rfl
    _ ≤ ∑ i, (∑ j, (A i j) ^ 2) * energy x := Finset.sum_le_sum fun i _ ↦ hrow i
    _ = (∑ i, ∑ j, (A i j) ^ 2) * energy x := by rw [Finset.sum_mul]
    _ = (Aᵀ * A).trace * energy x := by
      congr 1
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
      exact Finset.sum_comm

theorem quadratic_le_trace_mul_energy
    {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hS : S.PosSemidef)
    (x : Fin (n + 1) → ℝ) : x ⬝ᵥ S *ᵥ x ≤ S.trace * energy x := by
  let A := CFC.sqrt S
  have hsym : Aᵀ = A := (CFC.sqrt_nonneg S).posSemidef.isHermitian.isSymm
  have hAA : Aᵀ * A = S := by rw [hsym]; exact CFC.sqrt_mul_sqrt_self S hS.nonneg
  have h := energy_mulVec_le_trace_gram A x
  rw [energy_mulVec, hAA] at h
  exact h

theorem energy_sqrt (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hS : S.PosDef)
    (x : Fin (n + 1) → ℝ) : energy (sqrtEquiv S hS x) = x ⬝ᵥ S *ᵥ x := by
  have hsym : (CFC.sqrt S)ᵀ = CFC.sqrt S :=
    (CFC.sqrt_nonneg S).posSemidef.isHermitian.isSymm
  rw [sqrtEquiv, matrixEquiv_apply, energy_mulVec, hsym,
    CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg]

theorem energy_le_inverse_trace_mul_quadratic
    {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hS : S.PosDef)
    (x : Fin (n + 1) → ℝ) : energy x ≤ S⁻¹.trace * (x ⬝ᵥ S *ᵥ x) := by
  have h := quadratic_le_trace_mul_energy hS.posSemidef.inv (sqrtEquiv S hS x)
  rw [← energy_inverse_sqrt S hS, ContinuousLinearEquiv.symm_apply_apply,
    energy_sqrt S hS] at h
  exact h

theorem relative_gap_of_trace_product
    {C E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hC : C.PosDef) (hE : E.PosSemidef) {δ : ℝ}
    (hbudget : E.trace * C⁻¹.trace ≤ δ) : (δ • C - E).PosSemidef := by
  have hherm : (δ • C - E).IsHermitian :=
    (hC.isHermitian.smul (show IsSelfAdjoint δ from by simp [IsSelfAdjoint])).sub hE.isHermitian
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
  intro x
  have hqC : 0 ≤ x ⬝ᵥ C *ᵥ x := by simpa using hC.posSemidef.dotProduct_mulVec_nonneg x
  have hq : x ⬝ᵥ E *ᵥ x ≤ δ * (x ⬝ᵥ C *ᵥ x) := calc
    x ⬝ᵥ E *ᵥ x ≤ E.trace * energy x := quadratic_le_trace_mul_energy hE x
    _ ≤ E.trace * (C⁻¹.trace * (x ⬝ᵥ C *ᵥ x)) :=
      mul_le_mul_of_nonneg_left (energy_le_inverse_trace_mul_quadratic hC x) hE.trace_nonneg
    _ = (E.trace * C⁻¹.trace) * (x ⬝ᵥ C *ᵥ x) := by ring
    _ ≤ δ * (x ⬝ᵥ C *ᵥ x) := mul_le_mul_of_nonneg_right hbudget hqC
  simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul] using sub_nonneg.mpr hq

theorem half_gap_of_diagonal_bound
    {C E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hC : C.PosDef) (hE : E.PosSemidef) (ε : ℝ)
    (hdiag : ∀ i, E i i ≤ ε) (hbudget : (n + 1 : ℝ) * ε * C⁻¹.trace ≤ 1 / 2) :
    (C - E - (1 / 2 : ℝ) • C).PosSemidef := by
  have ht : E.trace ≤ (n + 1 : ℝ) * ε := by
    calc
      E.trace = ∑ i, E i i := rfl
      _ ≤ ∑ _ : Fin (n + 1), ε := Finset.sum_le_sum fun i _ ↦ hdiag i
      _ = _ := by simp
  have hb : E.trace * C⁻¹.trace ≤ (1 / 2 : ℝ) :=
    (mul_le_mul_of_nonneg_right ht hC.posSemidef.inv.trace_nonneg).trans hbudget
  have h := relative_gap_of_trace_product hC hE hb
  convert h using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end Erdos524.PSDTracePerturbation
