import Erdos524.GaussianLinearLaw

/-! Sample regression covariance algebra and Schur-complement positivity. -/

namespace Erdos524.GaussianSampleCovariance

open Matrix
open scoped BigOperators

variable {n m : ℕ}

noncomputable def sampleCovariance (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m) := C.submatrix e e
noncomputable def crossCovariance (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m) := C.submatrix id e
noncomputable def predictorWeights (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m) :=
  crossCovariance C e * (sampleCovariance C e)⁻¹
noncomputable def predictorCovariance (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m) :=
  crossCovariance C e * (sampleCovariance C e)⁻¹ * (crossCovariance C e)ᵀ
noncomputable def residualCovariance (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m) :=
  C - predictorCovariance C e

theorem predictor_mul_sample (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m)
    (hA : (sampleCovariance C e).PosDef) :
    predictorWeights C e * sampleCovariance C e = crossCovariance C e := by
  exact Matrix.nonsing_inv_mul_cancel_right (sampleCovariance C e) (crossCovariance C e)
    (isUnit_iff_ne_zero.mpr hA.det_pos.ne')

theorem predictor_at_sample (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m)
    (hA : (sampleCovariance C e).PosDef) (i j : Fin n) :
    predictorWeights C e (e i) j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M i j)
    (Matrix.mul_nonsing_inv (sampleCovariance C e) (isUnit_iff_ne_zero.mpr hA.det_pos.ne'))
  exact h

theorem predictor_normal_equations {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (e : Fin n → Fin m) (hA : (sampleCovariance C e).PosDef) (i : Fin n) (j : Fin m) :
    C (e i) j = ∑ k, predictorWeights C e j k * C (e i) (e k) := by
  have hsym (a b : Fin m) : C a b = C b a :=
    congrArg (fun M : Matrix (Fin m) (Fin m) ℝ ↦ M b a) hC.isHermitian.isSymm
  have h := congrArg (fun M : Matrix (Fin m) (Fin n) ℝ ↦ M j i) (predictor_mul_sample C e hA)
  calc
    C (e i) j = C j (e i) := hsym _ _
    _ = ∑ k, predictorWeights C e j k * C (e k) (e i) := h.symm
    _ = _ := Finset.sum_congr rfl (fun k _ ↦ by rw [hsym (e k) (e i)])

theorem predictorCovariance_posSemidef (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m)
    (hA : (sampleCovariance C e).PosDef) : (predictorCovariance C e).PosSemidef := by
  have h := hA.inv.posSemidef.mul_mul_conjTranspose_same (crossCovariance C e)
  have he : (crossCovariance C e)ᴴ = (crossCovariance C e)ᵀ := by ext i j; simp
  rw [he] at h
  exact h

theorem residualCovariance_posSemidef {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (e : Fin n → Fin m) (hA : (sampleCovariance C e).PosDef) :
    (residualCovariance C e).PosSemidef := by
  letI := invertibleOfIsUnitDet (sampleCovariance C e) (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hsym (a b : Fin m) : C a b = C b a :=
    congrArg (fun M : Matrix (Fin m) (Fin m) ℝ ↦ M b a) hC.isHermitian.isSymm
  have he : C.submatrix (Sum.elim e id) (Sum.elim e id) =
      fromBlocks (sampleCovariance C e) (crossCovariance C e)ᵀ (crossCovariance C e) C := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.submatrix, Matrix.fromBlocks, sampleCovariance, crossCovariance, hsym]
  have hb := hC.submatrix (Sum.elim e id)
  rw [he] at hb
  have hc : ((crossCovariance C e)ᵀ)ᴴ = crossCovariance C e := by ext i j; simp
  have hb' : (fromBlocks (sampleCovariance C e) (crossCovariance C e)ᵀ
      ((crossCovariance C e)ᵀ)ᴴ C).PosSemidef := by rwa [hc]
  have h := (Matrix.PosDef.fromBlocks₁₁ (crossCovariance C e)ᵀ C hA).mp hb'
  rw [hc] at h
  exact h

theorem predictor_covariance_identity (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m)
    (hA : (sampleCovariance C e).PosDef) :
    predictorWeights C e * sampleCovariance C e * (predictorWeights C e)ᵀ = predictorCovariance C e := by
  rw [predictor_mul_sample C e hA, predictorWeights, Matrix.transpose_mul,
    hA.inv.isHermitian.isSymm, ← Matrix.mul_assoc]
  rfl

theorem predictor_action_at_sample (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m)
    (hA : (sampleCovariance C e).PosDef) (z : Fin n → ℝ) (i : Fin n) :
    (predictorWeights C e *ᵥ z) (e i) = z i := by
  change (∑ k, predictorWeights C e (e i) k * z k) = z i
  simp_rw [predictor_at_sample C e hA i]
  exact congrFun (Matrix.one_mulVec z) i

end Erdos524.GaussianSampleCovariance
