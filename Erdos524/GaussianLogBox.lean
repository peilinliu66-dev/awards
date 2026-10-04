import Erdos524.GaussianCovarianceBox

/-! Exact exponential box bounds, retaining the dimensional normalization term. -/

namespace Erdos524.GaussianLogBox

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal BigOperators
open Erdos524.GaussianBoxDensity Erdos524.GaussianCovarianceBox

variable {n : ℕ}

noncomputable def boxExponent (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (y : Fin (n + 1) → ℝ) : ℝ :=
  -(∑ i, y i) - Real.log S.det / 2 +
    (n + 1 : ℝ) * (Real.log 2 - Real.log (Real.sqrt (2 * Real.pi)))

theorem normalization_exp : normalization n =
    ENNReal.ofReal (Real.exp (-((n + 1 : ℝ) * Real.log (Real.sqrt (2 * Real.pi))))) := by
  have hp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  unfold normalization
  congr 1
  rw [Real.exp_neg, show (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) by push_cast; rfl,
    Real.exp_nat_mul, Real.exp_log hp, inv_pow]

theorem inverse_sqrt_exp {d : ℝ} (hd : 0 < d) :
    1 / Real.sqrt d = Real.exp (-Real.log d / 2) := by
  rw [show -Real.log d / 2 = -(Real.log d / 2) by ring,
    ← Real.log_sqrt hd.le, Real.exp_neg, Real.exp_log (Real.sqrt_pos.mpr hd)]
  simp

theorem box_volume_exp (y : Fin (n + 1) → ℝ) :
    (∏ i, ENNReal.ofReal (2 * Real.exp (-y i))) =
      ENNReal.ofReal (Real.exp ((n + 1 : ℝ) * Real.log 2 - ∑ i, y i)) := by
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ by positivity)]
  congr 1
  have he (i : Fin (n + 1)) : 2 * Real.exp (-y i) = Real.exp (Real.log 2 - y i) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num)]
  simp_rw [he]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_sub_distrib]
  simp

theorem density_box_factor_exp {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hS : S.PosDef) (y : Fin (n + 1) → ℝ) :
    normalization n * ENNReal.ofReal (1 / Real.sqrt S.det) *
        (∏ i, ENNReal.ofReal (2 * Real.exp (-y i))) =
      ENNReal.ofReal (Real.exp (boxExponent S y)) := by
  rw [normalization_exp, inverse_sqrt_exp hS.det_pos, box_volume_exp,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le),
    ← Real.exp_add, ← Real.exp_add]
  congr 2
  unfold boxExponent
  ring

theorem gaussian_box_exp_upper {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hS : S.PosDef) (y : Fin (n + 1) → ℝ) :
    (multivariateGaussian 0 S) (ofLp ⁻¹' box (fun i ↦ Real.exp (-y i))) ≤
      ENNReal.ofReal (Real.exp (boxExponent S y)) := by
  rw [← density_box_factor_exp hS y]
  exact gaussian_box_upper hS _

theorem gaussian_box_exp_lower {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hS : S.PosDef) (y : Fin (n + 1) → ℝ) (Q : ℝ)
    (hQ : ∀ x ∈ box (fun i ↦ Real.exp (-y i)), x ⬝ᵥ S⁻¹ *ᵥ x ≤ Q) :
    ENNReal.ofReal (Real.exp (boxExponent S y - Q / 2)) ≤
      (multivariateGaussian 0 S) (ofLp ⁻¹' box (fun i ↦ Real.exp (-y i))) := by
  have h := gaussian_box_lower hS (fun i ↦ Real.exp (-y i)) Q hQ
  have he : normalization n * ENNReal.ofReal (Real.exp (-Q / 2)) *
      ENNReal.ofReal (1 / Real.sqrt S.det) * (∏ i, ENNReal.ofReal (2 * Real.exp (-y i))) =
      ENNReal.ofReal (Real.exp (boxExponent S y - Q / 2)) := by
    calc
      _ = (normalization n * ENNReal.ofReal (1 / Real.sqrt S.det) *
          (∏ i, ENNReal.ofReal (2 * Real.exp (-y i)))) *
          ENNReal.ofReal (Real.exp (-Q / 2)) := by ring
      _ = _ := by
        rw [density_box_factor_exp hS y, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← Real.exp_add]
        congr 2
        ring
  rw [he] at h
  exact h

end Erdos524.GaussianLogBox
