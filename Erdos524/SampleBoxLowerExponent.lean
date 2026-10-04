import Erdos524.RegressionWeightBounds
import Erdos524.GaussianLogBox
import Erdos524.GaussianDiagonalScaling
import Erdos524.SetMeshEnergy

/-! Explicit sample-box lower exponent from row and aggregate potential bounds. -/

namespace Erdos524.SampleBoxLowerExponent

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator
open Erdos524.CauchyKernel Erdos524.RegressionWeightBounds
open Erdos524.GaussianBoxDensity Erdos524.GaussianCovarianceBox Erdos524.GaussianLogBox
open Erdos524.GaussianDiagonalScaling

variable {n : ℕ}

theorem omittedPotential_eq_full_row (s : Fin n → ℝ) (i : Fin n) :
    omittedPotential s i (s i) = ∑ j, logTanhPotential |s j - s i| := by
  have he := Finset.sum_erase_add Finset.univ
    (fun j ↦ logTanhPotential |s j - s i|) (Finset.mem_univ i)
  simp only [sub_self, abs_zero, logTanhPotential_zero, add_zero] at he
  rw [← he]
  unfold omittedPotential
  apply Finset.sum_congr rfl
  intro j hj
  rw [abs_sub_comm]

theorem inverse_diagonal_omitted (s : Fin (n + 1) → ℝ) (hs : Function.Injective s)
    (i : Fin (n + 1)) :
    (normalized (fun j ↦ Real.exp (s j)))⁻¹ i i =
      2 * Real.exp (2 * omittedPotential s i (s i)) := by
  rw [inverse_diagonal_exp_eq s hs i]
  have he := Fin.sum_univ_succAbove (fun j ↦ logTanhPotential |s j - s i|) i
  simp only [sub_self, abs_zero, logTanhPotential_zero, zero_add] at he
  rw [← he, ← omittedPotential_eq_full_row]

theorem log_det_eq_row_potentials (s : Fin n → ℝ) (hs : StrictMono s) :
    Real.log (normalized (fun i ↦ Real.exp (s i))).det =
      -(n : ℝ) * Real.log 2 - ∑ i, omittedPotential s i (s i) := by
  rw [log_det_normalized_exp s hs]
  simp_rw [omittedPotential_eq_full_row]
  rw [rowEnergy_eq_twice_pairEnergy s hs]

theorem sample_inverse_energy_bound (s : Fin (n + 1) → ℝ) (hs : Function.Injective s)
    (d : Fin (n + 1) → ℝ) (A H : ℝ)
    (hrow : ∀ i, omittedPotential s i (s i) ≤ d i + A) (i : Fin (n + 1)) :
    (Real.exp (-(d i + H))) ^ 2 * (normalized (fun j ↦ Real.exp (s j)))⁻¹ i i ≤
      2 * Real.exp (2 * (A - H)) := by
  rw [inverse_diagonal_omitted s hs i]
  calc
    _ = 2 * (Real.exp (-(d i + H)) * Real.exp (-(d i + H)) *
        Real.exp (2 * omittedPotential s i (s i))) := by ring
    _ = 2 * Real.exp (2 * (omittedPotential s i (s i) - d i - H)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by gcongr; linarith [hrow i]

theorem sample_quadratic_bound (s : Fin (n + 1) → ℝ) (hs : Function.Injective s)
    (d : Fin (n + 1) → ℝ) (A H : ℝ)
    (hrow : ∀ i, omittedPotential s i (s i) ≤ d i + A)
    {z : Fin (n + 1) → ℝ} (hz : z ∈ box (fun i ↦ Real.exp (-(d i + H)))) :
    z ⬝ᵥ (normalized (fun j ↦ Real.exp (s j)))⁻¹ *ᵥ z ≤
      2 * (n + 1 : ℝ) ^ 2 * Real.exp (2 * (A - H)) := by
  have hC := posDef_normalized_fin (fun i ↦ Real.exp (s i)) (fun i ↦ Real.exp_pos _)
    (Real.exp_injective.comp hs)
  have h := quadratic_le_box_diagonal_budget hC.posSemidef.inv _ hz
  refine h.trans ?_
  calc
    _ ≤ (n + 1 : ℝ) * ∑ _ : Fin (n + 1), 2 * Real.exp (2 * (A - H)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun i _ ↦ sample_inverse_energy_bound s hs d A H hrow i)
    _ = _ := by simp; ring

theorem normalized_sample_box_lower (s : Fin (n + 1) → ℝ) (hs : StrictMono s)
    (d : Fin (n + 1) → ℝ) (A H E : ℝ)
    (hrow : ∀ i, omittedPotential s i (s i) ≤ d i + A)
    (haggregate : (∑ i, d i) - E ≤ ∑ i, omittedPotential s i (s i)) :
    ENNReal.ofReal (Real.exp (-(∑ i, d i) / 2 - (n + 1 : ℝ) * H - E / 2 +
      (n + 1 : ℝ) * ((3 / 2 : ℝ) * Real.log 2 - Real.log (Real.sqrt (2 * Real.pi))) -
      (n + 1 : ℝ) ^ 2 * Real.exp (2 * (A - H)))) ≤
    (multivariateGaussian 0 (normalized (fun i ↦ Real.exp (s i))))
      (ofLp ⁻¹' box (fun i ↦ Real.exp (-(d i + H)))) := by
  have hC := posDef_normalized_fin (fun i ↦ Real.exp (s i)) (fun i ↦ Real.exp_pos _)
    (Real.exp_injective.comp hs.injective)
  have hp := gaussian_box_exp_lower hC (fun i ↦ d i + H)
    (2 * (n + 1 : ℝ) ^ 2 * Real.exp (2 * (A - H)))
    (fun z hz ↦ sample_quadratic_bound s hs.injective d A H hrow hz)
  refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) hp
  unfold boxExponent
  rw [log_det_eq_row_potentials s hs, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  linarith

theorem raw_constant_sample_box_lower (s : Fin (n + 1) → ℝ) (hs : StrictMono s)
    (L A H E : ℝ)
    (hrow : ∀ i, omittedPotential s i (s i) ≤ L - s i / 2 + A)
    (haggregate : (∑ i, (L - s i / 2)) - E ≤ ∑ i, omittedPotential s i (s i)) :
    ENNReal.ofReal (Real.exp (-(∑ i, (L - s i / 2)) / 2 - (n + 1 : ℝ) * H - E / 2 +
      (n + 1 : ℝ) * ((3 / 2 : ℝ) * Real.log 2 - Real.log (Real.sqrt (2 * Real.pi))) -
      (n + 1 : ℝ) ^ 2 * Real.exp (2 * (A - H)))) ≤
    (multivariateGaussian 0 (cauchy (fun i ↦ Real.exp (s i))))
      (ofLp ⁻¹' box (fun _ ↦ Real.exp (-L - H))) := by
  have hp := normalized_sample_box_lower s hs (fun i ↦ L - s i / 2) A H E hrow haggregate
  have he := diagonal_gaussian_box
    (posSemidef_cauchy_fin (fun i ↦ Real.exp (s i)) (fun i ↦ Real.exp_pos _))
    (fun i ↦ Real.sqrt (Real.exp (s i))) (fun i ↦ Real.sqrt_pos.mpr (Real.exp_pos _))
    (fun _ ↦ Real.exp (-L - H))
  rw [← normalized_eq_diagonal] at he
  have hw (i : Fin (n + 1)) : Real.sqrt (Real.exp (s i)) * Real.exp (-L - H) =
      Real.exp (-(L - s i / 2 + H)) := by
    rw [sqrt_exp_half, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hw] at he
  rw [he] at hp
  exact hp

end Erdos524.SampleBoxLowerExponent
