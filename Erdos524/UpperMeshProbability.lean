import Erdos524.UpperMeshCutoff
import Erdos524.UpperMeshExponent
import Erdos524.FiniteKernelBox

/-! Quantitative upper small-box estimate for the actual finite-[0,1] Laplace covariance. -/

namespace Erdos524.UpperMeshProbability

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator
open Erdos524.CauchyKernel Erdos524.FiniteKernelPerturbation
open Erdos524.FiniteKernelBox Erdos524.GaussianBoxDensity Erdos524.GaussianLogBox

variable {K n : ℕ}

theorem upper_mesh_gaussian_probability (hK : 0 < K) {L : ℝ} (hL : 2 ≤ L)
    (hw : 0 ≤ upperWidth L (4 * Real.log L) K)
    (hn : (upperPointSet L (4 * Real.log L) K).card = n + 1) :
    let t := (upperPointSet L (4 * Real.log L) K).orderEmbOfFin hn
    (multivariateGaussian 0 (normalizedFiniteKernel (fun i ↦ Real.exp (t i))))
        (ofLp ⁻¹' box (fun i ↦ Real.exp (-(L - t i / 2)))) ≤
      ENNReal.ofReal (Real.exp (
        -upperWidth L (4 * Real.log L) K / Real.pi ^ 2 *
          (L ^ 2 * ((K : ℝ) / 3 - 1 / (12 * K))) +
        (K : ℝ) * L / 4 + 2 * (n + 1 : ℝ) ^ 2 * Real.exp (-2 * (4 * Real.log L)) +
        (n + 1 : ℝ) * (2 * Real.log 2 - Real.log (Real.sqrt (2 * Real.pi))))) := by
  let s := upperPointSet L (4 * Real.log L) K
  let t : Fin (n + 1) → ℝ := s.orderEmbOfFin hn
  have ht : StrictMono t := (s.orderEmbOfFin hn).strictMono
  have hC := (posDef_normalized_fin (fun i ↦ Real.exp (t i)) (fun i ↦ Real.exp_pos _)
    (Real.exp_injective.comp ht.injective)).smul (show (0 : ℝ) < 1 / 2 by norm_num)
  have hp := (gaussian_box_covariance_mono hC.posSemidef
    (upper_mesh_actual_half_gap hK hL hw hn) (fun i ↦ Real.exp (-(L - t i / 2)))).trans
      (gaussian_box_exp_upper hC (fun i ↦ L - t i / 2))
  refine hp.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  rw [half_normalized_boxExponent t ht]
  have hE := upper_mesh_exponent_bound hK (by linarith : 0 < L)
    (upper_mesh_energy_gap hL) hw hn
  have hs := sum_ordered_set s hn (fun x ↦ L - x / 2)
  change (∑ i, (L - t i / 2)) = _ at hs
  change -(∑ x ∈ s, (L - x / 2)) -
    Real.log (normalized (fun i ↦ Real.exp (t i))).det / 2 ≤ _ at hE
  rw [← hs, log_det_normalized_exp t ht] at hE
  push_cast at hE
  ring_nf at hE ⊢
  linarith

end Erdos524.UpperMeshProbability
