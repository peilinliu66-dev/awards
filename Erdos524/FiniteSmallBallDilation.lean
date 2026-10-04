import Erdos524.GaussianSampleDilation
import Erdos524.FiniteSmallBallStrict

/-! Passage of the sampled finite-cube likelihood ratio to the finite-evaluation envelope. -/

namespace Erdos524.FiniteSmallBallDilation

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal
open Erdos524.GaussianSampleDilation Erdos524.GaussianSampleCovariance
open Erdos524.GaussianIndependentSumLaw Erdos524.GaussianDiagonalScaling
open Erdos524.GaussianBoxDensity Erdos524.FiniteKernelPerturbation
open Erdos524.LaplaceKernelComparison Erdos524.FiniteSmallBallEnvelope
open Erdos524.FiniteGaussianCubes

variable {n m : ℕ}

theorem sampled_finiteKernel_dilation
    (s : Fin (n + 1) → ℝ) (hs : ∀ i, 0 < s i)
    (hA : (normalizedFiniteKernel s).PosDef)
    (u : Fin (m + 1) → ℝ) (hu : ∀ i, 0 ≤ u i)
    {r δ Q : ℝ} (hr : 1 ≤ r)
    (hQ : ∀ x ∈ box (fun i ↦ Real.sqrt (s i) * δ),
      x ⬝ᵥ (normalizedFiniteKernel s)⁻¹ *ᵥ x ≤ Q) :
    ENNReal.ofReal (r ^ (n + 1) * Real.exp (-((r ^ 2 - 1) * Q) / 2)) * finiteSmallBall δ ≤
      (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' box (fun _ ↦ r * δ)) := by
  let v := Fin.append s u
  let d := Fin.append (fun i ↦ Real.sqrt (s i)) (fun _ : Fin (m + 1) ↦ (1 : ℝ))
  let C := diagonal d * finiteKernel v * diagonal d
  let e : Fin (n + 1) → Fin ((n + 1) + (m + 1)) := Fin.castAdd (m + 1)
  have hv : ∀ i, 0 ≤ v i := by
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa only [v, Fin.append_left] using (hs j).le
    · simpa only [v, Fin.append_right] using hu j
  have hd : ∀ i, 0 < d i := by
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa only [d, Fin.append_left] using Real.sqrt_pos.mpr (hs j)
    · simp only [d, Fin.append_right]; norm_num
  have hC : C.PosSemidef := by
    simpa only [C, Matrix.diagonal_conjTranspose, star_trivial] using
      (finiteKernel_posSemidef v hv).conjTranspose_mul_mul_same (diagonal d)
  have hsample : sampleCovariance C e = normalizedFiniteKernel s := by
    ext i j
    simp only [sampleCovariance, Matrix.submatrix_apply, C, Matrix.diagonal_mul,
      Matrix.mul_diagonal, e, d, v, Fin.append_left, normalizedFiniteKernel]
    simp only [finiteKernel_apply, Fin.append_left]
  have hA' : (sampleCovariance C e).PosDef := hsample ▸ hA
  have hQ' : ∀ x ∈ box (fun i ↦ d (e i) * δ), x ⬝ᵥ (sampleCovariance C e)⁻¹ *ᵥ x ≤ Q := by
    simpa only [hsample, e, d, Fin.append_left] using hQ
  have h := finite_cube_dilation hC e hA' (fun i ↦ d i * δ) hr hQ'
  rw [coordinateGaussian_apply _ (measurableSet_box _),
    coordinateGaussian_apply _ (measurableSet_box _)] at h
  have hleft := diagonal_gaussian_box (finiteKernel_posSemidef v hv) d hd (fun _ ↦ δ)
  have hright := diagonal_gaussian_box (finiteKernel_posSemidef v hv) d hd (fun _ ↦ r * δ)
  change (multivariateGaussian 0 C) (ofLp ⁻¹' box (fun i ↦ d i * δ)) = _ at hleft
  have hw : (fun i ↦ r * (d i * δ)) = (fun i ↦ d i * (r * δ)) := by funext i; ring
  have hraw := (mul_le_mul_right hleft.ge
    (ENNReal.ofReal (r ^ (n + 1) * Real.exp (-((r ^ 2 - 1) * Q) / 2)))).trans h
  have hright' : (multivariateGaussian 0 C) (ofLp ⁻¹' box (fun i ↦ r * (d i * δ))) =
      (multivariateGaussian 0 (finiteKernel v)) (ofLp ⁻¹' box (fun _ ↦ r * δ)) := by
    dsimp only [C]
    convert hright using 1
    congr 1
    ext z
    simp only [Set.mem_preimage, box, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    apply forall_congr'
    intro i
    ring_nf
  have hraw' := hraw.trans_eq hright'
  have hF := finiteSmallBall_le_evaluation δ ((n + 1) + m) (fun i ↦ ⟨v i, hv i⟩)
  have hprojection := finiteKernel_projection_cube v hv (Fin.natAdd (n + 1)) (r * δ)
  have hprojection' : (multivariateGaussian 0 (finiteKernel v))
      ((fun z ↦ fun i : Fin (m + 1) ↦ z (Fin.natAdd (n + 1) i)) ⁻¹' box (fun _ ↦ r * δ)) =
      (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' box (fun _ ↦ r * δ)) := by
    simpa only [v, Fin.append_right, cube, box] using hprojection
  refine (mul_le_mul_right hF _).trans (hraw'.trans ?_)
  refine (measure_mono ?_).trans_eq hprojection'
  intro z hz i hi
  exact hz (Fin.natAdd (n + 1) i) (Set.mem_univ _)

theorem finiteSmallBall_dilation
    (s : Fin (n + 1) → ℝ) (hs : ∀ i, 0 < s i)
    (hA : (normalizedFiniteKernel s).PosDef)
    {r δ Q : ℝ} (hr : 1 ≤ r)
    (hQ : ∀ x ∈ box (fun i ↦ Real.sqrt (s i) * δ),
      x ⬝ᵥ (normalizedFiniteKernel s)⁻¹ *ᵥ x ≤ Q) :
    ENNReal.ofReal (r ^ (n + 1) * Real.exp (-((r ^ 2 - 1) * Q) / 2)) * finiteSmallBall δ ≤
      finiteSmallBall (r * δ) := by
  apply le_iInf
  intro m
  apply le_iInf
  intro u
  exact sampled_finiteKernel_dilation s hs hA (fun i ↦ u i) (fun i ↦ (u i).property) hr hQ

end Erdos524.FiniteSmallBallDilation
