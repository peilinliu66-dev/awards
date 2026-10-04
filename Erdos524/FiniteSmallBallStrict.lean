import Erdos524.LaplaceAnnulusGeometry
import Erdos524.LaplaceResidualComparison
import Erdos524.FiniteSmallBallZero

/-! Strict increase from a uniform Gaussian annulus, without a process construction. -/

namespace Erdos524.FiniteSmallBallStrict

open Set Filter MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal
open Erdos524.FiniteLaplaceRegression Erdos524.FiniteLaplaceBand
open Erdos524.LaplaceAnnulusGeometry Erdos524.LaplaceResidualComparison
open Erdos524.FiniteSmallBallEnvelope Erdos524.FiniteSmallBallBasic Erdos524.FiniteSmallBallZero
open Erdos524.LaplaceKernelComparison Erdos524.GaussianBoxDensity Erdos524.FiniteGaussianCubes

variable {n : ℕ}

theorem zero_evaluation_annulus (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 ≤ u i)
    (j : Fin (n + 1)) (hj : u j = 0) {a η : ℝ} (ha : 0 ≤ a) (hη : 0 < η) :
    finiteSmallBall a + (gaussianReal 0 1) (Icc (a + 2 * η) (a + 3 * η)) * finiteSmallBall η ≤
      (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' box (fun _ ↦ a + 4 * η)) := by
  let ν := (jointMeasure u).map (laplaceResidual u)
  haveI := (residual_gaussian u).isGaussian_map
  let P := (gaussianReal 0 1).prod ν
  let E := Icc (a + 2 * η) (a + 3 * η) ×ˢ box (fun _ : Fin (n + 1) ↦ η)
  have hsub : E ⊆ fiberSet u (a + 4 * η) \ fiberSet u a := affine_annulus_subset u hu j hj ha hη
  have hdis : Disjoint (fiberSet u a) E := disjoint_left.mpr (fun _ hA hE ↦ (hsub hE).2 hA)
  have hEmeas : MeasurableSet E := measurableSet_Icc.prod (measurableSet_box _)
  have hmono : fiberSet u a ⊆ fiberSet u (a + 4 * η) := by
    intro p hp i
    exact (hp i).trans (by linarith)
  have hFa : finiteSmallBall a ≤ P (fiberSet u a) :=
    (finiteSmallBall_le_evaluation a n (fun i ↦ ⟨u i, hu i⟩)).trans_eq (laplace_box_product u hu a)
  have hFη : finiteSmallBall η ≤ ν (box (fun _ ↦ η)) := finiteSmallBall_le_residual u hu η
  rw [laplace_box_product u hu (a + 4 * η)]
  change _ ≤ P (fiberSet u (a + 4 * η))
  calc
    _ ≤ P (fiberSet u a) + (gaussianReal 0 1) (Icc (a + 2 * η) (a + 3 * η)) * ν (box (fun _ ↦ η)) := by gcongr
    _ = P (fiberSet u a) + P E := by rw [Measure.prod_prod]
    _ = P (fiberSet u a ∪ E) := (measure_union hdis hEmeas).symm
    _ ≤ _ := measure_mono (union_subset hmono (fun p hp ↦ (hsub hp).1))

theorem finiteKernel_cons_cube_le (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 ≤ u i) (δ : ℝ) :
    (multivariateGaussian 0 (finiteKernel (Fin.cons 0 u))) (ofLp ⁻¹' box (fun _ ↦ δ)) ≤
      (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' box (fun _ ↦ δ)) := by
  have hp := finiteKernel_projection_cube (Fin.cons 0 u) (cons_nonneg u hu) Fin.succ δ
  have hp' : (multivariateGaussian 0 (finiteKernel (Fin.cons 0 u)))
      ((fun z ↦ fun i ↦ z i.succ) ⁻¹' box (fun _ : Fin (n + 1) ↦ δ)) =
      (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' box (fun _ ↦ δ)) := by
    simpa only [Fin.cons_succ, cube, box] using hp
  refine le_trans (measure_mono ?_) hp'.le
  intro z hz i hi
  exact hz i.succ (Set.mem_univ _)

theorem finiteSmallBall_annulus {a η : ℝ} (ha : 0 ≤ a) (hη : 0 < η) :
    finiteSmallBall a + (gaussianReal 0 1) (Icc (a + 2 * η) (a + 3 * η)) * finiteSmallBall η ≤
      finiteSmallBall (a + 4 * η) := by
  apply le_iInf
  intro n
  apply le_iInf
  intro u
  let v : Fin (n + 1) → ℝ := fun i ↦ (u i : ℝ)
  have hv (i : Fin (n + 1)) : 0 ≤ v i := (u i).property
  have h := zero_evaluation_annulus (Fin.cons 0 v) (cons_nonneg v hv) 0 (by simp) ha hη
  exact h.trans (finiteKernel_cons_cube_le v hv _)

theorem finiteSmallBall_strict_increase {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    finiteSmallBall a < finiteSmallBall b := by
  let η := (b - a) / 4
  have hη : 0 < η := by dsimp [η]; linarith
  have hp : 0 < (gaussianReal 0 1) (Icc (a + 2 * η) (a + 3 * η)) * finiteSmallBall η :=
    ENNReal.mul_pos (ne_of_gt (standardGaussian_interval_pos (by linarith)))
      (ne_of_gt (finiteSmallBall_pos hη))
  have h := (ENNReal.lt_add_right (finiteSmallBall_ne_top a) (ne_of_gt hp)).trans_le
    (finiteSmallBall_annulus ha hη)
  have he : a + 4 * η = b := by dsimp [η]; ring
  rwa [he] at h

theorem smallBallReal_strictMono : StrictMonoOn smallBallReal (Ici 0) := by
  intro a ha b hb hab
  exact (ENNReal.toReal_lt_toReal (finiteSmallBall_ne_top a) (finiteSmallBall_ne_top b)).mpr
    (finiteSmallBall_strict_increase ha hab)

theorem smallBallReal_lt_one {δ : ℝ} (hδ : 0 ≤ δ) : smallBallReal δ < 1 := by
  have h := smallBallReal_strictMono hδ (show 0 ≤ δ + 1 by linarith) (show δ < δ + 1 by linarith)
  exact h.trans_le (smallBallReal_le_one _)

end Erdos524.FiniteSmallBallStrict
