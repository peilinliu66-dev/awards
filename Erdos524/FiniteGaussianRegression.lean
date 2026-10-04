import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! Finite Gaussian regression with explicitly verified normal equations. -/

namespace Erdos524.FiniteGaussianRegression

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n m : ℕ}
variable {X : Ω → (Fin n → ℝ)} {Y : Ω → (Fin m → ℝ)}

noncomputable def residual (W : Matrix (Fin m) (Fin n) ℝ)
    (X : Ω → (Fin n → ℝ)) (Y : Ω → (Fin m → ℝ)) : Ω → (Fin m → ℝ) :=
  fun ω ↦ Y ω - W *ᵥ X ω

theorem joint_residual_gaussian (W : Matrix (Fin m) (Fin n) ℝ)
    (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω ↦ (X ω, residual W X Y ω)) P := by
  let fstL := LinearMap.fst ℝ (Fin n → ℝ) (Fin m → ℝ)
  let sndL := LinearMap.snd ℝ (Fin n → ℝ) (Fin m → ℝ)
  let A := fstL.prod (sndL - (Matrix.toLin' W).comp fstL)
  let L := A.toContinuousLinearMap
  simpa [L, A, fstL, sndL, residual, Matrix.toLin'_apply] using hXY.map_fun L

theorem covariance_X_residual_zero (W : Matrix (Fin m) (Fin n) ℝ)
    (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (hnormal : ∀ i j,
      cov[fun ω ↦ X ω i, fun ω ↦ Y ω j; P] =
        ∑ k, W j k * cov[fun ω ↦ X ω i, fun ω ↦ X ω k; P]) (i : Fin n) (j : Fin m) :
    cov[fun ω ↦ X ω i, fun ω ↦ residual W X Y ω j; P] = 0 := by
  haveI := hXY.isProbabilityMeasure
  have hX (k : Fin n) : MemLp (fun ω ↦ X ω k) 2 P := (hXY.fst.eval k).memLp_two
  have hY (k : Fin m) : MemLp (fun ω ↦ Y ω k) 2 P := (hXY.snd.eval k).memLp_two
  have hWX (k : Fin n) : MemLp (fun ω ↦ W j k * X ω k) 2 P := (hX k).const_mul _
  have hsum : MemLp (fun ω ↦ ∑ k, W j k * X ω k) 2 P :=
    memLp_finsetSum Finset.univ (fun k _ ↦ hWX k)
  change cov[fun ω ↦ X ω i, fun ω ↦ Y ω j - ∑ k, W j k * X ω k; P] = 0
  rw [covariance_fun_sub_right (hX i) (hY j) hsum,
    covariance_fun_sum_right hWX (hX i)]
  simp_rw [covariance_const_mul_right]
  rw [hnormal i j, sub_self]

/-- The residual is independent of the sampled vector once the actual normal
equations are proved. In the Cauchy application those equations are finite
matrix identities; they are not replaced by an assumed regression theorem. -/
theorem residual_independent (W : Matrix (Fin m) (Fin n) ℝ)
    (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (hnormal : ∀ i j,
      cov[fun ω ↦ X ω i, fun ω ↦ Y ω j; P] =
        ∑ k, W j k * cov[fun ω ↦ X ω i, fun ω ↦ X ω k; P]) :
    IndepFun X (residual W X Y) P := by
  exact (joint_residual_gaussian W hXY).indepFun_of_covariance_eval
    (covariance_X_residual_zero W hXY hnormal)

theorem covariance_residual (W : Matrix (Fin m) (Fin n) ℝ)
    (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (hnormal : ∀ i j,
      cov[fun ω ↦ X ω i, fun ω ↦ Y ω j; P] =
        ∑ k, W j k * cov[fun ω ↦ X ω i, fun ω ↦ X ω k; P]) (j l : Fin m) :
    cov[fun ω ↦ residual W X Y ω j, fun ω ↦ residual W X Y ω l; P] =
      cov[fun ω ↦ Y ω j, fun ω ↦ Y ω l; P] -
        ∑ k, W j k * cov[fun ω ↦ X ω k, fun ω ↦ Y ω l; P] := by
  haveI := hXY.isProbabilityMeasure
  have hX (k : Fin n) : MemLp (fun ω ↦ X ω k) 2 P := (hXY.fst.eval k).memLp_two
  have hY (k : Fin m) : MemLp (fun ω ↦ Y ω k) 2 P := (hXY.snd.eval k).memLp_two
  have hR (k : Fin m) : MemLp (fun ω ↦ residual W X Y ω k) 2 P :=
    ((joint_residual_gaussian W hXY).snd.eval k).memLp_two
  have hWX (j : Fin m) (k : Fin n) : MemLp (fun ω ↦ W j k * X ω k) 2 P :=
    (hX k).const_mul _
  have hsum (j : Fin m) : MemLp (fun ω ↦ ∑ k, W j k * X ω k) 2 P :=
    memLp_finsetSum Finset.univ (fun k _ ↦ hWX j k)
  have hrx (k : Fin n) :
      cov[fun ω ↦ residual W X Y ω j, fun ω ↦ X ω k; P] = 0 := by
    rw [covariance_comm]
    exact covariance_X_residual_zero W hXY hnormal k j
  calc
    cov[fun ω ↦ residual W X Y ω j, fun ω ↦ residual W X Y ω l; P] =
        cov[fun ω ↦ residual W X Y ω j, fun ω ↦ Y ω l; P] := by
      change cov[fun ω ↦ residual W X Y ω j,
        fun ω ↦ Y ω l - ∑ k, W l k * X ω k; P] = _
      rw [covariance_fun_sub_right (hR j) (hY l) (hsum l),
        covariance_fun_sum_right (hWX l) (hR j)]
      simp_rw [covariance_const_mul_right, hrx, mul_zero, Finset.sum_const_zero, sub_zero]
    _ = _ := by
      change cov[fun ω ↦ Y ω j - ∑ k, W j k * X ω k, fun ω ↦ Y ω l; P] = _
      rw [covariance_fun_sub_left (hY j) (hsum j) (hY l),
        covariance_fun_sum_left (hWX j) (hY l)]
      simp_rw [covariance_const_mul_left]

end Erdos524.FiniteGaussianRegression
