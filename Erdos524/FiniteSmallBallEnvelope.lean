import Erdos524.UpperMeshAsymptotic
import Erdos524.GaussianDiagonalScaling

namespace Erdos524.FiniteSmallBallEnvelope
open Filter MeasureTheory ProbabilityTheory WithLp
open Erdos524.LaplaceKernelComparison Erdos524.GaussianBoxDensity
open Erdos524.CauchyKernel Erdos524.GaussianDiagonalScaling
open scoped ENNReal

/-- The infimum of the actual finite Gaussian evaluation probabilities on [0,∞).
This definition does not assume existence of a continuous Gaussian process. -/
noncomputable def finiteSmallBall (δ : ℝ) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (u : Fin (n+1) → NNReal),
    (multivariateGaussian 0 (finiteKernel (fun i => (u i : ℝ))))
      (ofLp ⁻¹' box (fun _ => δ))

theorem finiteSmallBall_le_evaluation (δ : ℝ) (n : ℕ) (u : Fin (n+1) → NNReal) :
    finiteSmallBall δ ≤ (multivariateGaussian 0 (finiteKernel (fun i => (u i : ℝ))))
      (ofLp ⁻¹' box (fun _ => δ)) :=
  iInf_le_of_le n (iInf_le_of_le u le_rfl)

theorem finiteSmallBall_le_one (δ : ℝ) : finiteSmallBall δ ≤ 1 := by
  apply (finiteSmallBall_le_evaluation δ 0 (fun _ => 0)).trans
  exact prob_le_one

theorem finiteSmallBall_mono : Monotone finiteSmallBall := by
  intro a b hab
  apply le_iInf
  intro n
  apply le_iInf
  intro u
  apply (finiteSmallBall_le_evaluation a n u).trans
  apply measure_mono
  intro x hx
  intro i hi
  have h := hx i hi
  change -a≤ofLp x i ∧ ofLp x i≤a at h
  change -b≤ofLp x i ∧ ofLp x i≤b
  constructor <;> linarith [h.1,h.2]

theorem sharp_smallBall_upper {ε : ℝ} (heps : 0<ε) :
    ∀ᶠ L : ℝ in atTop,
      finiteSmallBall (Real.exp (-L)) ≤
        ENNReal.ofReal (Real.exp (-(2/(3*Real.pi^2)-ε)*L^3)) := by
  obtain ⟨K,hK,he⟩ := sharp_finite_mesh_upper heps
  filter_upwards [he] with L hL
  obtain ⟨n,hn,hp⟩ := hL
  let t := (upperPointSet L (4*Real.log L) K).orderEmbOfFin hn
  let u : Fin (n+1) → NNReal := fun i => ⟨Real.exp (t i), (Real.exp_pos _).le⟩
  have h := finiteSmallBall_le_evaluation (Real.exp (-L)) n u
  have hs := normalized_finiteKernel_exp_box t L
  change _ ≤ (multivariateGaussian 0 (finiteKernel (fun i => Real.exp (t i))))
      (ofLp ⁻¹' box (fun _ => Real.exp (-L))) at h
  rw [← hs] at h
  exact h.trans hp

end Erdos524.FiniteSmallBallEnvelope
