import Erdos524.GramGaussianCoupling
import Erdos524.LaplaceKernelComparison
import Erdos524.CauchyIncrementBounds

namespace Erdos524.LaplaceIncrementBudget
open MeasureTheory ProbabilityTheory Filter Matrix
open Erdos524.LaplaceKernelComparison Erdos524.FiniteGaussianTailBound
open Erdos524.GramGaussianCoupling Erdos524.IntegralGramComparison Erdos524.CauchyIncrementBounds

noncomputable def rootBudget (u : ℝ) : ℝ := 1/Real.sqrt (u+1)

theorem squared_difference_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, (f ω-g ω)^2 ∂μ)=(∫ ω, f ω*f ω ∂μ)-2*(∫ ω, f ω*g ω ∂μ)+(∫ ω, g ω*g ω ∂μ) := by
  have h := gram_increment (fun _ : Fin 1 => f) (fun _ : Fin 1 => g) (fun _ => hf) (fun _ => hg) 0
  simpa only [integralGram,jointFamily,Fin.addCases_left,Fin.addCases_right] using h.symm

theorem finite_increment_budget {n : ℕ} (u : Fin n → ℝ) (hu : ∀ i, 0≤u i) (i j : Fin n) :
    (∫ z : EuclideanSpace ℝ (Fin n), (z i-z j)^2 ∂multivariateGaussian 0 (finiteKernel u))≤
      (Real.exp 1*(rootBudget (u i)-rootBudget (u j)))^2 := by
  rw [gaussian_increment_second_moment (finiteKernel_posSemidef u hu)]
  have hk := squared_difference_integral (memLp_laplace_interval (hu i)) (memLp_laplace_interval (hu j))
  have hd := squared_difference_integral (memLp_laplace_dominating (hu i)) (memLp_laplace_dominating (hu j))
  have hint : Integrable (fun s => (laplace (u i) s-laplace (u j) s)^2) dominatingMeasure := by
    simpa only [Real.norm_eq_abs,sq_abs,Pi.sub_apply] using
      ((memLp_laplace_dominating (hu i)).sub (memLp_laplace_dominating (hu j))).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hm := integral_mono_measure intervalMeasure_le_dominatingMeasure (Eventually.of_forall (fun s => sq_nonneg (laplace (u i) s-laplace (u j) s))) hint
  rw [hk,hd] at hm
  change finiteKernel u i i-2*finiteKernel u i j+finiteKernel u j j≤dominatingKernel u i i-2*dominatingKernel u i j+dominatingKernel u j j at hm
  apply hm.trans
  rw [dominatingKernel_apply u hu,dominatingKernel_apply u hu,dominatingKernel_apply u hu]
  have hi : u i+u i+2=2*(u i+1) := by ring
  have hj : u j+u j+2=2*(u j+1) := by ring
  have hij : u i+u j+2=(u i+1)+(u j+1) := by ring
  rw [hi,hj,hij]
  have hc := mul_le_mul_of_nonneg_left (cauchy_increment_le_inverse_root_sq (v := u i+1) (w := u j+1) (by linarith [hu i]) (by linarith [hu j])) (Real.exp_pos 2).le
  have he : Real.exp (2:ℝ)=(Real.exp 1)^2 := by rw [← Real.exp_nat_mul]; norm_num
  dsimp only [rootBudget]
  rw [he] at hc ⊢
  convert hc using 1 <;> ring

theorem rootBudget_antitone {u v : ℝ} (hu : 0≤u) (huv : u≤v) : rootBudget v≤rootBudget u := by
  unfold rootBudget
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt (by linarith))

theorem rootBudget_gap {u v : ℝ} (hu : 0≤u) (huv : u≤v) : rootBudget u-rootBudget v≤(v-u)/2 := by
  let p := Real.sqrt (u+1)
  let q := Real.sqrt (v+1)
  have hp : 1≤p := by dsimp only [p]; simpa using Real.sqrt_le_sqrt (show (1:ℝ)≤u+1 by linarith)
  have hq : 1≤q := by dsimp only [q]; simpa using Real.sqrt_le_sqrt (show (1:ℝ)≤v+1 by linarith)
  have hp0 : p≠0 := by linarith
  have hq0 : q≠0 := by linarith
  have hps : p^2=u+1 := Real.sq_sqrt (by linarith)
  have hqs : q^2=v+1 := Real.sq_sqrt (by linarith)
  have hgap : 0≤1/p-1/q := sub_nonneg.mpr (rootBudget_antitone hu huv)
  have hden : 2≤p*q*(p+q) := by nlinarith [mul_le_mul hp hq (by norm_num : (0:ℝ)≤1) (by linarith : 0≤p)]
  have he : (1/p-1/q)*(p*q*(p+q))=v-u := by
    calc
      _ = q^2-p^2 := by field_simp; ring
      _ = _ := by rw [hps,hqs]; ring
  change 1/p-1/q≤(v-u)/2
  nlinarith

end Erdos524.LaplaceIncrementBudget
