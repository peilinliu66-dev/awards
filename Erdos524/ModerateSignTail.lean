import Erdos524.ModerateGaussianTail
import Erdos524.SignSumGaussianComparison

namespace Erdos524.ModerateSignTail
open MeasureTheory ProbabilityTheory Filter Set
open Erdos524.SignGaussianMoments Erdos524.SignSumGaussianComparison Erdos524.ModerateGaussianTail

theorem eventual_exponential_error {a D r C : ℝ} (ha : 0<a) (hD : 0<D) :
    ∀ᶠ J : ℝ in atTop, D*Real.exp (-(a*J-C)/2)≤Real.exp (-r*Real.log J) := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero r (a/2) (by positivity)
  have hc : 0<1/(D*Real.exp (C/2)) := by positivity
  filter_upwards [ht.eventually (gt_mem_nhds hc),eventually_gt_atTop (0:ℝ)] with J hJ hpos
  rw [Real.rpow_def_of_pos hpos] at hJ
  have h := (lt_div_iff₀ (show 0<D*Real.exp (C/2) by positivity)).mp hJ
  have he : (Real.exp (Real.log J*r)*Real.exp (-(a/2)*J))*(D*Real.exp (C/2))=
      (D*Real.exp (-(a*J-C)/2))*Real.exp (r*Real.log J) := by
    calc
      _ = D*(Real.exp (Real.log J*r)*Real.exp (-(a/2)*J)*Real.exp (C/2)) := by ring
      _ = D*Real.exp (Real.log J*r+(-(a/2)*J)+C/2) := by rw [← Real.exp_add,← Real.exp_add]
      _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
  rw [he] at h
  have hm := mul_le_mul_of_nonneg_right h.le (Real.exp_pos (-r*Real.log J)).le
  have he' : ((D*Real.exp (-(a*J-C)/2))*Real.exp (r*Real.log J))*Real.exp (-r*Real.log J)=D*Real.exp (-(a*J-C)/2) := by
    rw [mul_assoc,← Real.exp_add]; simp
  simpa only [he',one_mul] using hm

theorem eventual_sum_moderate_lower {p a C C₀ : ℝ} (hp : 0<p) (hp1 : p<1) (ha : 0<a) :
    ∀ᶠ J : ℝ in atTop, ∀ N : ℕ, 0<N → a*J-C₀≤Real.log (N:ℝ) → ∀ x : ℝ,
      0≤x → x^2≤2*p*Real.log J+C →
      1/J≤(Measure.pi (fun _ : Fin N => signLaw)).real {z | x<normalizedSum z} := by
  let r := (p+1)/2
  have hpr : p<r := by dsimp [r]; linarith
  have hr1 : r<1 := by dsimp [r]; linarith
  obtain ⟨D,hD,hcomp⟩ := exists_exponential_sum_tail_constant
  have hgauss := Real.tendsto_log_atTop.eventually (eventual_gaussian_moderate_lower (C := C) hp hpr)
  filter_upwards [hgauss,eventual_exponential_error (r := r) (C := C₀) ha hD,
    eventually_ge_atTop (1:ℝ)] with J hg he hJ
  intro N hN hlog x hx hx2
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hln : 0≤Real.log (N:ℝ) := Real.log_nonneg hn1
  have hη : Real.exp (-Real.log (N:ℝ)/8)≤1 := by rw [Real.exp_le_one_iff]; linarith
  have hmono : (gaussianReal 0 1).real (Ioi (x+2))≤
      (gaussianReal 0 1).real (Ioi (x+2*Real.exp (-Real.log (N:ℝ)/8))) :=
    measureReal_mono (by intro y hy; simp only [mem_Ioi] at *; linarith)
  have herror : D*Real.exp (-Real.log (N:ℝ)/2)≤Real.exp (-r*Real.log J) :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hD.le).trans he
  have hc := hcomp hN x
  have hgl := hg x hx hx2
  have hlo : Real.exp (-r*Real.log J)≤(Measure.pi (fun _ : Fin N => signLaw)).real {z | x<normalizedSum z} := by linarith
  apply le_trans _ hlo
  have hJp : 0<J := lt_of_lt_of_le zero_lt_one hJ
  have heJ : 1/J=Real.exp (-Real.log J) := by rw [Real.exp_neg,Real.exp_log hJp,one_div]
  rw [heJ]
  exact Real.exp_le_exp.mpr (by have := Real.log_nonneg hJ; nlinarith)

end Erdos524.ModerateSignTail
