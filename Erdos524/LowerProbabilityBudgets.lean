import Erdos524.LowerPotentialEstimates

namespace Erdos524.QuantileCounting
open Erdos524.CauchyKernel

theorem lower_exp80_le_cube {L : ℝ} (hL : 16≤L) :
    Real.exp (-80*Real.log L)≤1/L^3 := by
  have hlpos : 0<L := by linarith
  have hlog : 0≤Real.log L := Real.log_nonneg (by linarith)
  have he := Real.exp_le_exp.mpr (show -80*Real.log L≤ -3*Real.log L by linarith)
  have h3 := exp_neg_nat_log hlpos 3
  norm_num at h3
  simpa only [neg_mul,h3,one_div] using he

theorem lower_mean_budget {L N : ℝ} (hL : 16≤L) (hN : 0≤N) (hNmax : N≤L^2) :
    2*N*Real.exp (-L-200*Real.log L)*Real.exp (120*Real.log L)≤
      Real.exp (-L)-Real.exp (-L)/2 := by
  have hlpos : 0<L := by linarith
  have hd := Real.exp_pos (-L)
  have he : 2*N*Real.exp (-L-200*Real.log L)*Real.exp (120*Real.log L)=
      2*N*Real.exp (-L)*Real.exp (-80*Real.log L) := by
    rw [mul_assoc (2*N),← Real.exp_add,mul_assoc (2*N),← Real.exp_add]
    congr 2
    ring
  rw [he]
  calc
    _ ≤ 2*L^2*Real.exp (-L)*(1/L^3) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (by nlinarith : 2*N≤2*L^2) hd.le
      · exact lower_exp80_le_cube hL
      · positivity
      · positivity
    _ = 2*Real.exp (-L)/L := by field_simp
    _ ≤ _ := by
      apply (div_le_iff₀ hlpos).mpr
      nlinarith

theorem lower_residual_budget {L : ℝ} (hL : 16≤L) :
    Real.exp (-L-80*Real.log L)*(1+(2*L+4*Real.log L)/Real.sqrt 8)+
      Real.exp (-(2*L+4*Real.log L)/2)≤(Real.exp (-L)/2)/2 := by
  have hlpos : 0<L := by linarith
  have hlog : 0≤Real.log L := Real.log_nonneg (by linarith)
  have hlogL : Real.log L≤L := by have := Real.log_le_sub_one_of_pos hlpos; linarith
  have hs : 1≤Real.sqrt 8 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤8),Real.sqrt_nonneg 8]
  have hfactor : 1+(2*L+4*Real.log L)/Real.sqrt 8≤7*L := by
    have hd := div_le_self (show 0≤2*L+4*Real.log L by positivity) hs
    linarith
  have hprod : Real.exp (-80*Real.log L)*(1+(2*L+4*Real.log L)/Real.sqrt 8)≤7/L^2 := by
    calc
      _ ≤ (1/L^3)*(7*L) := mul_le_mul (lower_exp80_le_cube hL) hfactor (by positivity) (by positivity)
      _ = _ := by field_simp
  have he1 : Real.exp (-L-80*Real.log L)=Real.exp (-L)*Real.exp (-80*Real.log L) := by
    rw [← Real.exp_add]; congr 1; ring
  have he2 : Real.exp (-(2*L+4*Real.log L)/2)=Real.exp (-L)*(1/L^2) := by
    have h2 := exp_neg_nat_log hlpos 2
    norm_num at h2
    rw [one_div,← h2,← Real.exp_add]
    congr 1
    ring
  rw [he1,he2]
  have hh := mul_le_mul_of_nonneg_left hprod (Real.exp_pos (-L)).le
  have hlast : Real.exp (-L)*(7/L^2)+Real.exp (-L)*(1/L^2)≤(Real.exp (-L)/2)/2 := by
    have hsq : 32≤L^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsq (Real.exp_pos (-L)).le
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    field_simp
    nlinarith
  nlinarith

end Erdos524.QuantileCounting
