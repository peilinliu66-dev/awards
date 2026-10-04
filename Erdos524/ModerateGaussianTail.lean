import Erdos524.GaussianTailLower
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Erdos524.ModerateGaussianTail
open MeasureTheory ProbabilityTheory Filter Set
open Erdos524.GaussianTailLower

theorem eventually_shifted_square_bound {p q C : ℝ} (hp : 0<p) (hpq : p<q) :
    ∀ᶠ L : ℝ in atTop, ∀ x : ℝ, 0≤x → x^2≤2*p*L+C → (x+2)^2≤2*q*L := by
  let θ := (q-p)/(2*p)
  have hθ : 0<θ := by dsimp [θ]; positivity
  have heθ : (1+θ)*(2*p)=p+q := by dsimp [θ]; field_simp; ring
  let K := (1+θ)*C+4/θ+4
  filter_upwards [eventually_ge_atTop (max 0 (K/(q-p)))] with L hL
  have hL0 : 0≤L := (le_max_left _ _).trans hL
  have hKL : K≤(q-p)*L := by
    have h := (div_le_iff₀ (sub_pos.mpr hpq)).mp ((le_max_right _ _).trans hL)
    nlinarith
  intro x hx hx2
  have hy : 4*x≤θ*x^2+4/θ := by
    have h := sq_nonneg (θ*x-2)
    have he : θ*(4/θ)=4 := by field_simp
    nlinarith
  have hb := mul_le_mul_of_nonneg_left hx2 (show 0≤1+θ by linarith)
  have he : (1+θ)*(2*p*L+C)=(p+q)*L+(1+θ)*C := by
    calc
      _ = ((1+θ)*(2*p))*L+(1+θ)*C := by ring
      _ = _ := by rw [heθ]
  rw [he] at hb
  dsimp only [K] at hKL
  nlinarith

theorem eventually_linear_le_exp {a c : ℝ} (ha : 0<a) (hc : 0<c) :
    ∀ᶠ L : ℝ in atTop, L≤c*Real.exp (a*L) := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) a ha
  have h := ht.eventually (gt_mem_nhds hc)
  filter_upwards [h] with L hL
  simp only [Real.rpow_one] at hL
  have hm := mul_le_mul_of_nonneg_right hL.le (Real.exp_pos (a*L)).le
  have he : (L*Real.exp (-a*L))*Real.exp (a*L)=L := by
    rw [mul_assoc,← Real.exp_add]
    simp
  rwa [he] at hm

theorem eventual_gaussian_moderate_lower {p r C : ℝ} (hp : 0<p) (hpr : p<r) :
    ∀ᶠ L : ℝ in atTop, ∀ x : ℝ, 0≤x → x^2≤2*p*L+C →
      2*Real.exp (-r*L)≤(gaussianReal 0 1).real (Ioi (x+2)) := by
  let q := (p+r)/2
  have hpq : p<q := by dsimp [q]; linarith
  have hqr : q<r := by dsimp [q]; linarith
  have hq : 0<q := hp.trans hpq
  filter_upwards [eventually_shifted_square_bound (C := C) hp hpq,
    eventually_linear_le_exp (sub_pos.mpr hqr) (show 0<tailConstant/2 by positivity [tailConstant_pos]),
    eventually_ge_atTop (max 0 (2*q))] with L hsq he hL
  have hL0 : 0≤L := (le_max_left _ _).trans hL
  have hLq : 2*q≤L := (le_max_right _ _).trans hL
  intro x hx hx2
  have hy : 1≤x+2 := by linarith
  have hyp : 0<x+2 := by linarith
  have hysq := hsq x hx hx2
  have hyL : x+2≤L := by nlinarith
  have hden := hyL.trans he
  have hexp : Real.exp (-q*L)≤Real.exp (-(x+2)^2/2) := Real.exp_le_exp.mpr (by nlinarith)
  have htail := gaussian_tail_lower hy
  have hlo : tailConstant*Real.exp (-q*L)/(x+2)≤(gaussianReal 0 1).real (Ioi (x+2)) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp tailConstant_pos.le) hyp.le).trans htail
  apply le_trans _ hlo
  apply (le_div_iff₀ hyp).mpr
  have hm := mul_le_mul_of_nonneg_left hden (show 0≤2*Real.exp (-r*L) by positivity)
  have heq : (2*Real.exp (-r*L))*(tailConstant/2*Real.exp ((r-q)*L))=tailConstant*Real.exp (-q*L) := by
    calc
      _ = tailConstant*(Real.exp (-r*L)*Real.exp ((r-q)*L)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  rw [heq] at hm
  exact hm

end Erdos524.ModerateGaussianTail
