import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Erdos524.ExponentialKernelLipschitz
open Set

theorem exp_negative_lipschitz {u s t : ℝ} (hu : 0≤u) (hs : 0≤s) (ht : 0≤t) :
    |Real.exp (-u*t)-Real.exp (-u*s)|≤u*|t-s| := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (-u*y)) (-u*Real.exp (-u*x)) x := by
    simpa only [id_eq,mul_one,mul_comm] using ((hasDerivAt_id x).const_mul (-u)).exp
  have he := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun y : ℝ => Real.exp (-u*y)) (s := Ici (0:ℝ))
    (fun x _ => (hd x).differentiableAt) (C := u) (by
      intro x hx
      rw [(hd x).deriv,Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg hu,abs_of_pos (Real.exp_pos _)]
      have hexp : Real.exp (-u*x)≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) hx)
      nlinarith) (convex_Ici 0) hs ht
  simpa only [Real.norm_eq_abs] using he

theorem exp_kernel_cell_error {u s t h : ℝ} (hu : 0≤u) (hs : 0≤s) (ht : 0≤t)
    (hcell : |t-s|≤h) : (Real.exp (-u*t)-Real.exp (-u*s))^2≤u^2*h^2 := by
  have hb := (exp_negative_lipschitz hu hs ht).trans (mul_le_mul_of_nonneg_left hcell hu)
  have hh : 0≤h := (abs_nonneg _).trans hcell
  have hp := sq_le_sq₀ (abs_nonneg (Real.exp (-u*t)-Real.exp (-u*s))) (mul_nonneg hu hh)
  have hb2 := hp.mpr hb
  simpa only [sq_abs,mul_pow] using hb2

end Erdos524.ExponentialKernelLipschitz
