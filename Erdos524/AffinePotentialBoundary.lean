import Erdos524.QuantilePotentialBounds
import Erdos524.PotentialTailIntegrals

namespace Erdos524.CauchyKernel
open Set MeasureTheory Filter
open Erdos524.QuantileCounting

theorem integral_translated_set (s : Set ℝ) (hs : MeasurableSet s) (f : ℝ → ℝ) (t : ℝ) :
    (∫ x in {x : ℝ | x-t ∈ s}, f (x-t)) = ∫ x in s, f x := by
  have hm : MeasurableSet {x : ℝ | x-t ∈ s} := hs.preimage (measurable_id.sub measurable_const)
  rw [← integral_indicator hm]
  have he : {x : ℝ | x-t ∈ s}.indicator (fun x => f (x-t)) =
      (fun x => s.indicator f (x-t)) := by
    funext x
    rfl
  rw [he,integral_sub_right_eq_self,integral_indicator hs]

theorem integrable_linear_evenPotential (C B : ℝ) :
    Integrable (fun x : ℝ => (C+B*|x|)*evenPotential x) := by
  convert (integrable_evenPotential.const_mul C).add (absolute_firstMoment_integrable.const_mul B) using 1
  funext x
  change _=C*evenPotential x+B*(|x| * evenPotential x)
  ring

theorem affine_abs_bound (A B t x : ℝ) (hB : 0≤B) :
    |A-B*x|≤|A-B*t|+B*|x-t| := by
  have he : A-B*x=(A-B*t)-B*(x-t) := by ring
  rw [he]
  have h := abs_sub (A-B*t) (B*(x-t))
  simpa only [abs_mul,abs_of_nonneg hB] using h

theorem affinePotential_interior_error (a b A B t : ℝ) {G : ℝ}
    (hB : 0≤B) (hG : Real.log 2≤G) (hleft : a+G≤t) (hright : t+G≤b) :
    |affinePotential a b A B t-(A-B*t)*(Real.pi^2/2)| ≤
      8*|A-B*t| * Real.exp (-G)+32*B*Real.exp (-(1/2:ℝ)*G) := by
  let f : ℝ → ℝ := fun x => (A-B*x)*evenPotential (x-t)
  let g : ℝ → ℝ := fun x => (|A-B*t|+B*|x-t|)*evenPotential (x-t)
  let S : Set ℝ := {x : ℝ | G≤|x-t|}
  have hf : Integrable f := integrable_affine_evenPotential A B t
  have hg : Integrable g := (integrable_linear_evenPotential |A-B*t| B).comp_sub_right t
  have hg0 : ∀ x, 0≤g x := fun x => mul_nonneg (by positivity) (evenPotential_nonneg (x-t))
  have hsub : (Icc a b)ᶜ ⊆ S := by
    intro x hx
    have hnot : ¬(a≤x ∧ x≤b) := hx
    by_cases hxa : a≤x
    · have hbx : b<x := lt_of_not_ge (fun h => hnot ⟨hxa,h⟩)
      change G≤|x-t|
      have h := le_abs_self (x-t)
      linarith
    · have hxa' : x<a := lt_of_not_ge hxa
      change G≤|x-t|
      have h := neg_le_abs (x-t)
      linarith
  have hcompl := integral_add_compl (s := Icc a b) measurableSet_Icc hf
  have hwhole : (∫ x : ℝ, f x)=(A-B*t)*(Real.pi^2/2) := integral_affine_evenPotential A B t
  have heq : |affinePotential a b A B t-(A-B*t)*(Real.pi^2/2)| = |∫ x in (Icc a b)ᶜ, f x| := by
    change |(∫ x in Icc a b, f x)-(A-B*t)*(Real.pi^2/2)| = _
    rw [← hwhole,← hcompl]
    simp only [sub_add_cancel_left,abs_neg]
  rw [heq]
  calc
    _ ≤ ∫ x in (Icc a b)ᶜ, ‖f x‖ := by exact norm_integral_le_integral_norm f
    _ ≤ ∫ x in (Icc a b)ᶜ, g x := by
      apply integral_mono_ae hf.norm.integrableOn hg.integrableOn
      apply Eventually.of_forall
      intro x
      dsimp [f,g]
      rw [abs_mul,abs_of_nonneg (evenPotential_nonneg _)]
      exact mul_le_mul_of_nonneg_right (affine_abs_bound A B t x hB) (evenPotential_nonneg _)
    _ ≤ ∫ x in S, g x :=
      setIntegral_mono_set hg.integrableOn (Eventually.of_forall hg0) (Eventually.of_forall hsub)
    _ = ∫ x in absoluteTail G, (|A-B*t|+B*|x|)*evenPotential x := by
      exact integral_translated_set (absoluteTail G) (measurableSet_absoluteTail G)
        (fun x => (|A-B*t|+B*|x|)*evenPotential x) t
    _ ≤ _ := linear_potential_tail_bound (abs_nonneg _) hB hG


theorem affinePotential_boundary_upper (a b A B t : ℝ) {H : ℝ}
    (hB : 0<B) (hH : Real.log 2≤H) (hmargin : B*H≤A-B*t) :
    affinePotential a b A B t ≤ (A-B*t)*(Real.pi^2/2)+32*B*Real.exp (-(1/2:ℝ)*H) := by
  let f : ℝ → ℝ := fun x => (A-B*x)*evenPotential (x-t)
  let g : ℝ → ℝ := fun x => (absoluteTail H).indicator
    (fun z => (0+B*|z|)*evenPotential z) (x-t)
  have hHp : 0<H := lt_of_lt_of_le (Real.log_pos (by norm_num)) hH
  have hf : Integrable f := integrable_affine_evenPotential A B t
  have hg : Integrable g := ((integrable_linear_evenPotential 0 B).indicator
    (measurableSet_absoluteTail H)).comp_sub_right t
  have hg0 : ∀ x, 0≤g x := by
    intro x
    dsimp [g]
    by_cases hx : x-t ∈ absoluteTail H
    · rw [indicator_of_mem hx]
      exact mul_nonneg (by positivity) (evenPotential_nonneg _)
    · rw [indicator_of_notMem hx]
  have hpoint : ∀ x, -f x≤g x := by
    intro x
    by_cases hpos : 0≤A-B*x
    · have hf0 : 0≤f x := mul_nonneg hpos (evenPotential_nonneg _)
      exact (neg_nonpos.mpr hf0).trans (hg0 x)
    · have hneg : A-B*x<0 := lt_of_not_ge hpos
      have hprod : B*H<B*(x-t) := by nlinarith
      have hdist : H<x-t := by nlinarith [hprod]
      have hx : x-t ∈ absoluteTail H := hdist.le.trans (le_abs_self _)
      have hcoeff : -(A-B*x)≤B*|x-t| := by
        have habs := le_abs_self (x-t)
        have hm := mul_le_mul_of_nonneg_left habs hB.le
        have hρ : 0≤A-B*t := le_trans (mul_nonneg hB.le hHp.le) hmargin
        nlinarith
      have hm := mul_le_mul_of_nonneg_right hcoeff (evenPotential_nonneg (x-t))
      dsimp [f,g]
      rw [indicator_of_mem hx,zero_add]
      nlinarith
  have hcompl := integral_add_compl (s := Icc a b) measurableSet_Icc hf
  have hwhole : (∫ x : ℝ, f x)=(A-B*t)*(Real.pi^2/2) := integral_affine_evenPotential A B t
  have heq : affinePotential a b A B t-(A-B*t)*(Real.pi^2/2)=
      ∫ x in (Icc a b)ᶜ, -f x := by
    rw [integral_neg]
    change (∫ x in Icc a b, f x)-(A-B*t)*(Real.pi^2/2)=_
    linarith
  have hbound : affinePotential a b A B t-(A-B*t)*(Real.pi^2/2)≤
      32*B*Real.exp (-(1/2:ℝ)*H) := by
    rw [heq]
    calc
      _ ≤ ∫ x in (Icc a b)ᶜ, g x := integral_mono_ae hf.neg.integrableOn hg.integrableOn (Eventually.of_forall hpoint)
      _ ≤ ∫ x : ℝ, g x := setIntegral_le_integral hg (Eventually.of_forall hg0)
      _ = ∫ x in absoluteTail H, (0+B*|x|)*evenPotential x := by
        exact (integral_sub_right_eq_self ((absoluteTail H).indicator (fun z => (0+B*|z|)*evenPotential z)) t).trans
          (integral_indicator (measurableSet_absoluteTail H))
      _ ≤ _ := by simpa only [mul_zero,zero_mul,zero_add] using linear_potential_tail_bound (by norm_num : (0:ℝ)≤0) hB.le hH
  linarith

end Erdos524.CauchyKernel
