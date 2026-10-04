import Erdos524.SignGaussianMoments
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

namespace Erdos524.SignConcentration
open MeasureTheory ProbabilityTheory Filter Set
open Erdos524.SignGaussianMoments

 theorem signLaw_ae_interval : ∀ᵐ x ∂signLaw, x∈Icc (-1:ℝ) 1 := by
  unfold signLaw
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    simp
  · apply Measure.ae_smul_measure
    simp

theorem signLaw_subgaussian : HasSubgaussianMGF (id : ℝ → ℝ) 1 signLaw := by
  have hm : AEMeasurable (id : ℝ → ℝ) signLaw := measurable_id.aemeasurable
  have hi : (∫ x : ℝ, id x ∂signLaw)=0 := by rw [integral_signLaw]; norm_num
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm signLaw_ae_interval hi
  norm_num at h
  exact h

theorem coordinate_subgaussian {N : ℕ} (i : Fin N) :
    HasSubgaussianMGF (fun z : Fin N → ℝ => z i) 1 (Measure.pi (fun _ : Fin N => signLaw)) := by
  have hmap := (measurePreserving_eval (fun _ : Fin N => signLaw) i).map_eq
  have h := signLaw_subgaussian
  rw [← hmap] at h
  have hm : AEMeasurable (Function.eval i : (Fin N → ℝ) → ℝ) (Measure.pi (fun _ : Fin N => signLaw)) :=
    (measurable_pi_apply i).aemeasurable
  have hh := HasSubgaussianMGF.of_map hm h
  simpa only [Function.comp_def,id_eq,Function.eval] using hh

theorem sign_coordinates_independent (N : ℕ) :
    iIndepFun (fun i (z : Fin N → ℝ) => z i) (Measure.pi (fun _ : Fin N => signLaw)) := by
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem sign_sum_upper_tail {N : ℕ} (s : Finset (Fin N)) {t : ℝ} (ht : 0≤t) :
    (Measure.pi (fun _ : Fin N => signLaw)).real {z | t≤∑ i ∈ s, z i}≤Real.exp (-t^2/(2*(s.card:ℝ))) := by
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (sign_coordinates_independent N)
    (c := fun _ => (1:NNReal)) (s := s) (fun i _ => coordinate_subgaussian i) ht
  simpa using h

theorem sign_sum_lower_tail {N : ℕ} (s : Finset (Fin N)) {t : ℝ} (ht : 0≤t) :
    (Measure.pi (fun _ : Fin N => signLaw)).real {z | (∑ i ∈ s, z i)≤-t}≤Real.exp (-t^2/(2*(s.card:ℝ))) := by
  have hs := HasSubgaussianMGF.sum_of_iIndepFun (sign_coordinates_independent N)
    (c := fun _ => (1:NNReal)) (s := s) (fun i _ => coordinate_subgaussian i)
  have h := hs.neg.measure_ge_le ht
  simpa only [Pi.neg_apply,le_neg,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,NNReal.coe_natCast] using h

theorem sign_sum_abs_tail {N : ℕ} (s : Finset (Fin N)) {t : ℝ} (ht : 0≤t) :
    (Measure.pi (fun _ : Fin N => signLaw)).real {z | t≤|∑ i ∈ s, z i|}≤2*Real.exp (-t^2/(2*(s.card:ℝ))) := by
  have he : {z : Fin N → ℝ | t≤|∑ i ∈ s, z i|}={z | t≤∑ i ∈ s, z i} ∪ {z | (∑ i ∈ s, z i)≤-t} := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_union,le_abs,le_neg]
  rw [he]
  have h := measureReal_union_le (μ := Measure.pi (fun _ : Fin N => signLaw)) {z | t≤∑ i ∈ s, z i} {z | (∑ i ∈ s, z i)≤-t}
  have hu := sign_sum_upper_tail s ht
  have hl := sign_sum_lower_tail s ht
  linarith

end Erdos524.SignConcentration
