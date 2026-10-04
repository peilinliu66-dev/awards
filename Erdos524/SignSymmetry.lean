import Erdos524.SignConcentration

namespace Erdos524.SignSymmetry
open MeasureTheory ProbabilityTheory
open Erdos524.SignGaussianMoments

theorem signLaw_map_neg : signLaw.map (fun x : ℝ => -x)=signLaw := by
  unfold signLaw
  rw [Measure.map_add _ _ (by fun_prop),Measure.map_smul _ (by fun_prop),Measure.map_smul _ (by fun_prop),
    Measure.map_dirac,Measure.map_dirac]
  norm_num
  exact add_comm _ _

theorem pi_sign_map_neg (N : ℕ) :
    (Measure.pi (fun _ : Fin N => signLaw)).map (fun z : Fin N → ℝ => fun i => -z i)=
      Measure.pi (fun _ : Fin N => signLaw) := by
  rw [Measure.pi_map_pi (fun _ => (show Measurable (fun x : ℝ => -x) by fun_prop).aemeasurable)]
  simp only [signLaw_map_neg]

theorem signLaw_map_phase {a : ℝ} (ha : a^2=1) : signLaw.map (fun x : ℝ => a*x)=signLaw := by
  have h : a=1 ∨ a=-1 := sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa using ha)
  rcases h with h|h
  · subst a; simp
  · subst a; simpa only [neg_one_mul] using signLaw_map_neg

theorem pi_sign_map_phases {N : ℕ} (a : Fin N → ℝ) (ha : ∀ i, (a i)^2=1) :
    (Measure.pi (fun _ : Fin N => signLaw)).map (fun z : Fin N → ℝ => fun i => a i*z i)=
      Measure.pi (fun _ : Fin N => signLaw) := by
  rw [Measure.pi_map_pi (fun i => (show Measurable (fun x : ℝ => a i*x) by fun_prop).aemeasurable)]
  simp_rw [signLaw_map_phase (ha _)]

end Erdos524.SignSymmetry
