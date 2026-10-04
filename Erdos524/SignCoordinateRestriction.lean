import Erdos524.SignConcentration

namespace Erdos524.SignCoordinateRestriction
open MeasureTheory ProbabilityTheory
open Erdos524.SignGaussianMoments Erdos524.SignConcentration

theorem pi_sign_restriction {N m : ℕ} (f : Fin m → Fin N) (hf : Function.Injective f) :
    (Measure.pi (fun _ : Fin N => signLaw)).map (fun z => fun j => z (f j))=
      Measure.pi (fun _ : Fin m => signLaw) := by
  have hi := (sign_coordinates_independent N).precomp hf
  have he := hi.map_fun_eq_pi_map (fun j => (measurable_pi_apply (f j)).aemeasurable)
  simp only [(measurePreserving_eval (fun _ : Fin N => signLaw) (f _)).map_eq] at he
  exact he

theorem integral_pi_sign_restriction {N m : ℕ} (f : Fin m → Fin N) (hf : Function.Injective f)
    (g : (Fin m → ℝ) → ℝ) (hg : Measurable g) :
    (∫ z, g (fun j => z (f j)) ∂Measure.pi (fun _ : Fin N => signLaw))=
      ∫ y, g y ∂Measure.pi (fun _ : Fin m => signLaw) := by
  have hm : Measurable (fun z : Fin N → ℝ => fun j => z (f j)) := by fun_prop
  rw [← pi_sign_restriction f hf,integral_map hm.aemeasurable hg.aestronglyMeasurable]

theorem integrable_pi_sign_restriction {N m : ℕ} (f : Fin m → Fin N) (hf : Function.Injective f)
    (g : (Fin m → ℝ) → ℝ) (hg : Integrable g (Measure.pi (fun _ : Fin m => signLaw))) :
    Integrable (fun z => g (fun j => z (f j))) (Measure.pi (fun _ : Fin N => signLaw)) := by
  have hm : MeasurePreserving (fun z : Fin N → ℝ => fun j => z (f j))
      (Measure.pi (fun _ : Fin N => signLaw)) (Measure.pi (fun _ : Fin m => signLaw)) :=
    ⟨by fun_prop,pi_sign_restriction f hf⟩
  exact hm.integrable_comp_of_integrable hg

end Erdos524.SignCoordinateRestriction
