import Erdos524.FiniteSignWalk

namespace Erdos524.FiniteSignWalk
open MeasureTheory ProbabilityTheory Filter Set
open Erdos524.SignGaussianMoments Erdos524.ProductCoordinateReplacement

theorem integral_pi_sign_head {N : ℕ} (f : (Fin (N+1) → ℝ) → ℝ)
    (hf : Measurable f) (hb : ∀ z, ‖f z‖≤1) :
    (∫ z, f z ∂Measure.pi (fun _ : Fin (N+1) => signLaw))=
      ∫ a, (∫ y, f (Fin.cons a y) ∂Measure.pi (fun _ : Fin N => signLaw)) ∂signLaw := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => ℝ) (0 : Fin (N+1))
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => signLaw) (0 : Fin (N+1))).symm
  rw [← hmp.integral_comp' f]
  have hi : Integrable (fun z : ℝ × (Fin N → ℝ) => f (e.symm z))
      (signLaw.prod (Measure.pi (fun _ : Fin N => signLaw))) :=
    Integrable.of_bound (hf.comp e.symm.measurable).aestronglyMeasurable 1 (Eventually.of_forall (fun z => hb (e.symm z)))
  rw [integral_prod _ hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro a
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  change f (insertCoordinate (0 : Fin (N+1)) a y)=f (Fin.cons a y)
  rw [insertCoordinate_zero]

theorem hitProbability_recursion {N : ℕ} {t s : ℝ} (hs : s<t) :
    hitProbability (N+1) t s=(hitProbability N t (s-1)+hitProbability N t (s+1))/2 := by
  classical
  let f : (Fin (N+1) → ℝ) → ℝ := (hitEvent (N+1) t s).indicator 1
  have hf : Measurable f := measurable_const.indicator (hitEvent_measurable (N+1) t s)
  have hb : ∀ z, ‖f z‖≤1 := by
    intro z
    by_cases hz : z∈hitEvent (N+1) t s <;> simp [f,Set.indicator,hz]
  have he (a : ℝ) : (∫ y, f (Fin.cons a y) ∂Measure.pi (fun _ : Fin N => signLaw))=hitProbability N t (s+a) := by
    rw [hitProbability,← integral_indicator_one (hitEvent_measurable N t (s+a))]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    have hiff : Fin.cons a y∈hitEvent (N+1) t s ↔ y∈hitEvent N t (s+a) := by
      rw [hitEvent_cons_iff]
      simp only [not_le.mpr hs,false_or]
    change (if Fin.cons a y∈hitEvent (N+1) t s then (1:ℝ) else 0)=(if y∈hitEvent N t (s+a) then 1 else 0)
    rw [hiff]
  rw [hitProbability,← integral_indicator_one (hitEvent_measurable (N+1) t s)]
  change (∫ z, f z ∂Measure.pi (fun _ : Fin (N+1) => signLaw))=_
  rw [integral_pi_sign_head f hf hb]
  simp_rw [he]
  rw [integral_signLaw]
  simp only [sub_eq_add_neg]

end Erdos524.FiniteSignWalk
