import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace Erdos524.ProductCoordinateReplacement
open MeasureTheory Filter

 theorem integral_prod_difference_le {α : Type*} [MeasurableSpace α]
    (μ ν : Measure ℝ) (P : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure P]
    (f : ℝ × α → ℝ) (hf : Measurable f) (hbound : ∀ z, ‖f z‖≤1) {B : ℝ}
    (hinner : ∀ y, |(∫ t, f (t,y) ∂μ)-(∫ t, f (t,y) ∂ν)|≤B) :
    |(∫ z, f z ∂μ.prod P)-(∫ z, f z ∂ν.prod P)|≤B := by
  have hμ : Integrable f (μ.prod P) := Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall hbound)
  have hν : Integrable f (ν.prod P) := Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall hbound)
  rw [integral_prod_symm f hμ,integral_prod_symm f hν,← integral_sub hμ.integral_prod_right hν.integral_prod_right]
  have he := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun y => (∫ t, f (t,y) ∂μ)-(∫ t, f (t,y) ∂ν))
    (Eventually.of_forall hinner)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using he

noncomputable def insertCoordinate {n : ℕ} (i : Fin (n+1)) (t : ℝ) (y : Fin n → ℝ) : Fin (n+1) → ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm (t,y)

theorem integral_pi_change_one {n : ℕ} (μ ν : Fin (n+1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, IsProbabilityMeasure (ν j)]
    (i : Fin (n+1)) (hsame : ∀ j : Fin n, μ (i.succAbove j)=ν (i.succAbove j))
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : Measurable f) (hbound : ∀ z, ‖f z‖≤1) {B : ℝ}
    (hinner : ∀ y : Fin n → ℝ,
      |(∫ t, f (insertCoordinate i t y) ∂μ i)-(∫ t, f (insertCoordinate i t y) ∂ν i)|≤B) :
    |(∫ z, f z ∂Measure.pi μ)-(∫ z, f z ∂Measure.pi ν)|≤B := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hμ := (measurePreserving_piFinSuccAbove μ i).symm
  have hν := (measurePreserving_piFinSuccAbove ν i).symm
  rw [← hμ.integral_comp' f,← hν.integral_comp' f]
  have hP : Measure.pi (fun j : Fin n => μ (i.succAbove j))=
      Measure.pi (fun j : Fin n => ν (i.succAbove j)) := by
    congr 1
    funext j
    exact hsame j
  rw [← hP]
  apply integral_prod_difference_le (μ i) (ν i) (Measure.pi (fun j : Fin n => μ (i.succAbove j)))
    (fun z => f (e.symm z)) (hf.comp e.symm.measurable) (fun z => hbound (e.symm z))
  exact hinner

end Erdos524.ProductCoordinateReplacement
