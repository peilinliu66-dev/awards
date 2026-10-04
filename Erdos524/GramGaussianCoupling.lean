import Erdos524.IntegralGramComparison
import Erdos524.GaussianCoordinateProjection
import Erdos524.FiniteCouplingComparison

namespace Erdos524.GramGaussianCoupling
open MeasureTheory ProbabilityTheory Matrix WithLp
open Erdos524.IntegralGramComparison Erdos524.FiniteGaussianTailBound
open Erdos524.GaussianCoordinateProjection Erdos524.FiniteCouplingComparison

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}

noncomputable def jointFamily (f g : Fin d → Ω → ℝ) : Fin (d+d) → Ω → ℝ := Fin.addCases f g

theorem jointFamily_memLp (f g : Fin d → Ω → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ) :
    ∀ i, MemLp (jointFamily f g i) 2 μ := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [jointFamily,Fin.addCases_left] using hf j
  · simpa only [jointFamily,Fin.addCases_right] using hg j

theorem gram_increment (f g : Fin d → Ω → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ) (j : Fin d) :
    (integralGram (jointFamily f g) μ) (Fin.castAdd d j) (Fin.castAdd d j)-
      2*(integralGram (jointFamily f g) μ) (Fin.castAdd d j) (Fin.natAdd d j)+
      (integralGram (jointFamily f g) μ) (Fin.natAdd d j) (Fin.natAdd d j)=
      ∫ ω, (f j ω-g j ω)^2 ∂μ := by
  simp only [integralGram,jointFamily,Fin.addCases_left,Fin.addCases_right]
  have hff : Integrable (fun ω => f j ω*f j ω) μ := (hf j).integrable_mul (hf j)
  have hfg : Integrable (fun ω => 2*(f j ω*g j ω)) μ := ((hf j).integrable_mul (hg j)).const_mul 2
  have hgg : Integrable (fun ω => g j ω*g j ω) μ := (hg j).integrable_mul (hg j)
  have hsub : Integrable (fun ω => f j ω*f j ω-2*(f j ω*g j ω)) μ := hff.sub hfg
  rw [← integral_const_mul,← integral_sub hff hfg,← integral_add hsub hgg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by ring)

theorem joint_increment_second_moment (f g : Fin d → Ω → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ) (j : Fin d) :
    (∫ z : EuclideanSpace ℝ (Fin (d+d)), (z (Fin.castAdd d j)-z (Fin.natAdd d j))^2
      ∂multivariateGaussian 0 (integralGram (jointFamily f g) μ))=
      ∫ ω, (f j ω-g j ω)^2 ∂μ := by
  rw [gaussian_increment_second_moment (integralGram_posSemidef _ _ (jointFamily_memLp f g hf hg))]
  exact gram_increment f g hf hg j

theorem joint_left_law (f g : Fin d → Ω → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ) :
    (multivariateGaussian 0 (integralGram (jointFamily f g) μ)).map
      (fun z : EuclideanSpace ℝ (Fin (d+d)) => fun j : Fin d => z (Fin.castAdd d j))=
      (multivariateGaussian 0 (integralGram f μ)).map ofLp := by
  have h := gaussian_coordinate_projection (integralGram_posSemidef _ _ (jointFamily_memLp f g hf hg)) (Fin.castAdd d)
  have he : (integralGram (jointFamily f g) μ).submatrix (Fin.castAdd d) (Fin.castAdd d)=integralGram f μ := by
    ext i j
    simp only [Matrix.submatrix_apply,integralGram,jointFamily,Fin.addCases_left]
  rw [he] at h
  exact h

theorem joint_right_law (f g : Fin d → Ω → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ) :
    (multivariateGaussian 0 (integralGram (jointFamily f g) μ)).map
      (fun z : EuclideanSpace ℝ (Fin (d+d)) => fun j : Fin d => z (Fin.natAdd d j))=
      (multivariateGaussian 0 (integralGram g μ)).map ofLp := by
  have h := gaussian_coordinate_projection (integralGram_posSemidef _ _ (jointFamily_memLp f g hf hg)) (Fin.natAdd d)
  have he : (integralGram (jointFamily f g) μ).submatrix (Fin.natAdd d) (Fin.natAdd d)=integralGram g μ := by
    ext i j
    simp only [Matrix.submatrix_apply,integralGram,jointFamily,Fin.addCases_right]
  rw [he] at h
  exact h

noncomputable def gramBoxProbability (f : Fin d → Ω → ℝ) (μ : Measure Ω) (r : ℝ) : ℝ :=
  (multivariateGaussian 0 (integralGram f μ)).real {z : EuclideanSpace ℝ (Fin d) | ∀ j, |z j|≤r}

theorem gram_box_probability_comparison (f g : Fin d → Ω → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ) {η : ℝ} (hη : 0<η) (r : ℝ) :
    gramBoxProbability f μ r≤gramBoxProbability g μ (r+η)+(∑ j, ∫ ω, (f j ω-g j ω)^2 ∂μ)/η^2 := by
  let P := multivariateGaussian 0 (integralGram (jointFamily f g) μ)
  let X : EuclideanSpace ℝ (Fin (d+d)) → Fin d → ℝ := fun z j => z (Fin.castAdd d j)
  let Y : EuclideanSpace ℝ (Fin (d+d)) → Fin d → ℝ := fun z j => z (Fin.natAdd d j)
  have hL (j : Fin d) : MemLp (fun z => X z j-Y z j) 2 P :=
    (gaussian_coordinate_memLp_two _ _).sub (gaussian_coordinate_memLp_two _ _)
  have h := box_probability_comparison (P := P) X Y (by intro j; fun_prop) (by intro j; fun_prop) hL hη r
  have heX : P.real (box X r)=gramBoxProbability f μ r := by
    have hm := congrArg (fun ν : Measure (Fin d → ℝ) => ν.real (box id r)) (joint_left_law f g hf hg)
    have hbox : MeasurableSet (box (id : (Fin d → ℝ) → Fin d → ℝ) r) := box_measurable id (by intro j; fun_prop) r
    simp only [Measure.real] at hm
    rw [Measure.map_apply (by fun_prop) hbox,Measure.map_apply (by fun_prop) hbox] at hm
    exact hm
  have heY : P.real (box Y (r+η))=gramBoxProbability g μ (r+η) := by
    have hm := congrArg (fun ν : Measure (Fin d → ℝ) => ν.real (box id (r+η))) (joint_right_law f g hf hg)
    have hbox : MeasurableSet (box (id : (Fin d → ℝ) → Fin d → ℝ) (r+η)) := box_measurable id (by intro j; fun_prop) (r+η)
    simp only [Measure.real] at hm
    rw [Measure.map_apply (by fun_prop) hbox,Measure.map_apply (by fun_prop) hbox] at hm
    exact hm
  rw [heX,heY] at h
  have he (j : Fin d) : (∫ z, (X z j-Y z j)^2 ∂P)=∫ ω, (f j ω-g j ω)^2 ∂μ :=
    joint_increment_second_moment f g hf hg j
  simpa only [he] using h

end Erdos524.GramGaussianCoupling
