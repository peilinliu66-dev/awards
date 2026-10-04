import Erdos524.RandomPolynomialFinite
import Erdos524.UniformPolynomialTail

/-! Actual full-norm Gaussian-type tail bound from the two sign walks. -/

namespace Erdos524.RandomPolynomialModel

open Set MeasureTheory ProbabilityTheory
open Erdos524.SignGaussianMoments Erdos524.FiniteSignWalk
open Erdos524.FinitePolynomialAbel Erdos524.UniformPolynomialTail

theorem finiteNorm_le_max_walk {N : ℕ} (z : Fin N → ℝ) :
    finiteNorm z ≤ max (walkMax z) (walkMax (alternatingVector z)) := by
  apply (ContinuousMap.norm_le _ ((norm_nonneg _).trans (le_max_left _ _))).mpr
  intro x
  rw [Real.norm_eq_abs, finitePolyCM_apply]
  change |finitePolynomial z x| ≤ _
  by_cases hx : 0 ≤ (x : ℝ)
  · exact (finitePolynomial_abs_le_walkMax z hx x.property.2).trans (le_max_left _ _)
  · have hn : 0 ≤ -(x : ℝ) := by linarith
    have hn1 : -(x : ℝ) ≤ 1 := by linarith [x.property.1]
    have he : finitePolynomial z x = finitePolynomial (alternatingVector z) (-(x : ℝ)) := by
      simpa only [neg_neg] using finitePolynomial_neg_argument z (-(x : ℝ))
    rw [he]
    exact (finitePolynomial_abs_le_walkMax _ hn hn1).trans (le_max_right _ _)

theorem finiteNorm_tail {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun _ : Fin N ↦ signLaw)).real {z | t ≤ finiteNorm z} ≤
      4 * Real.exp (-t ^ 2 / (2 * (N : ℝ))) := by
  let μ := Measure.pi (fun _ : Fin N ↦ signLaw)
  let E := {z : Fin N → ℝ | t ≤ walkMax z}
  have hm : MeasurableSet E := measurableSet_le measurable_const (walkMax_continuous N).measurable
  have hA : Measurable (alternatingVector (N := N)) := by unfold alternatingVector; fun_prop
  have hlaw := congrArg (fun ν : Measure (Fin N → ℝ) ↦ ν.real E) (alternatingVector_map N)
  unfold Measure.real at hlaw
  rw [Measure.map_apply hA hm] at hlaw
  have hs : {z : Fin N → ℝ | t ≤ finiteNorm z} ⊆ E ∪ alternatingVector ⁻¹' E := by
    intro z hz
    exact le_max_iff.mp (hz.trans (finiteNorm_le_max_walk z))
  have hbound : μ.real E ≤ 2 * Real.exp (-t ^ 2 / (2 * (N : ℝ))) := by
    rw [show E = absHitEvent N t from walkMax_level_eq ht]
    exact abs_maximal_hoeffding hN ht.le
  have hsub := measureReal_mono hs (by finiteness : μ (E ∪ alternatingVector ⁻¹' E) ≠ ⊤)
  have hu := measureReal_union_le (μ := μ) E (alternatingVector ⁻¹' E)
  change μ.real (alternatingVector ⁻¹' E) = μ.real E at hlaw
  rw [hlaw] at hu
  exact hsub.trans (hu.trans (by linarith))

theorem fullNorm_tail {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ fullNorm ω N} ≤ 4 * Real.exp (-t ^ 2 / (2 * (N : ℝ))) := by
  have h := congrArg (fun μ : Measure ℝ ↦ μ.real (Ici t)) (fullNorm_law N)
  unfold Measure.real at h
  rw [Measure.map_apply (measurable_fullNorm N) measurableSet_Ici,
    Measure.map_apply (measurable_finiteNorm N) measurableSet_Ici] at h
  change P.real {ω | t ≤ fullNorm ω N} =
    (Measure.pi (fun _ : Fin N ↦ signLaw)).real {z | t ≤ finiteNorm z} at h
  rw [h]
  exact finiteNorm_tail hN ht

end Erdos524.RandomPolynomialModel
