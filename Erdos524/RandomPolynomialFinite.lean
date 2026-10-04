import Erdos524.RandomPolynomialModel

/-! Finite continuous-polynomial laws and fresh-block distributions. -/

namespace Erdos524.RandomPolynomialModel

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Erdos524.SignGaussianMoments

noncomputable def finitePolyCM {n : ℕ} (z : Fin n → ℝ) : C(Interval, ℝ) :=
  ∑ i : Fin n, z i • basis i.val

noncomputable def finiteNorm {n : ℕ} (z : Fin n → ℝ) : ℝ := ‖finitePolyCM z‖

noncomputable def freshNorm (a n : ℕ) (ω : Ω) : ℝ := finiteNorm (finiteBlock a n ω)

theorem finitePolyCM_apply {n : ℕ} (z : Fin n → ℝ) (x : Interval) :
    finitePolyCM z x = ∑ i : Fin n, z i * (x : ℝ) ^ (i.val + 1) := by
  simp [finitePolyCM, basis, ContinuousMap.sum_apply]

theorem finitePolyCM_prefix (ω : Ω) (n : ℕ) : finitePolyCM (finitePrefix n ω) = polyCM ω n := by
  ext x
  rw [finitePolyCM_apply, polyCM_apply_fin]
  rfl

theorem finiteNorm_prefix (ω : Ω) (n : ℕ) : finiteNorm (finitePrefix n ω) = fullNorm ω n :=
  congrArg norm (finitePolyCM_prefix ω n)

theorem continuous_finiteNorm (n : ℕ) : Continuous (finiteNorm (n := n)) := by
  unfold finiteNorm finitePolyCM
  fun_prop

theorem measurable_finiteNorm (n : ℕ) : Measurable (finiteNorm (n := n)) :=
  (continuous_finiteNorm n).measurable

theorem measurable_freshNorm (a n : ℕ) : Measurable (freshNorm a n) :=
  (measurable_finiteNorm n).comp (measurable_finiteBlock a n)

theorem fullNorm_law (n : ℕ) :
    P.map (fun ω ↦ fullNorm ω n) = (Measure.pi (fun _ : Fin n ↦ signLaw)).map finiteNorm := by
  rw [← finitePrefix_law n, Measure.map_map (measurable_finiteNorm n) (measurable_finitePrefix n)]
  congr 1
  funext ω
  exact (finiteNorm_prefix ω n).symm

theorem freshNorm_law (a n : ℕ) :
    P.map (freshNorm a n) = (Measure.pi (fun _ : Fin n ↦ signLaw)).map finiteNorm := by
  rw [← finiteBlock_law a n, Measure.map_map (measurable_finiteNorm n) (measurable_finiteBlock a n)]
  rfl

theorem freshNorm_event_law (a n : ℕ) (R : ℝ) :
    P {ω | freshNorm a n ω ≤ R} = P {ω | fullNorm ω n ≤ R} := by
  have h := congrArg (fun μ : Measure ℝ ↦ μ (Iic R)) ((freshNorm_law a n).trans (fullNorm_law n).symm)
  rw [Measure.map_apply (measurable_freshNorm a n) measurableSet_Iic,
    Measure.map_apply (measurable_fullNorm n) measurableSet_Iic] at h
  exact h

theorem fullNorm_finite_event_law (n : ℕ) (R : ℝ) :
    P {ω | fullNorm ω n ≤ R} = (Measure.pi (fun _ : Fin n ↦ signLaw)) {z | finiteNorm z ≤ R} := by
  have h := congrArg (fun μ : Measure ℝ ↦ μ (Iic R)) (fullNorm_law n)
  rw [Measure.map_apply (measurable_fullNorm n) measurableSet_Iic,
    Measure.map_apply (measurable_finiteNorm n) measurableSet_Iic] at h
  exact h

end Erdos524.RandomPolynomialModel
