import Erdos524.SignGaussianMoments
import Erdos524.PolynomialAbel
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Topology.ContinuousMap.Compact

/-! The actual infinite independent-sign model and the continuous supremum norm on [-1,1]. -/

namespace Erdos524.RandomPolynomialModel

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Erdos524.SignGaussianMoments

abbrev Ω := ℕ → ℝ
abbrev Interval := Set.Icc (-1 : ℝ) 1

noncomputable def P : Measure Ω := Measure.infinitePi (fun _ : ℕ ↦ signLaw)

instance : IsProbabilityMeasure P := by unfold P; infer_instance

noncomputable def basis (i : ℕ) : C(Interval, ℝ) :=
  ⟨fun x ↦ (x : ℝ) ^ (i + 1), by fun_prop⟩

noncomputable def polyCM (ω : Ω) (n : ℕ) : C(Interval, ℝ) :=
  ∑ i ∈ Finset.range n, ω i • basis i

noncomputable def fullNorm (ω : Ω) (n : ℕ) : ℝ := ‖polyCM ω n‖

noncomputable def finitePrefix (n : ℕ) (ω : Ω) : Fin n → ℝ := fun i ↦ ω i
noncomputable def finiteBlock (a n : ℕ) (ω : Ω) : Fin n → ℝ := fun i ↦ ω (a + i)

theorem polyCM_apply (ω : Ω) (n : ℕ) (x : Interval) :
    polyCM ω n x = ∑ i ∈ Finset.range n, ω i * (x : ℝ) ^ (i + 1) := by
  simp [polyCM, basis, ContinuousMap.sum_apply]

theorem polyCM_apply_fin (ω : Ω) (n : ℕ) (x : Interval) :
    polyCM ω n x = ∑ i : Fin n, ω i * (x : ℝ) ^ (i.val + 1) := by
  rw [polyCM_apply]
  exact (Fin.sum_univ_eq_sum_range (fun i ↦ ω i * (x : ℝ) ^ (i + 1)) n).symm

theorem polyCM_apply_polynomial (ω : Ω) (n : ℕ) (x : Interval) :
    polyCM ω n x = Erdos524.PolynomialAbel.polynomial ω n x := polyCM_apply ω n x

theorem fullNorm_nonneg (ω : Ω) (n : ℕ) : 0 ≤ fullNorm ω n := norm_nonneg _

theorem fullNorm_evaluation_bound (ω : Ω) (n : ℕ) (x : Interval) :
    |Erdos524.PolynomialAbel.polynomial ω n x| ≤ fullNorm ω n := by
  rw [← polyCM_apply_polynomial]
  exact (polyCM ω n).norm_coe_le_norm x

theorem fullNorm_le_iff (ω : Ω) (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    fullNorm ω n ≤ R ↔ ∀ x : Interval, |Erdos524.PolynomialAbel.polynomial ω n x| ≤ R := by
  unfold fullNorm
  rw [ContinuousMap.norm_le _ hR]
  simp only [Real.norm_eq_abs, polyCM_apply_polynomial]

theorem continuous_polyCM (n : ℕ) : Continuous (fun ω : Ω ↦ polyCM ω n) := by
  unfold polyCM
  fun_prop

theorem continuous_fullNorm (n : ℕ) : Continuous (fun ω : Ω ↦ fullNorm ω n) :=
  (continuous_polyCM n).norm

theorem measurable_fullNorm (n : ℕ) : Measurable (fun ω : Ω ↦ fullNorm ω n) :=
  (continuous_fullNorm n).measurable

theorem measurable_finitePrefix (n : ℕ) : Measurable (finitePrefix n) := by unfold finitePrefix; fun_prop

theorem measurable_finiteBlock (a n : ℕ) : Measurable (finiteBlock a n) := by unfold finiteBlock; fun_prop

theorem coordinate_independent : iIndepFun (fun i : ℕ ↦ fun ω : Ω ↦ ω i) P :=
  iIndepFun_infinitePi (X := fun _ : ℕ ↦ id) (fun _ ↦ measurable_id)

theorem coordinate_law (i : ℕ) : P.map (fun ω : Ω ↦ ω i) = signLaw :=
  Measure.infinitePi_map_eval (fun _ : ℕ ↦ signLaw) i

theorem finite_marginal_law {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) :
    P.map (fun ω : Ω ↦ fun i : Fin n ↦ ω (f i)) = Measure.pi (fun _ : Fin n ↦ signLaw) := by
  have h := (coordinate_independent.precomp hf).map_fun_eq_pi_map (fun i ↦ (show Measurable (fun ω : Ω ↦ ω (f i)) by fun_prop).aemeasurable)
  simpa only [coordinate_law] using h

theorem finitePrefix_law (n : ℕ) : P.map (finitePrefix n) = Measure.pi (fun _ : Fin n ↦ signLaw) :=
  finite_marginal_law Fin.val Fin.val_injective

theorem finiteBlock_law (a n : ℕ) : P.map (finiteBlock a n) = Measure.pi (fun _ : Fin n ↦ signLaw) := by
  apply finite_marginal_law
  intro i j hij
  apply Fin.ext
  dsimp at hij
  omega

end Erdos524.RandomPolynomialModel
