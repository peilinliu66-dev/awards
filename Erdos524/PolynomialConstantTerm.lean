import Erdos524.RandomPolynomialModel
import Erdos524.SignConcentration
import Erdos524.NormalizerGrowth

/-! The original constant coefficient and the shift of the independent-sign sequence. -/

namespace Erdos524.RandomPolynomialModel

open Set Filter MeasureTheory ProbabilityTheory
open Erdos524.SignGaussianMoments Erdos524.SignConcentration

noncomputable def shift (ω : Ω) : Ω := fun i ↦ ω (i + 1)
noncomputable def withConstantPolyCM (ω : Ω) (n : ℕ) : C(Interval, ℝ) :=
  ContinuousMap.const Interval (ω 0) + polyCM (shift ω) n
noncomputable def withConstantNorm (ω : Ω) (n : ℕ) : ℝ := ‖withConstantPolyCM ω n‖

theorem measurable_shift : Measurable shift := by unfold shift; fun_prop

theorem shift_law : P.map shift = P := by
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ ↦ signLaw) Nat.succ_injective

theorem withConstantPolyCM_apply (ω : Ω) (n : ℕ) (x : Interval) :
    withConstantPolyCM ω n x = ω 0 + ∑ i ∈ Finset.range n, ω (i + 1) * (x : ℝ) ^ (i + 1) := by
  simp only [withConstantPolyCM, ContinuousMap.add_apply, ContinuousMap.const_apply, polyCM_apply, shift]

theorem withConstantPolyCM_sum_range (ω : Ω) (n : ℕ) (x : Interval) :
    withConstantPolyCM ω n x = ∑ i ∈ Finset.range (n + 1), ω i * (x : ℝ) ^ i := by
  rw [withConstantPolyCM_apply, Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  ring

theorem withConstantNorm_nonneg (ω : Ω) (n : ℕ) : 0 ≤ withConstantNorm ω n := norm_nonneg _

theorem withConstantNorm_difference (ω : Ω) (n : ℕ) :
    |withConstantNorm ω n - fullNorm (shift ω) n| ≤ |ω 0| := by
  have h := abs_norm_sub_norm_le (withConstantPolyCM ω n) (polyCM (shift ω) n)
  have he : withConstantPolyCM ω n - polyCM (shift ω) n = ContinuousMap.const Interval (ω 0) := by
    unfold withConstantPolyCM
    abel
  rw [he] at h
  have hconst : ‖ContinuousMap.const Interval (ω 0)‖ ≤ |ω 0| := by
    apply (ContinuousMap.norm_le _ (abs_nonneg _)).mpr
    intro x
    exact le_rfl
  exact h.trans hconst

theorem ae_constant_bounded : ∀ᵐ ω ∂P, |ω 0| ≤ 1 := by
  have h := signLaw_ae_interval
  rw [← coordinate_law 0] at h
  have h' := ae_of_ae_map (show AEMeasurable (fun ω : Ω ↦ ω 0) P from (by fun_prop : Measurable (fun ω : Ω ↦ ω 0)).aemeasurable) h
  filter_upwards [h'] with ω hω
  exact abs_le.mpr hω

theorem ae_withConstantNorm_difference :
    ∀ᵐ ω ∂P, ∀ n, |withConstantNorm ω n - fullNorm (shift ω) n| ≤ 1 := by
  filter_upwards [ae_constant_bounded] with ω hω
  intro n
  exact (withConstantNorm_difference ω n).trans hω

end Erdos524.RandomPolynomialModel
