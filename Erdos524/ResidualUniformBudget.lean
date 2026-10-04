import Erdos524.CauchyResidualBounds

/-! A uniform residual budget for arbitrary finite evaluations on [1,infinity). -/

namespace Erdos524.ResidualUniformBudget

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators
open Erdos524.CauchyKernel Erdos524.CauchyGaussianRegression Erdos524.CauchyResidualBounds

variable {n m k l : ℕ}

theorem blaschke_abs_le_one (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) {v : ℝ} (hv : 0 < v) :
    |blaschke x v| ≤ 1 := by
  unfold blaschke numerator denominator
  rw [← Finset.prod_div_distrib, Finset.abs_prod]
  apply Finset.prod_le_one₀ (fun i _ ↦ abs_nonneg _)
  intro i hi
  rw [abs_div, abs_of_pos (add_pos hv (hx i)), div_le_one (add_pos hv (hx i))]
  exact abs_le.mpr ⟨by linarith [hx i], by linarith [hx i]⟩

theorem norm_le_sum_restrictions (z : Fin m → ℝ) (f : Fin k → Fin m) (g : Fin l → Fin m)
    (hcover : ∀ j, (∃ i, f i = j) ∨ ∃ i, g i = j) :
    ‖z‖ ≤ ‖fun i ↦ z (f i)‖ + ‖fun i ↦ z (g i)‖ := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro j
  rcases hcover j with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact (norm_le_pi_norm (fun i ↦ z (f i)) i).trans (le_add_of_nonneg_right (norm_nonneg _))
  · exact (norm_le_pi_norm (fun i ↦ z (g i)) i).trans (le_add_of_nonneg_left (norm_nonneg _))

theorem integral_residual_cover_le (x : Fin n → ℝ) (v : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (hv : ∀ j, 0 < v j)
    (f : Fin k → Fin m) (g : Fin l → Fin m)
    (hcover : ∀ j, (∃ i, f i = j) ∨ ∃ i, g i = j) :
    (∫ z, ‖cauchyResidual x v z‖ ∂jointMeasure x v) ≤
      (∫ z, ‖cauchyResidual x (fun i ↦ v (f i)) z‖ ∂jointMeasure x (fun i ↦ v (f i))) +
      (∫ z, ‖cauchyResidual x (fun i ↦ v (g i)) z‖ ∂jointMeasure x (fun i ↦ v (g i))) := by
  have hF := (residual_gaussian x v).map_fun
    (ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj (f i)))
  have hG := (residual_gaussian x v).map_fun
    (ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj (g i)))
  have h := integral_mono (residual_gaussian x v).integrable.norm
    (hF.integrable.norm.add hG.integrable.norm)
    (fun z ↦ norm_le_sum_restrictions (cauchyResidual x v z) f g hcover)
  simp only [Pi.add_apply] at h
  rw [integral_add hF.integrable.norm hG.integrable.norm] at h
  have hfeq := congrArg (fun μ : Measure (Fin k → ℝ) ↦ ∫ z, ‖z‖ ∂μ)
    (residual_subvector_law x v hx hinj hv f)
  have hgeq := congrArg (fun μ : Measure (Fin l → ℝ) ↦ ∫ z, ‖z‖ ∂μ)
    (residual_subvector_law x v hx hinj hv g)
  change HasGaussianLaw (fun z ↦ fun i ↦ cauchyResidual x v z (f i)) (jointMeasure x v) at hF
  change HasGaussianLaw (fun z ↦ fun i ↦ cauchyResidual x v z (g i)) (jointMeasure x v) at hG
  rw [integral_map hF.aemeasurable (by fun_prop),
    integral_map (residual_gaussian x _).aemeasurable (by fun_prop)] at hfeq
  rw [integral_map hG.aemeasurable (by fun_prop),
    integral_map (residual_gaussian x _).aemeasurable (by fun_prop)] at hgeq
  change (∫ z, ‖cauchyResidual x v z‖ ∂jointMeasure x v) ≤
    (∫ z, ‖fun i ↦ cauchyResidual x v z (f i)‖ ∂jointMeasure x v) +
    (∫ z, ‖fun i ↦ cauchyResidual x v z (g i)‖ ∂jointMeasure x v) at h
  rwa [hfeq, hgeq] at h

theorem integral_residual_tail_any_le (x : Fin n → ℝ) (v : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    {T : ℝ} (hT : 0 < T) (hv : ∀ j, T ≤ v j) :
    (∫ z, ‖cauchyResidual x v z‖ ∂jointMeasure x v) ≤ 1 / Real.sqrt T := by
  cases m with
  | zero =>
    have he (z) : ‖cauchyResidual x v z‖ = 0 := by
      rw [show cauchyResidual x v z = 0 from Subsingleton.elim _ _, norm_zero]
    simp only [he, integral_zero]
    positivity
  | succ m =>
    simpa using integral_residual_tail_unordered_le x v hx hinj hT hv (by norm_num : (0:ℝ)≤1)
      (fun j ↦ blaschke_abs_le_one x hx (hT.trans_le (hv j)))

theorem integral_residual_core_any_le (x : Fin n → ℝ) (v : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    {T b : ℝ} (hT : 1 ≤ T) (hb : 0 ≤ b)
    (hlo : ∀ j, 1 ≤ v j) (hhi : ∀ j, v j ≤ T)
    (hB : ∀ j, |blaschke x (v j)| ≤ b * Real.sqrt (v j)) :
    (∫ z, ‖cauchyResidual x v z‖ ∂jointMeasure x v) ≤ b * (1 + Real.log T / Real.sqrt 8) := by
  cases m with
  | zero =>
    have he (z) : ‖cauchyResidual x v z‖ = 0 := by
      rw [show cauchyResidual x v z = 0 from Subsingleton.elim _ _, norm_zero]
    simp only [he, integral_zero]
    have := Real.log_nonneg hT
    positivity
  | succ m =>
    have hv (j) : 0 < v j := lt_of_lt_of_le (by norm_num) (hlo j)
    have he : (fun j ↦ Real.exp (Real.log (v j))) = v := funext (fun j ↦ Real.exp_log (hv j))
    have h := integral_residual_core_unordered_le x (fun j ↦ Real.log (v j)) hx hinj
      (fun j ↦ Real.log_nonneg (hlo j)) (fun j ↦ Real.log_le_log (hv j) (hhi j)) hb
      (fun j ↦ by simpa only [Real.exp_log (hv j)] using hB j)
    rw [he] at h
    simpa only [sub_zero] using h

theorem integral_residual_uniform_le (x : Fin n → ℝ) (v : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (hv : ∀ j, 1 ≤ v j)
    {T b : ℝ} (hT : 1 ≤ T) (hb : 0 ≤ b)
    (hB : ∀ u : ℝ, 1 ≤ u → u ≤ T → |blaschke x u| ≤ b * Real.sqrt u) :
    (∫ z, ‖cauchyResidual x v z‖ ∂jointMeasure x v) ≤
      b * (1 + Real.log T / Real.sqrt 8) + 1 / Real.sqrt T := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter (fun j ↦ v j ≤ T)
  let f : Fin s.card → Fin m := fun i ↦ (s.equivFin.symm i).val
  let g : Fin sᶜ.card → Fin m := fun i ↦ (sᶜ.equivFin.symm i).val
  have hcover (j : Fin m) : (∃ i, f i = j) ∨ ∃ i, g i = j := by
    by_cases hj : j ∈ s
    · left
      refine ⟨s.equivFin ⟨j, hj⟩, ?_⟩
      exact congrArg Subtype.val (s.equivFin.symm_apply_apply ⟨j, hj⟩)
    · right
      have hj' : j ∈ sᶜ := Finset.mem_compl.mpr hj
      refine ⟨sᶜ.equivFin ⟨j, hj'⟩, ?_⟩
      exact congrArg Subtype.val (sᶜ.equivFin.symm_apply_apply ⟨j, hj'⟩)
  have hcore (i : Fin s.card) : v (f i) ≤ T :=
    (Finset.mem_filter.mp (s.equivFin.symm i).property).2
  have htail (i : Fin sᶜ.card) : T ≤ v (g i) := by
    have hnot : g i ∉ s := Finset.mem_compl.mp (sᶜ.equivFin.symm i).property
    apply le_of_lt
    apply lt_of_not_ge
    intro hi
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  refine (integral_residual_cover_le x v hx hinj (fun j ↦ lt_of_lt_of_le (by norm_num) (hv j))
    f g hcover).trans ?_
  exact add_le_add
    (integral_residual_core_any_le x (fun i ↦ v (f i)) hx hinj hT hb
      (fun i ↦ hv (f i)) hcore (fun i ↦ hB _ (hv (f i)) (hcore i)))
    (integral_residual_tail_any_le x (fun i ↦ v (g i)) hx hinj
      (lt_of_lt_of_le (by norm_num) hT) htail)

end Erdos524.ResidualUniformBudget
