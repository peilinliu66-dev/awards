import Erdos524.IntegralGramComparison
import Erdos524.GaussianCovarianceComparison
import Erdos524.CauchyKernel
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The actual finite-interval Laplace covariance and a dominating weighted measure. -/

namespace Erdos524.LaplaceKernelComparison

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open Erdos524.IntegralGramComparison

noncomputable def intervalMeasure : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsFiniteMeasure intervalMeasure := by
  dsimp [intervalMeasure]
  infer_instance

noncomputable def dominationConstant : ℝ≥0∞ := ENNReal.ofReal (Real.exp 2 / 2)

noncomputable def dominatingMeasure : Measure ℝ := dominationConstant • expMeasure 2

instance : IsFiniteMeasure dominatingMeasure := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 2)
  refine ⟨?_⟩
  simp [dominatingMeasure, dominationConstant, Measure.smul_apply]

noncomputable def laplace (u s : ℝ) : ℝ := Real.exp (-u * s)

theorem ae_nonneg_expMeasure : ∀ᵐ s ∂expMeasure 2, 0 ≤ s := by
  change ∀ᵐ s ∂volume.withDensity (exponentialPDF 2), 0 ≤ s
  have hm : Measurable (exponentialPDF 2) := (measurable_exponentialPDFReal 2).ennreal_ofReal
  rw [ae_withDensity_iff hm]
  apply Eventually.of_forall
  intro s hs
  by_contra hn
  exact hs (exponentialPDF_of_neg (lt_of_not_ge hn))

theorem ae_nonneg_dominatingMeasure : ∀ᵐ s ∂dominatingMeasure, 0 ≤ s :=
  Measure.ae_smul_measure ae_nonneg_expMeasure dominationConstant

theorem memLp_laplace_interval {u : ℝ} (hu : 0 ≤ u) : MemLp (laplace u) 2 intervalMeasure := by
  apply MemLp.of_bound (by unfold laplace; fun_prop) 1
  change ∀ᵐ s ∂volume.restrict (Icc 0 1), ‖laplace u s‖ ≤ 1
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
  rw [laplace, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) hs.1)

theorem memLp_laplace_dominating {u : ℝ} (hu : 0 ≤ u) :
    MemLp (laplace u) 2 dominatingMeasure := by
  apply MemLp.of_bound (by unfold laplace; fun_prop) 1
  filter_upwards [ae_nonneg_dominatingMeasure] with s hs
  rw [laplace, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) hs)

theorem intervalMeasure_eq_withDensity :
    intervalMeasure = volume.withDensity ((Icc (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ≥0∞))) := by
  rw [withDensity_indicator measurableSet_Icc]
  change intervalMeasure = (volume.restrict (Icc (0 : ℝ) 1)).withDensity 1
  rw [withDensity_one]
  rfl

theorem dominatingMeasure_eq_withDensity :
    dominatingMeasure = volume.withDensity (fun s ↦ dominationConstant * exponentialPDF 2 s) := by
  change dominationConstant • volume.withDensity (exponentialPDF 2) = _
  exact (withDensity_smul dominationConstant
    ((measurable_exponentialPDFReal 2).ennreal_ofReal)).symm

theorem intervalMeasure_le_dominatingMeasure : intervalMeasure ≤ dominatingMeasure := by
  rw [intervalMeasure_eq_withDensity, dominatingMeasure_eq_withDensity]
  apply withDensity_mono
  apply Eventually.of_forall
  intro s
  by_cases hs : s ∈ Icc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hs]
    change (1 : ℝ≥0∞) ≤ dominationConstant * exponentialPDF 2 s
    rw [exponentialPDF_of_nonneg hs.1]
    unfold dominationConstant
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp 2 / 2)]
    have he : (Real.exp 2 / 2) * (2 * Real.exp (-(2 * s))) = Real.exp (2 - 2 * s) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    rw [he, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr (by linarith [hs.2]))
  · rw [Set.indicator_of_notMem hs]
    positivity

variable {n : ℕ}

noncomputable def finiteKernel (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  integralGram (fun i ↦ laplace (u i)) intervalMeasure

noncomputable def dominatingKernel (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  integralGram (fun i ↦ laplace (u i)) dominatingMeasure

theorem finiteKernel_posSemidef (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (finiteKernel u).PosSemidef :=
  integralGram_posSemidef _ _ (fun i ↦ memLp_laplace_interval (hu i))

theorem dominatingKernel_sub_finiteKernel_posSemidef
    (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (dominatingKernel u - finiteKernel u).PosSemidef :=
  integralGram_mono _ intervalMeasure_le_dominatingMeasure
    (fun i ↦ memLp_laplace_dominating (hu i))

theorem integral_laplace_expMeasure_two {q : ℝ} (hq : 0 ≤ q) :
    (∫ s, laplace q s ∂expMeasure 2) = 2 / (q + 2) := by
  have hm : Measurable (exponentialPDF 2) := (measurable_exponentialPDFReal 2).ennreal_ofReal
  have htop : ∀ᵐ s ∂(volume : Measure ℝ), exponentialPDF 2 s < ∞ :=
    Eventually.of_forall fun s ↦ ENNReal.ofReal_lt_top
  change (∫ s, laplace q s ∂volume.withDensity (exponentialPDF 2)) = _
  rw [integral_withDensity_eq_integral_toReal_smul hm htop]
  simp only [smul_eq_mul]
  have he : (fun s ↦ (exponentialPDF 2 s).toReal * laplace q s) =
      (Ici (0 : ℝ)).indicator (fun s ↦ 2 * Real.exp (-(q + 2) * s)) := by
    funext s
    by_cases hs : 0 ≤ s
    · rw [exponentialPDF_of_nonneg hs,
        ENNReal.toReal_ofReal (by positivity),
        Set.indicator_of_mem (show s ∈ Ici (0 : ℝ) from hs)]
      unfold laplace
      calc
        2 * Real.exp (-(2 * s)) * Real.exp (-q * s) =
            2 * (Real.exp (-(2 * s)) * Real.exp (-q * s)) := by ring
        _ = 2 * Real.exp (-(q + 2) * s) := by
          rw [← Real.exp_add]
          congr 2
          ring
    · rw [exponentialPDF_of_neg (lt_of_not_ge hs), ENNReal.toReal_zero,
        zero_mul, Set.indicator_of_notMem (show s ∉ Ici (0 : ℝ) from hs)]
  rw [he, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_exp_mul_Ioi (by linarith : -(q + 2) < 0) 0]
  simp
  have hq2 : q + 2 ≠ 0 := by linarith
  have hneg : -2 + -q ≠ 0 := by linarith
  field_simp
  <;> ring

theorem dominatingKernel_apply (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (i j : Fin n) :
    dominatingKernel u i j = Real.exp 2 / (u i + u j + 2) := by
  change (∫ s, laplace (u i) s * laplace (u j) s ∂dominatingMeasure) = _
  have he : (fun s ↦ laplace (u i) s * laplace (u j) s) = laplace (u i + u j) := by
    funext s
    unfold laplace
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  unfold dominatingMeasure
  rw [integral_smul_measure, integral_laplace_expMeasure_two (add_nonneg (hu i) (hu j))]
  unfold dominationConstant
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul]
  ring

theorem integral_laplace_interval (q : ℝ) :
    (∫ s, laplace q s ∂intervalMeasure) =
      if q = 0 then 1 else (1 - Real.exp (-q)) / q := by
  by_cases hq : q = 0
  · subst q
    simp [laplace, intervalMeasure, Real.volume_Icc]
  · rw [if_neg hq]
    change (∫ s in Icc (0 : ℝ) 1, Real.exp (-q * s)) = _
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hq),
      integral_exp]
    simp only [mul_zero, mul_one, Real.exp_zero, smul_eq_mul, inv_neg]
    ring

theorem finiteKernel_apply (u : Fin n → ℝ) (i j : Fin n) :
    finiteKernel u i j = if u i + u j = 0 then 1 else
      (1 - Real.exp (-(u i + u j))) / (u i + u j) := by
  change (∫ s, laplace (u i) s * laplace (u j) s ∂intervalMeasure) = _
  have he : (fun s ↦ laplace (u i) s * laplace (u j) s) = laplace (u i + u j) := by
    funext s
    unfold laplace
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, integral_laplace_interval]

theorem dominatingKernel_eq_shiftedCauchy (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) :
    dominatingKernel u = Real.exp 2 • Erdos524.CauchyKernel.cauchy (fun i ↦ u i + 1) := by
  ext i j
  rw [dominatingKernel_apply u hu]
  change Real.exp 2 / (u i + u j + 2) =
    Real.exp 2 * (1 / ((u i + 1) + (u j + 1)))
  congr 1
  ring

theorem finite_laplace_gaussian_comparison (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 ≤ u i)
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hclosed : IsClosed K) (hconvex : Convex ℝ K)
    (hneg : ∀ ⦃y⦄, y ∈ K → -y ∈ K) :
    (multivariateGaussian 0
      (Real.exp 2 • Erdos524.CauchyKernel.cauchy (fun i ↦ u i + 1))) K ≤
      (multivariateGaussian 0 (finiteKernel u)) K := by
  rw [← dominatingKernel_eq_shiftedCauchy u hu]
  exact Erdos524.GaussianCovarianceComparison.multivariate_gaussian_covariance_mono
    (finiteKernel_posSemidef u hu) (dominatingKernel_sub_finiteKernel_posSemidef u hu)
    hclosed hconvex hneg

end Erdos524.LaplaceKernelComparison
