import Erdos524.EmpiricalQuantileMeasure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Erdos524.QuantileCounting
open Set MeasureTheory Filter

noncomputable def affineMeasure (a b A B : ℝ) : Measure ℝ :=
  (volume.restrict (Icc a b)).withDensity (fun x => ENNReal.ofReal (A-B*x))

instance affineMeasure_finite (a b A B : ℝ) : IsFiniteMeasure (affineMeasure a b A B) := by
  have hc : Continuous (fun x : ℝ => A-B*x) := by fun_prop
  exact isFiniteMeasure_withDensity_ofReal (hc.integrableOn_Icc (μ := volume)).hasFiniteIntegral

theorem integral_affine_density {a s A B : ℝ} (has : a≤s) :
    ∫ x in Icc a s, (A-B*x) = affineCDF a A B s := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le has]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => A) (g := fun x : ℝ => B*x)
    (continuous_const.intervalIntegrable _ _)
    ((show Continuous (fun x : ℝ => B*x) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id]
  simp only [smul_eq_mul]
  unfold affineCDF
  ring

theorem affineMeasure_real_prefix {a b A B s : ℝ} (hB : 0≤B) (hr : 0≤A-B*b)
    (hs : s ∈ Icc a b) :
    (affineMeasure a b A B).real (Iic s)=affineCDF a A B s := by
  have hinter : Iic s ∩ Icc a b=Icc a s := by
    ext x
    simp only [mem_inter_iff,mem_Iic,mem_Icc]
    constructor
    · intro h; exact ⟨h.2.1,h.1⟩
    · intro h; exact ⟨h.2,h.1,h.2.trans hs.2⟩
  rw [measureReal_def,affineMeasure,withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic,hinter]
  rw [← integral_eq_lintegral_of_nonneg_ae]
  · exact integral_affine_density hs.1
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have h := mul_le_mul_of_nonneg_left (hx.2.trans hs.2) hB
    change 0≤A-B*x
    linarith
  · exact (show Continuous (fun x : ℝ => A-B*x) by fun_prop).aestronglyMeasurable

theorem affineMeasure_singleton (a b A B x : ℝ) : affineMeasure a b A B {x}=0 := by
  apply withDensity_absolutelyContinuous _ _
  exact measure_singleton x


theorem affineMeasure_real_cdf {a b A B : ℝ} (hab : a≤b) (hB : 0≤B) (hr : 0≤A-B*b) (s : ℝ) :
    (affineMeasure a b A B).real (Iic s)=clampedCDF a b (affineCDF a A B) s := by
  classical
  unfold clampedCDF
  by_cases hsa : s<a
  · rw [if_pos hsa]
    have hinter : Iic s ∩ Icc a b=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have h1 := hx.1
      have h2 := hx.2.1
      exact not_le_of_gt (lt_of_lt_of_le hsa h2) h1
    rw [measureReal_def,affineMeasure,withDensity_apply _ measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic,hinter]
    simp
  · rw [if_neg hsa]
    by_cases hbs : b<s
    · rw [if_pos hbs]
      have he : (affineMeasure a b A B).real (Iic s)=(affineMeasure a b A B).real (Iic b) := by
        have h1 : Iic s ∩ Icc a b=Icc a b := inter_eq_right.mpr (fun x hx => hx.2.trans hbs.le)
        have h2 : Iic b ∩ Icc a b=Icc a b := inter_eq_right.mpr (fun _ hx => hx.2)
        simp only [measureReal_def,affineMeasure,withDensity_apply _ measurableSet_Iic,
          Measure.restrict_restrict measurableSet_Iic,h1,h2]
      rw [he]
      exact affineMeasure_real_prefix hB hr (right_mem_Icc.mpr hab)
    · rw [if_neg hbs]
      exact affineMeasure_real_prefix hB hr ⟨le_of_not_gt hsa,le_of_not_gt hbs⟩

theorem affine_quantile_potential_discrepancy {a b A B τ : ℝ}
    (hab : a<b) (hB : 0≤B) (hr : 0<A-B*b) (hτ : 0<τ)
    (mesh : QuantileMesh a b (affineCDF a A B) ⌊affineCDF a A B b⌋₊) (t : ℝ) :
    |(∑ i, Erdos524.CauchyKernel.truncatedPotential τ (mesh.node i-t))-
      (∫ x, Erdos524.CauchyKernel.truncatedPotential τ (x-t) ∂affineMeasure a b A B)|≤
      3*Erdos524.CauchyKernel.logTanhPotential τ := by
  have hcdf : ∀ s : ℝ, |(empirical mesh.node).real (Iic s)-(affineMeasure a b A B).real (Iic s)|≤1 := by
    intro s
    rw [affineMeasure_real_cdf hab.le hB hr.le]
    exact empirical_cdf_discrepancy mesh (affineCDF_strictMono hB hr) hab.le
      (affineCDF_left a A B) rfl (Nat.floor_le (affineCDF_total_pos hab hB hr).le)
      (Nat.lt_floor_add_one _).le s
  have hatom : ∀ s : ℝ, |(empirical mesh.node).real {s}-(affineMeasure a b A B).real {s}|≤1 := by
    intro s
    rw [measureReal_def (μ := affineMeasure a b A B),affineMeasure_singleton]
    simp only [ENNReal.toReal_zero,sub_zero,abs_of_nonneg measureReal_nonneg]
    exact empirical_atom_le_one mesh.node (mesh.strictMono (affineCDF_strictMono hB hr)).injective s
  have he := Erdos524.CDFDiscrepancy.truncated_discrepancy_of_cdf (empirical mesh.node)
    (affineMeasure a b A B) (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤1) hτ hcdf hatom t
  rw [integral_empirical] at he
  norm_num at he
  exact he


theorem integral_affineMeasure {a b A B : ℝ} (hB : 0≤B) (hr : 0≤A-B*b) (f : ℝ → ℝ) :
    (∫ x, f x ∂affineMeasure a b A B) = ∫ x in Icc a b, (A-B*x)*f x := by
  unfold affineMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x : ℝ => ENNReal.ofReal (A-B*x)) by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hnonneg : 0≤A-B*x := by
    have h := mul_le_mul_of_nonneg_left hx.2 hB
    linarith
  rw [ENNReal.toReal_ofReal hnonneg,smul_eq_mul]

end Erdos524.QuantileCounting
