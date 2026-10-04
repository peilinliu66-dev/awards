import Erdos524.AffineQuantileMeasure

/-! Affine sample moments from bounded-ramp layer-cake discrepancy. -/

namespace Erdos524.QuantileCounting

open Set MeasureTheory Filter
open scoped BigOperators
open Erdos524.LayercakeDiscrepancy

noncomputable def boundedRamp (a b x : ℝ) : ℝ := max 0 (min (b - a) (b - x))

theorem boundedRamp_nonneg (a b x : ℝ) : 0 ≤ boundedRamp a b x := le_max_left _ _

theorem boundedRamp_le {a b : ℝ} (hab : a ≤ b) (x : ℝ) : boundedRamp a b x ≤ b - a :=
  max_le (sub_nonneg.mpr hab) (min_le_left _ _)

theorem boundedRamp_on_interval {a b x : ℝ} (hx : x ∈ Icc a b) : boundedRamp a b x = b - x := by
  unfold boundedRamp
  rw [min_eq_right (by linarith [hx.1]), max_eq_right (by linarith [hx.2])]

theorem boundedRamp_superlevel {a b t : ℝ} (ht : t ∈ Ioc 0 (b - a)) :
    {x : ℝ | t ≤ boundedRamp a b x} = Iic (b - t) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Iic, boundedRamp, le_max_iff, le_min_iff]
  constructor
  · intro h
    rcases h with h | h
    · linarith [ht.1]
    · linarith [h.2]
  · intro h
    right
    exact ⟨ht.2, by linarith⟩

theorem boundedRamp_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a ≤ b) :
    Integrable (boundedRamp a b) μ :=
  Integrable.of_bound (by unfold boundedRamp; fun_prop) (b - a)
    (Eventually.of_forall (fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (boundedRamp_nonneg a b x)]
      exact boundedRamp_le hab x))

theorem boundedRamp_discrepancy (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a b : ℝ} (hab : a ≤ b)
    (hcdf : ∀ t : ℝ, |μ.real (Iic t) - ν.real (Iic t)| ≤ 1) :
    |(∫ x, boundedRamp a b x ∂μ) - (∫ x, boundedRamp a b x ∂ν)| ≤ b - a := by
  have h := integral_discrepancy_of_level_bound μ ν
    (f := boundedRamp a b) (by unfold boundedRamp; fun_prop)
    (sub_nonneg.mpr hab) (by norm_num : (0 : ℝ) ≤ 1)
    (boundedRamp_nonneg a b) (boundedRamp_le hab)
    (fun t ht ↦ by rw [boundedRamp_superlevel ht]; exact hcdf _)
  simpa only [one_mul] using h

theorem affineMeasure_total {a b A B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B) (hr : 0 ≤ A - B * b) :
    (affineMeasure a b A B).real univ = affineCDF a A B b := by
  have h := integral_affineMeasure (a := a) hB hr (fun _ ↦ (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at h
  rw [integral_affine_density hab] at h
  exact h

theorem affine_deficit_integral_decomposition {a b A B : ℝ}
    (hab : a ≤ b) (hB : 0 ≤ B) (hr : 0 ≤ A - B * b) (L : ℝ) :
    (∫ x, (L - x / 2) ∂affineMeasure a b A B) =
      affineCDF a A B b * (L - b / 2) + (1 / 2 : ℝ) *
        ∫ x, boundedRamp a b x ∂affineMeasure a b A B := by
  have hae : ∀ᵐ x ∂affineMeasure a b A B, x ∈ Icc a b :=
    (ae_restrict_mem measurableSet_Icc).filter_mono (withDensity_absolutelyContinuous _ _).ae_le
  calc
    _ = ∫ x, ((L - b / 2) + (1 / 2 : ℝ) * boundedRamp a b x) ∂affineMeasure a b A B := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [boundedRamp_on_interval hx]
      ring
    _ = _ := by
      rw [integral_add (integrable_const _) ((boundedRamp_integrable _ hab).const_mul _),
        integral_const, integral_const_mul, affineMeasure_total hab hB hr, smul_eq_mul]

theorem affine_quantile_deficit_discrepancy {a b A B : ℝ}
    (hab : a < b) (hB : 0 ≤ B) (hr : 0 < A - B * b)
    (mesh : QuantileMesh a b (affineCDF a A B) ⌊affineCDF a A B b⌋₊) (L : ℝ) :
    |(∑ i, (L - mesh.node i / 2)) -
      (∫ x in Icc a b, (A - B * x) * (L - x / 2))| ≤
        (b - a) / 2 + |L - b / 2| := by
  have hcdf : ∀ t : ℝ, |(empirical mesh.node).real (Iic t) -
      (affineMeasure a b A B).real (Iic t)| ≤ 1 := by
    intro t
    rw [affineMeasure_real_cdf hab.le hB hr.le]
    exact empirical_cdf_discrepancy mesh (affineCDF_strictMono hB hr) hab.le
      (affineCDF_left a A B) rfl (Nat.floor_le (affineCDF_total_pos hab hB hr).le)
      (Nat.lt_floor_add_one _).le t
  have hramp := boundedRamp_discrepancy (empirical mesh.node) (affineMeasure a b A B) hab.le hcdf
  rw [integral_empirical] at hramp
  have hmass : |(⌊affineCDF a A B b⌋₊ : ℝ) - affineCDF a A B b| ≤ 1 := by
    have h1 := Nat.floor_le (affineCDF_total_pos hab hB hr).le
    have h2 := Nat.lt_floor_add_one (affineCDF a A B b)
    rw [abs_le]
    constructor <;> linarith
  have hsum : (∑ i, (L - mesh.node i / 2)) =
      (⌊affineCDF a A B b⌋₊ : ℝ) * (L - b / 2) +
        (1 / 2 : ℝ) * ∑ i, boundedRamp a b (mesh.node i) := by
    have he (i) : L - mesh.node i / 2 = (L - b / 2) + (1 / 2 : ℝ) * boundedRamp a b (mesh.node i) := by
      rw [boundedRamp_on_interval (mesh.node_mem i)]
      ring
    simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
    ring
  rw [← integral_affineMeasure hB hr.le, affine_deficit_integral_decomposition hab.le hB hr.le,
    hsum]
  have he : (⌊affineCDF a A B b⌋₊ : ℝ) * (L - b / 2) + (1 / 2 : ℝ) *
      (∑ i, boundedRamp a b (mesh.node i)) -
      (affineCDF a A B b * (L - b / 2) + (1 / 2 : ℝ) *
        ∫ x, boundedRamp a b x ∂affineMeasure a b A B) =
      ((⌊affineCDF a A B b⌋₊ : ℝ) - affineCDF a A B b) * (L - b / 2) +
        (1 / 2 : ℝ) * ((∑ i, boundedRamp a b (mesh.node i)) -
          ∫ x, boundedRamp a b x ∂affineMeasure a b A B) := by ring
  rw [he]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h1 := mul_le_mul_of_nonneg_right hmass (abs_nonneg (L - b / 2))
  have h2 := mul_le_mul_of_nonneg_left hramp (by norm_num : (0 : ℝ) ≤ 1 / 2)
  linarith

end Erdos524.QuantileCounting
