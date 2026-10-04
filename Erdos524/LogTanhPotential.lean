import Erdos524.CauchyLogGeometry
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

namespace Erdos524.CauchyKernel
open scoped BigOperators
open MeasureTheory Set

noncomputable def logTanhPotential (x : ℝ) : ℝ := -Real.log (Real.tanh (x / 2))

theorem tanh_half_exp (x : ℝ) :
    Real.tanh (x / 2) = (1 - Real.exp (-x)) / (1 + Real.exp (-x)) := by
  simpa only [Real.exp_zero, zero_sub, neg_neg] using (cauchy_ratio_exp 0 (-x)).symm

theorem logTanhPotential_eq_logs {x : ℝ} (hx : 0 < x) :
    logTanhPotential x = Real.log (1 + Real.exp (-x)) - Real.log (1 - Real.exp (-x)) := by
  have he : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hp := Real.exp_pos (-x)
  unfold logTanhPotential
  rw [tanh_half_exp, Real.log_div (by linarith) (by linarith)]
  ring

theorem logTanhPotential_pos {x : ℝ} (hx : 0 < x) : 0 < logTanhPotential x := by
  have he : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hp := Real.exp_pos (-x)
  have ht : 0 < Real.tanh (x/2) := by rw [tanh_half_exp]; positivity
  exact neg_pos.mpr (Real.log_neg ht (Real.tanh_lt_one _))

theorem hasSum_logTanhPotential {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) *
      Real.exp (-((2 * k + 1 : ℕ) : ℝ) * x)) (logTanhPotential x) := by
  have he : |Real.exp (-x)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]; linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one he
  rw [← logTanhPotential_eq_logs hx] at hs
  convert hs using 1
  ext k
  rw [← Real.exp_nat_mul]
  congr 2
  ring


theorem hasSum_odd_reciprocal_sq :
    HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ)^2) (Real.pi^2/8) := by
  have hs := hasSum_zeta_two.summable
  have ho : Summable (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ)^2) :=
    hs.comp_injective (by intro a b h; dsimp at h; omega)
  have he : HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ)^2) (Real.pi^2/24) := by
    convert hasSum_zeta_two.mul_left (1/4 : ℝ) using 1
    · ext k
      simp only [Nat.cast_mul, Nat.cast_ofNat, mul_pow, div_mul_eq_div_mul_one_div]
      ring
    · ring
  have hsum := tsum_even_add_odd (f := fun k : ℕ => (1 : ℝ) / (k : ℝ)^2) he.summable ho
  rw [he.tsum_eq, hasSum_zeta_two.tsum_eq] at hsum
  convert ho.hasSum using 1
  linarith

noncomputable def potentialTerm (k : ℕ) (x : ℝ) : ℝ :=
  2 * (1 / (2 * k + 1)) * Real.exp (-((2 * k + 1 : ℕ) : ℝ) * x)

theorem potentialTerm_nonneg (k : ℕ) (x : ℝ) : 0 ≤ potentialTerm k x := by
  unfold potentialTerm
  positivity

theorem potentialTerm_integrable (k : ℕ) : IntegrableOn (potentialTerm k) (Ioi 0) := by
  apply Integrable.const_mul
  exact integrableOn_exp_mul_Ioi (by simp only [neg_lt_zero]; positivity) 0

theorem integral_potentialTerm (k : ℕ) :
    ∫ x in Ioi (0 : ℝ), potentialTerm k x = 2 / ((2 * k + 1 : ℕ) : ℝ)^2 := by
  unfold potentialTerm
  rw [integral_const_mul, integral_exp_mul_Ioi (by simp only [neg_lt_zero]; positivity)]
  simp only [mul_zero, Real.exp_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  field_simp
  <;> ring

theorem integral_logTanhPotential :
    ∫ x in Ioi (0 : ℝ), logTanhPotential x = Real.pi^2/4 := by
  have hsum : Summable (fun k : ℕ => ∫ x in Ioi (0 : ℝ), ‖potentialTerm k x‖) := by
    simp only [Real.norm_eq_abs, abs_of_nonneg (potentialTerm_nonneg _ _), integral_potentialTerm]
    convert hasSum_odd_reciprocal_sq.summable.mul_left 2 using 1
    ext k
    ring
  have hswap := integral_tsum_of_summable_integral_norm potentialTerm_integrable hsum
  have heq : (∫ x in Ioi (0 : ℝ), ∑' k, potentialTerm k x) =
      ∫ x in Ioi (0 : ℝ), logTanhPotential x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact (hasSum_logTanhPotential hx).tsum_eq
  rw [heq] at hswap
  rw [← hswap]
  simp only [integral_potentialTerm]
  have hs := hasSum_odd_reciprocal_sq.mul_left 2
  convert hs.tsum_eq using 1
  · congr 1
    ext k
    ring
  · ring


theorem integrable_logTanhPotential : IntegrableOn logTanhPotential (Ioi 0) := by
  by_contra h
  have he := integral_logTanhPotential
  rw [integral_undef h] at he
  have hp := Real.pi_pos
  nlinarith [sq_pos_of_pos hp]

theorem logTanhPotential_antitone : AntitoneOn logTanhPotential (Ioi 0) := by
  intro x hx y hy hxy
  apply hasSum_le ?_ (hasSum_logTanhPotential hy) (hasSum_logTanhPotential hx)
  intro k
  have hk : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  apply mul_le_mul_of_nonneg_left
  · exact Real.exp_le_exp.mpr (by nlinarith)
  · positivity

theorem logTanhPotential_tail {x : ℝ} (hx : Real.log 2 ≤ x) :
    logTanhPotential x ≤ 4 * Real.exp (-x) := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.log_pos (by norm_num)) hx
  have hq : Real.exp (-x) ≤ 1/2 := by
    rw [Real.exp_neg]
    have he : (2 : ℝ) ≤ Real.exp x := by
      simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr hx
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) he
  have hp := Real.exp_pos (-x)
  have hd : 0 < 1 - Real.exp (-x) := by linarith
  have he := Real.log_le_sub_one_of_pos
    (div_pos (by positivity : 0 < 1 + Real.exp (-x)) hd)
  rw [Real.log_div (by positivity) (ne_of_gt hd)] at he
  rw [logTanhPotential_eq_logs hxpos]
  have hr : (1 + Real.exp (-x)) / (1 - Real.exp (-x)) - 1 ≤ 4 * Real.exp (-x) := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hd).mpr
    nlinarith
  linarith

theorem tanh_half_lower {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    x / 4 ≤ Real.tanh (x / 2) := by
  have he := Real.add_one_le_exp x
  have ht : Real.tanh (x/2) = (Real.exp x - 1) / (Real.exp x + 1) := by
    simpa only [Real.exp_zero, sub_zero] using (cauchy_ratio_exp x 0).symm
  rw [ht]
  apply (le_div_iff₀ (by positivity : 0 < Real.exp x + 1)).mpr
  nlinarith [mul_nonneg (by linarith : 0 ≤ 4-x) (sub_nonneg.mpr he)]

theorem logTanhPotential_near_zero {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    logTanhPotential x ≤ Real.log (4 / x) := by
  have h := Real.log_le_log (by positivity : 0 < x/4) (tanh_half_lower hx hx1)
  unfold logTanhPotential
  have he : Real.log (4/x) = -Real.log (x/4) := by
    rw [Real.log_div (by norm_num) (ne_of_gt hx),
      Real.log_div (ne_of_gt hx) (by norm_num)]
    ring
  rw [he]
  linarith


theorem integral_scaled_logTanhPotential {r : ℝ} (hr : 0 < r) :
    ∫ x in Ioi (0 : ℝ), logTanhPotential (x/r) = r * (Real.pi^2/4) := by
  have h := integral_comp_mul_left_Ioi logTanhPotential 0 (inv_pos.mpr hr)
  simpa only [inv_mul_eq_div, mul_zero, inv_inv, smul_eq_mul,
    integral_logTanhPotential] using h

theorem integrable_scaled_logTanhPotential {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x => logTanhPotential (x/r)) (Ioi 0) := by
  by_contra h
  have he := integral_scaled_logTanhPotential hr
  rw [integral_undef h] at he
  have hp : 0 < r * (Real.pi^2/4) := by positivity
  linarith

theorem sum_logTanhPotential_mesh_le {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ∑ k ∈ Finset.range m, logTanhPotential ((k+1 : ℕ)/r) ≤ r * (Real.pi^2/4) := by
  have hanti : AntitoneOn (fun x : ℝ => logTanhPotential (x/r)) (Ioc 0 (0 + m)) := by
    intro x hx y hy hxy
    exact logTanhPotential_antitone (div_pos hx.1 hr) (div_pos hy.1 hr)
      (div_le_div_of_nonneg_right hxy hr.le)
  have hi := integrable_scaled_logTanhPotential hr
  have hIoc : IntegrableOn (fun x : ℝ => logTanhPotential (x/r)) (Ioc 0 (0+m)) :=
    hi.mono_set (fun _ hx => hx.1)
  have hIcc : IntegrableOn (fun x : ℝ => logTanhPotential (x/r)) (Icc 0 (0+m)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc (by simp)]
    exact hIoc
  have hsum := hanti.sum_le_integral_of_integrableOn hIcc
  simp only [zero_add] at hsum
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun x => logTanhPotential (x/r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (logTanhPotential_pos (div_pos hx hr)).le
  have hmono := setIntegral_mono_set hi hnonneg
    (Filter.Eventually.of_forall (fun x (hx : x ∈ Ioc (0 : ℝ) m) => hx.1))
  rw [integral_scaled_logTanhPotential hr] at hmono
  rw [intervalIntegral.integral_of_le (by positivity)] at hsum
  exact hsum.trans hmono


theorem block_pair_energy_le {r : ℝ} (hr : 0 < r) (m : ℕ) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.Ico (i+1) m,
      logTanhPotential ((j-i : ℕ)/r)) ≤ (m : ℝ) * r * (Real.pi^2/4) := by
  have hrow (i : ℕ) : (∑ j ∈ Finset.Ico (i+1) m,
      logTanhPotential ((j-i : ℕ)/r)) ≤ r * (Real.pi^2/4) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have he : (fun k : ℕ => logTanhPotential (((i+1+k)-i : ℕ)/r)) =
        (fun k : ℕ => logTanhPotential ((k+1 : ℕ)/r)) := by
      funext k
      have hh : i+1+k-i = k+1 := by omega
      rw [hh]
    simp only [he]
    exact sum_logTanhPotential_mesh_le hr (m-(i+1))
  calc
    _ ≤ ∑ _i ∈ Finset.range m, r * (Real.pi^2/4) := Finset.sum_le_sum (fun i _ => hrow i)
    _ = _ := by simp; ring

end Erdos524.CauchyKernel
