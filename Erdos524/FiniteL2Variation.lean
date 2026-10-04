import Erdos524.FiniteChaining

namespace Erdos524.FiniteL2Variation
open MeasureTheory Filter
open Erdos524.FiniteChaining

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem integral_abs_product_le_sqrt {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    (∫ ω, |X ω| *|Y ω| ∂P)≤Real.sqrt (∫ ω, (X ω)^2 ∂P)*Real.sqrt (∫ ω, (Y ω)^2 ∂P) := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hX) (by simpa using hY)
  simpa only [Real.norm_eq_abs,Real.rpow_two,← Real.sqrt_eq_rpow,sq_abs] using h

theorem integral_squared_abs_sum_le {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (a : Fin n → ℝ) (ha : ∀ i, 0≤a i)
    (hbound : ∀ i, (∫ ω, (X i ω)^2 ∂P)≤(a i)^2) :
    (∫ ω, (∑ i, |X i ω|)^2 ∂P)≤(∑ i, a i)^2 := by
  have hAbs (i : Fin n) : MemLp (fun ω => |X i ω|) 2 P := by simpa only [Real.norm_eq_abs] using (hX i).norm
  have hi (i j : Fin n) : Integrable (fun ω => |X i ω| *|X j ω|) P := (hAbs i).integrable_mul (hAbs j)
  have he : (fun ω => (∑ i, |X i ω|)^2)=(fun ω => ∑ i, ∑ j, |X i ω| *|X j ω|) := by
    funext ω
    rw [pow_two,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  rw [he,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
  have hs (i : Fin n) : Real.sqrt (∫ ω, (X i ω)^2 ∂P)≤a i :=
    (Real.sqrt_le_sqrt (hbound i)).trans_eq (Real.sqrt_sq (ha i))
  calc
    _ ≤ ∑ i, ∑ j, a i*a j := by
      apply Finset.sum_le_sum
      intro i hi'
      apply Finset.sum_le_sum
      intro j hj'
      exact (integral_abs_product_le_sqrt (hX i) (hX j)).trans
        (mul_le_mul (hs i) (hs j) (Real.sqrt_nonneg _) (ha i))
    _ = _ := by rw [pow_two,Finset.sum_mul]; simp_rw [Finset.mul_sum]

theorem pi_norm_sq_le_sum {n : ℕ} (x : Fin n → ℝ) : ‖x‖^2≤∑ i, (x i)^2 := by
  have hs : 0≤∑ i, (x i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hnorm : ‖x‖≤Real.sqrt (∑ i, (x i)^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs]
    have hi := Finset.single_le_sum (s := Finset.univ) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    nlinarith [Real.sq_sqrt hs,abs_nonneg (x i),sq_abs (x i),Real.sqrt_nonneg (∑ i, (x i)^2)]
  nlinarith [Real.sq_sqrt hs,norm_nonneg x,Real.sqrt_nonneg (∑ i, (x i)^2)]

theorem integral_pi_norm_le_sqrt_sum [IsProbabilityMeasure P] {n : ℕ} (X : Ω → Fin n → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 P) :
    (∫ ω, ‖X ω‖ ∂P)≤Real.sqrt (∑ i, ∫ ω, (X ω i)^2 ∂P) := by
  have hv : MemLp X 2 P := memLp_pi_iff.mpr hX
  have hnorm : MemLp (fun ω => ‖X ω‖) 2 P := hv.norm
  have hi : Integrable (fun ω => ‖X ω‖^2) P := by simpa only [norm_norm] using hv.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hsq (i : Fin n) : Integrable (fun ω => (X ω i)^2) P := by
    simpa only [Real.norm_eq_abs,sq_abs] using (hX i).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hs := integral_mono hi (integrable_finsetSum _ (fun i _ => hsq i)) (fun ω => pi_norm_sq_le_sum (X ω))
  rw [integral_finsetSum _ (fun i _ => hsq i)] at hs
  have hb := integral_abs_le_sqrt_second_moment hnorm
  simp only [abs_of_nonneg (norm_nonneg _)] at hb
  exact hb.trans (Real.sqrt_le_sqrt hs)

end Erdos524.FiniteL2Variation
