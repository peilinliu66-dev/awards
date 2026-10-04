import Erdos524.SoftMaximumDerivatives

namespace Erdos524.SoftMaximum

theorem abs_five_term_le (a b c d e : ℝ) :
    |a-b-c+d-e|≤|a|+|b|+|c|+|d|+|e| := by
  calc
    _ ≤ |a-b-c+d|+|e| := abs_sub _ _
    _ ≤ (|a-b-c|+|d|)+|e| := by gcongr; exact abs_add_le _ _
    _ ≤ ((|a-b|+|c|)+|d|)+|e| := by gcongr; exact abs_sub _ _
    _ ≤ (((|a|+|b|)+|c|)+|d|)+|e| := by gcongr; exact abs_sub _ _
    _ = _ := by ring

theorem cumulant_second_bound {m1 m2 a : ℝ} (ha : 0≤a) (h1 : |m1|≤a) (h2 : |m2|≤a^2) :
    |m2-m1^2|≤2*a^2 := by
  have h := abs_sub m2 (m1^2)
  rw [abs_pow] at h
  have hp := pow_le_pow_left₀ (abs_nonneg m1) h1 2
  nlinarith

theorem cumulant_third_bound {m1 m2 m3 a : ℝ} (ha : 0≤a)
    (h1 : |m1|≤a) (h2 : |m2|≤a^2) (h3 : |m3|≤a^3) :
    |m3-3*m2*m1+2*m1^3|≤6*a^3 := by
  have hsub := abs_sub m3 (3*m2*m1)
  have hadd := abs_add_le (m3-3*m2*m1) (2*m1^3)
  norm_num [abs_mul,abs_pow] at hsub hadd
  calc
    _ ≤ |m3|+3*|m2| * |m1|+2*|m1|^3 := by linarith
    _ ≤ a^3+3*a^2*a+2*a^3 := by gcongr
    _ = _ := by ring

theorem cumulant_fourth_bound {m1 m2 m3 m4 a : ℝ} (ha : 0≤a)
    (h1 : |m1|≤a) (h2 : |m2|≤a^2) (h3 : |m3|≤a^3) (h4 : |m4|≤a^4) :
    |m4-4*m3*m1-3*m2^2+12*m2*m1^2-6*m1^4|≤26*a^4 := by
  have h := abs_five_term_le m4 (4*m3*m1) (3*m2^2) (12*m2*m1^2) (6*m1^4)
  norm_num [abs_mul,abs_pow] at h
  calc
    _ ≤ |m4|+4*|m3| * |m1|+3*|m2|^2+12*|m2| * |m1|^2+6*|m1|^4 := by simpa only [sq_abs] using h
    _ ≤ a^4+4*a^3*a+3*(a^2)^2+12*a^2*a^2+6*a^4 := by gcongr
    _ = _ := by ring

theorem softSecond_abs_le {n : ℕ} (hn : 0<n) {β a : ℝ} (hβ : 0≤β) (ha : 0≤a)
    (x v : Fin n → ℝ) (hv : ∀ i, |v i|≤a) (t : ℝ) :
    |softSecond β x v t|≤2*β*a^2 := by
  have h1 := directionalMoment_abs_le hn β x v ha hv 1 t
  have h2 := directionalMoment_abs_le hn β x v ha hv 2 t
  simp only [pow_one] at h1
  unfold softSecond
  rw [abs_mul,abs_of_nonneg hβ]
  have h := mul_le_mul_of_nonneg_left (cumulant_second_bound ha h1 h2) hβ
  nlinarith

theorem softThird_abs_le {n : ℕ} (hn : 0<n) {β a : ℝ} (hβ : 0≤β) (ha : 0≤a)
    (x v : Fin n → ℝ) (hv : ∀ i, |v i|≤a) (t : ℝ) :
    |softThird β x v t|≤6*β^2*a^3 := by
  have h1 := directionalMoment_abs_le hn β x v ha hv 1 t
  have h2 := directionalMoment_abs_le hn β x v ha hv 2 t
  have h3 := directionalMoment_abs_le hn β x v ha hv 3 t
  simp only [pow_one] at h1
  unfold softThird
  rw [abs_mul,abs_of_nonneg (sq_nonneg β)]
  have h := mul_le_mul_of_nonneg_left (cumulant_third_bound ha h1 h2 h3) (sq_nonneg β)
  nlinarith

theorem softFourth_abs_le {n : ℕ} (hn : 0<n) {β a : ℝ} (hβ : 0≤β) (ha : 0≤a)
    (x v : Fin n → ℝ) (hv : ∀ i, |v i|≤a) (t : ℝ) :
    |softFourth β x v t|≤26*β^3*a^4 := by
  have h1 := directionalMoment_abs_le hn β x v ha hv 1 t
  have h2 := directionalMoment_abs_le hn β x v ha hv 2 t
  have h3 := directionalMoment_abs_le hn β x v ha hv 3 t
  have h4 := directionalMoment_abs_le hn β x v ha hv 4 t
  simp only [pow_one] at h1
  unfold softFourth
  rw [abs_mul,abs_of_nonneg (pow_nonneg hβ 3)]
  have h := mul_le_mul_of_nonneg_left (cumulant_fourth_bound ha h1 h2 h3 h4) (pow_nonneg hβ 3)
  nlinarith

end Erdos524.SoftMaximum
