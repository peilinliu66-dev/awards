import Erdos524.LogCauchyInverse

/-! Conditional-mean coefficient bounds, with sample coincidences handled exactly. -/

namespace Erdos524.RegressionWeightBounds

open scoped BigOperators
open Erdos524.CauchyKernel

variable {n : ℕ}

noncomputable def omittedPotential (s : Fin n → ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, logTanhPotential |t - s j|

theorem tanh_half_ne_zero {d : ℝ} (hd : d ≠ 0) : Real.tanh (d / 2) ≠ 0 := by
  rw [← sub_zero d, ← cauchy_ratio_exp d 0, Real.exp_zero]
  apply div_ne_zero
  · intro h
    have he : Real.exp d = Real.exp 0 := by simpa using sub_eq_zero.mp h
    exact hd (Real.exp_injective he)
  · positivity

theorem abs_tanh_eq_exp_neg_potential {d : ℝ} (hd : d ≠ 0) :
    |Real.tanh (d / 2)| = Real.exp (-logTanhPotential |d|) := by
  rw [← log_tanh_potential_abs]
  exact (Real.exp_log_eq_abs (tanh_half_ne_zero hd)).symm

theorem abs_tanh_le_exp_neg_potential (d : ℝ) :
    |Real.tanh (d / 2)| ≤ Real.exp (-logTanhPotential |d|) := by
  by_cases hd : d = 0
  · subst d
    simp [logTanhPotential]
  · exact (abs_tanh_eq_exp_neg_potential hd).le

theorem abs_normalizedWeight_le_potentials (s : Fin n → ℝ) (hs : Function.Injective s)
    (i : Fin n) (t : ℝ) :
    |normalizedWeight (fun j ↦ Real.exp (s j)) i (Real.exp t)| ≤
      (1 / Real.cosh ((t - s i) / 2)) *
        Real.exp (omittedPotential s i (s i) - omittedPotential s i t) := by
  rw [normalizedWeight_exp, abs_mul, abs_div, abs_one,
    abs_of_pos (Real.cosh_pos _), Finset.abs_prod]
  simp_rw [abs_div]
  rw [Finset.prod_div_distrib]
  have hden : (∏ j ∈ Finset.univ.erase i, |Real.tanh ((s i - s j) / 2)|) =
      Real.exp (-omittedPotential s i (s i)) := by
    have he (j : Fin n) (hj : j ∈ Finset.univ.erase i) :
        |Real.tanh ((s i - s j) / 2)| = Real.exp (-logTanhPotential |s i - s j|) :=
      abs_tanh_eq_exp_neg_potential (sub_ne_zero.mpr (fun h ↦ (Finset.mem_erase.mp hj).1 (hs h).symm))
    rw [Finset.prod_congr rfl he, ← Real.exp_sum]
    simp only [omittedPotential, Finset.sum_neg_distrib]
  have hnum : (∏ j ∈ Finset.univ.erase i, |Real.tanh ((t - s j) / 2)|) ≤
      Real.exp (-omittedPotential s i t) := by
    calc
      _ ≤ ∏ j ∈ Finset.univ.erase i, Real.exp (-logTanhPotential |t - s j|) :=
        Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) (fun _ _ ↦ abs_tanh_le_exp_neg_potential _)
      _ = _ := by rw [← Real.exp_sum]; simp only [omittedPotential, Finset.sum_neg_distrib]
  rw [hden]
  have he : Real.exp (-omittedPotential s i t) / Real.exp (-omittedPotential s i (s i)) =
      Real.exp (omittedPotential s i (s i) - omittedPotential s i t) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  exact mul_le_mul_of_nonneg_left
    ((div_le_div_of_nonneg_right hnum (Real.exp_pos _).le).trans_eq he) (by positivity)

theorem regressionWeight_exp_normalized (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    regressionWeight (fun j ↦ Real.exp (s j)) i (Real.exp t) =
      Real.exp ((s i - t) / 2) * normalizedWeight (fun j ↦ Real.exp (s j)) i (Real.exp t) := by
  unfold normalizedWeight
  rw [sqrt_exp_half, sqrt_exp_half,
    show (s i - t) / 2 = s i / 2 - t / 2 by ring, Real.exp_sub]
  field_simp

theorem abs_regressionWeight_core_le (s : Fin n → ℝ) (hs : Function.Injective s)
    (i : Fin n) (t L A B : ℝ)
    (hrow : omittedPotential s i (s i) ≤ L - s i / 2 + A)
    (hpoint : L - t / 2 + B ≤ omittedPotential s i t) :
    |regressionWeight (fun j ↦ Real.exp (s j)) i (Real.exp t)| ≤ Real.exp (A - B) := by
  rw [regressionWeight_exp_normalized, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h := abs_normalizedWeight_le_potentials s hs i t
  have hc : 1 / Real.cosh ((t - s i) / 2) ≤ 1 :=
    (div_le_one (Real.cosh_pos _)).mpr (by
      have hsq := Real.cosh_sq ((t - s i) / 2)
      nlinarith [sq_nonneg (Real.sinh ((t - s i) / 2)), Real.cosh_pos ((t - s i) / 2)])
  have he : omittedPotential s i (s i) - omittedPotential s i t ≤ (t - s i) / 2 + A - B := by
    linarith
  calc
    _ ≤ Real.exp ((s i - t) / 2) *
        ((1 / Real.cosh ((t - s i) / 2)) * Real.exp (omittedPotential s i (s i) - omittedPotential s i t)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ ≤ Real.exp ((s i - t) / 2) * Real.exp ((t - s i) / 2 + A - B) := by
      gcongr
      exact (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans (by simpa using Real.exp_le_exp.mpr he)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem regressionWeight_at_sample (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x) (i j : Fin n) :
    regressionWeight x i (x j) = if i = j then 1 else 0 := by
  unfold regressionWeight cardinal
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Lagrange.eval_basis_self (fun a _ b _ h ↦ hinj h) (Finset.mem_univ i)]
    simp [denominator_ne_zero x hx (hx i)]
  · rw [if_neg hij, Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)]
    simp

theorem sum_abs_weights_at_sample (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x) (j : Fin n) (w : Fin n → ℝ) :
    (∑ i, |regressionWeight x i (x j)| * w i) = w j := by
  rw [Finset.sum_eq_single j]
  · rw [regressionWeight_at_sample x hx hinj j j]
    simp
  · intro i hi hij
    rw [regressionWeight_at_sample x hx hinj i j, if_neg hij, abs_zero, zero_mul]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

theorem omittedPotential_nonneg (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    0 ≤ omittedPotential s i t := by
  apply Finset.sum_nonneg
  intro j hj
  by_cases h : t - s j = 0
  · simp [h, logTanhPotential]
  · exact (logTanhPotential_pos (abs_pos.mpr h)).le

theorem sech_le_two_exp_neg (z : ℝ) : 1 / Real.cosh z ≤ 2 * Real.exp (-z) := by
  apply (div_le_iff₀ (Real.cosh_pos z)).mpr
  rw [Real.cosh_eq]
  have he : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
  nlinarith [sq_nonneg (Real.exp (-z))]

theorem abs_regressionWeight_far_le (s : Fin n → ℝ) (hs : Function.Injective s)
    (i : Fin n) (t L A c : ℝ)
    (hrow : omittedPotential s i (s i) ≤ L - s i / 2 + A) (hnode : s i ≤ c) :
    |regressionWeight (fun j ↦ Real.exp (s j)) i (Real.exp t)| ≤
      2 * Real.exp (L - t + c / 2 + A) := by
  rw [regressionWeight_exp_normalized, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hn := omittedPotential_nonneg s i t
  have hp := abs_normalizedWeight_le_potentials s hs i t
  have hpot : Real.exp (omittedPotential s i (s i) - omittedPotential s i t) ≤
      Real.exp (L - s i / 2 + A) := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ Real.exp ((s i - t) / 2) *
        ((1 / Real.cosh ((t - s i) / 2)) * Real.exp (omittedPotential s i (s i) - omittedPotential s i t)) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ ≤ Real.exp ((s i - t) / 2) *
        ((2 * Real.exp (-((t - s i) / 2))) * Real.exp (L - s i / 2 + A)) := by
      gcongr
      · exact sech_le_two_exp_neg _
    _ = 2 * Real.exp (L - t + s i / 2 + A) := by
      rw [show Real.exp ((s i - t) / 2) *
          ((2 * Real.exp (-((t - s i) / 2))) * Real.exp (L - s i / 2 + A)) =
          2 * (Real.exp ((s i - t) / 2) * Real.exp (-((t - s i) / 2)) * Real.exp (L - s i / 2 + A)) by ring,
        ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by gcongr

theorem sum_abs_weights_core_le (s : Fin n → ℝ) (hs : Function.Injective s)
    (t L A B q : ℝ) (hq : 0 ≤ q)
    (hrow : ∀ i, omittedPotential s i (s i) ≤ L - s i / 2 + A)
    (hpoint : ∀ i, L - t / 2 + B ≤ omittedPotential s i t) :
    (∑ i, |regressionWeight (fun j ↦ Real.exp (s j)) i (Real.exp t)| * q) ≤
      (n : ℝ) * q * Real.exp (A - B) := by
  calc
    _ ≤ ∑ _ : Fin n, Real.exp (A - B) * q := Finset.sum_le_sum (fun i _ ↦
      mul_le_mul_of_nonneg_right (abs_regressionWeight_core_le s hs i t L A B (hrow i) (hpoint i)) hq)
    _ = _ := by simp; ring

theorem sum_abs_weights_far_le (s : Fin n → ℝ) (hs : Function.Injective s)
    (t L A c q : ℝ) (hq : 0 ≤ q)
    (hrow : ∀ i, omittedPotential s i (s i) ≤ L - s i / 2 + A) (hnode : ∀ i, s i ≤ c) :
    (∑ i, |regressionWeight (fun j ↦ Real.exp (s j)) i (Real.exp t)| * q) ≤
      2 * (n : ℝ) * q * Real.exp (L - t + c / 2 + A) := by
  calc
    _ ≤ ∑ _ : Fin n, (2 * Real.exp (L - t + c / 2 + A)) * q :=
      Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_right
        (abs_regressionWeight_far_le s hs i t L A c (hrow i) (hnode i)) hq)
    _ = _ := by simp; ring

theorem sum_abs_weights_global_le (s : Fin (n + 1) → ℝ) (hs : Function.Injective s)
    (L G A B q : ℝ) (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ i, omittedPotential s i (s i) ≤ L - s i / 2 + A)
    (hnode : ∀ i, s i ≤ 2 * L + 2 * G)
    (hpoint : ∀ t : ℝ, 0 ≤ t → t ≤ 2 * L + G → (∀ j, t ≠ s j) →
      ∀ i, L - t / 2 + B ≤ omittedPotential s i t)
    {v : ℝ} (hv : 1 ≤ v) :
    (∑ i, |regressionWeight (fun j ↦ Real.exp (s j)) i v| * q) ≤
      2 * (n + 1 : ℝ) * q * Real.exp A := by
  let t := Real.log v
  have hvpos : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have het : Real.exp t = v := Real.exp_log hvpos
  have ht : 0 ≤ t := Real.log_nonneg hv
  have hN : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hEA : 1 ≤ Real.exp A := Real.one_le_exp_iff.mpr hA
  have hbase : q ≤ 2 * (n + 1 : ℝ) * q * Real.exp A := by
    calc
      q = 1 * q * 1 := by ring
      _ ≤ (2 * (n + 1 : ℝ)) * q * Real.exp A := by gcongr; linarith
  rw [← het]
  by_cases hsample : ∃ j, t = s j
  · obtain ⟨j, hj⟩ := hsample
    rw [hj, sum_abs_weights_at_sample _ (fun i ↦ Real.exp_pos _) (Real.exp_injective.comp hs)]
    exact hbase
  · by_cases hcore : t ≤ 2 * L + G
    · have h := sum_abs_weights_core_le s hs t L A B q hq hrow
        (hpoint t ht hcore (fun j hj ↦ hsample ⟨j, hj⟩))
      push_cast at h
      refine h.trans ?_
      calc
        (n + 1 : ℝ) * q * Real.exp (A - B) ≤ (n + 1 : ℝ) * q * Real.exp A := by gcongr; linarith
        _ ≤ 2 * (n + 1 : ℝ) * q * Real.exp A := by
          have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ n + 1) hq) (Real.exp_pos A).le
          nlinarith
    · have h := sum_abs_weights_far_le s hs t L A (2 * L + 2 * G) q hq hrow hnode
      push_cast at h
      refine h.trans ?_
      have ht' : 2 * L + G < t := lt_of_not_ge hcore
      gcongr
      linarith

theorem blaschke_at_sample (x : Fin n → ℝ) (i : Fin n) : blaschke x (x i) = 0 := by
  have he : numerator x (x i) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (x i))
  rw [blaschke, he, zero_div]

theorem abs_blaschke_le_omitted (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    |blaschke (fun j ↦ Real.exp (s j)) (Real.exp t)| ≤
      Real.exp (-omittedPotential s i t) := by
  rw [blaschke_exp, Finset.abs_prod]
  have hp : 0 ≤ ∏ j ∈ Finset.univ.erase i, |Real.tanh ((t - s j) / 2)| :=
    Finset.prod_nonneg (fun _ _ ↦ abs_nonneg _)
  calc
    _ = |Real.tanh ((t - s i) / 2)| *
        ∏ j ∈ Finset.univ.erase i, |Real.tanh ((t - s j) / 2)| :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    _ ≤ ∏ j ∈ Finset.univ.erase i, |Real.tanh ((t - s j) / 2)| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (Real.abs_tanh_lt_one _).le hp
    _ ≤ ∏ j ∈ Finset.univ.erase i, Real.exp (-logTanhPotential |t - s j|) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) (fun _ _ ↦ abs_tanh_le_exp_neg_potential _)
    _ = _ := by rw [← Real.exp_sum]; simp only [omittedPotential, Finset.sum_neg_distrib]

theorem blaschke_core_bound (s : Fin (n + 1) → ℝ) (t L B : ℝ)
    (hpoint : (∀ j, t ≠ s j) → L - t / 2 + B ≤ omittedPotential s 0 t) :
    |blaschke (fun j ↦ Real.exp (s j)) (Real.exp t)| ≤
      Real.exp (-L - B) * Real.sqrt (Real.exp t) := by
  by_cases hsample : ∃ j, t = s j
  · obtain ⟨j, hj⟩ := hsample
    rw [hj, blaschke_at_sample, abs_zero]
    positivity
  · have hp := hpoint (fun j hj ↦ hsample ⟨j, hj⟩)
    calc
      _ ≤ Real.exp (-omittedPotential s 0 t) := abs_blaschke_le_omitted s 0 t
      _ ≤ Real.exp (-L - B + t / 2) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [sqrt_exp_half, Real.exp_add]

end Erdos524.RegressionWeightBounds
