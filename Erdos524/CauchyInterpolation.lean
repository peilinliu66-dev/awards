import Erdos524.CauchyKernel
import Mathlib.LinearAlgebra.Lagrange

namespace Erdos524.CauchyKernel
open scoped BigOperators
open Polynomial

variable {n : ℕ}
noncomputable def denominator (x : Fin n → ℝ) (v : ℝ) : ℝ := ∏ k, (v + x k)
noncomputable def cardinal (x : Fin n → ℝ) (j : Fin n) (v : ℝ) : ℝ :=
  (Lagrange.basis Finset.univ x j).eval v
noncomputable def regressionWeight (x : Fin n → ℝ) (j : Fin n) (v : ℝ) : ℝ :=
  cardinal x j v * denominator x (x j) / denominator x v

theorem denominator_ne_zero (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    {v : ℝ} (hv : 0 < v) : denominator x v ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (add_pos hv (hx i)))

theorem erased_denominator (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (i : Fin n) {v : ℝ} (hv : 0 < v) :
    (Lagrange.nodal (Finset.univ.erase i) (fun k => -x k)).eval v =
      denominator x v / (v + x i) := by
  rw [Lagrange.eval_nodal]
  simp only [sub_neg_eq_add]
  apply (eq_div_iff (ne_of_gt (add_pos hv (hx i)))).mpr
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)

theorem normal_equations (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x) (i : Fin n) {v : ℝ} (hv : 0 < v) :
    ∑ j, regressionWeight x j v / (x i + x j) = 1 / (v + x i) := by
  let q := Lagrange.nodal (Finset.univ.erase i) (fun k => -x k)
  have hdeg : q.degree < (Finset.univ : Finset (Fin n)).card := by
    rw [Lagrange.degree_nodal]
    exact_mod_cast Finset.card_erase_lt_of_mem (Finset.mem_univ i)
  have hid := Lagrange.eq_interpolate (f := q) (s := Finset.univ)
    (v := x) (fun a _ b _ h => hinj h) hdeg
  have heval := congrArg (fun p : ℝ[X] => p.eval v) hid
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C] at heval
  have he : denominator x v / (v + x i) =
      ∑ j, (denominator x (x j) / (x j + x i)) * cardinal x j v := by
    simpa only [q, erased_denominator x hx i hv,
      erased_denominator x hx i (hx _), cardinal] using heval
  have hd := denominator_ne_zero x hx hv
  calc
    ∑ j, regressionWeight x j v / (x i + x j) =
        (∑ j, (denominator x (x j) / (x j + x i)) * cardinal x j v) /
          denominator x v := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      unfold regressionWeight
      rw [add_comm (x i) (x j)]
      ring
    _ = (denominator x v / (v + x i)) / denominator x v := by rw [← he]
    _ = 1 / (v + x i) := by field_simp

theorem cardinal_product (x : Fin n → ℝ) (j : Fin n) (v : ℝ) :
    cardinal x j v = ∏ k ∈ Finset.univ.erase j, (v - x k) / (x j - x k) := by
  simp only [cardinal, Lagrange.basis, eval_prod, Lagrange.basisDivisor,
    eval_mul, eval_C, eval_sub, eval_X]
  apply Finset.prod_congr rfl
  intro k _
  ring

theorem regressionWeight_product (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (j : Fin n) {v : ℝ} (hv : 0 < v) :
    regressionWeight x j v = (2 * x j / (v + x j)) *
      ∏ k ∈ Finset.univ.erase j,
        ((v - x k) / (v + x k) * ((x j + x k) / (x j - x k))) := by
  have hD (z : ℝ) : denominator x z =
      (z + x j) * ∏ k ∈ Finset.univ.erase j, (z + x k) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
  rw [regressionWeight, cardinal_product, hD, hD]
  simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib, div_mul_eq_div_mul_one_div]
  ring


theorem interpolate_eval (x : Fin n → ℝ) (hinj : Function.Injective x)
    (p : ℝ[X]) (hp : p.degree < n) (v : ℝ) :
    p.eval v = ∑ j, p.eval (x j) * cardinal x j v := by
  have hid := Lagrange.eq_interpolate (f := p) (s := Finset.univ)
    (v := x) (fun a _ b _ h => hinj h) (by simpa using hp)
  have he := congrArg (fun p : ℝ[X] => p.eval v) hid
  simpa only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C,
    cardinal] using he

theorem quotient_eval (p : ℝ[X]) (u t : ℝ) :
    p.eval (-u) + (t + u) * (p /ₘ (X - C (-u))).eval t = p.eval t := by
  have h := congrArg (fun p : ℝ[X] => p.eval t)
    (modByMonic_add_div p (X - C (-u)))
  simpa only [modByMonic_X_sub_C_eq_C_eval, eval_add, eval_C, eval_mul,
    eval_sub, eval_X, sub_neg_eq_add] using h

theorem quotient_interpolate (x : Fin n → ℝ) (hinj : Function.Injective x)
    (p : ℝ[X]) (hp : p ≠ 0) (hdeg : p.degree ≤ n) (u v : ℝ) :
    (p /ₘ (X - C (-u))).eval v =
      ∑ j, (p /ₘ (X - C (-u))).eval (x j) * cardinal x j v := by
  apply interpolate_eval x hinj
  exact lt_of_lt_of_le (degree_divByMonic_lt _ _ hp (by rw [degree_X_sub_C]; norm_num)) hdeg


theorem rational_error_factor (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x) (p : ℝ[X]) (hp : p ≠ 0)
    (hdeg : p.degree ≤ n) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    p.eval v / (v + u) - ∑ j, p.eval (x j) / (x j + u) * cardinal x j v =
      p.eval (-u) * (1 / (v + u) - ∑ j, cardinal x j v / (x j + u)) := by
  have heval (t : ℝ) (ht : 0 < t) :
      (p /ₘ (X - C (-u))).eval t =
        p.eval t / (t + u) - p.eval (-u) / (t + u) := by
    have he := quotient_eval p u t
    have htu : t + u ≠ 0 := ne_of_gt (add_pos ht hu)
    rw [← sub_div, eq_div_iff htu]
    nlinarith [he]
  have he := quotient_interpolate x hinj p hp hdeg u v
  rw [heval v hv] at he
  simp_rw [heval _ (hx _), sub_mul, Finset.sum_sub_distrib] at he
  have hs : (∑ j, p.eval (-u) / (x j + u) * cardinal x j v) =
      p.eval (-u) * ∑ j, cardinal x j v / (x j + u) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs] at he
  rw [mul_sub, mul_one_div]
  linarith


noncomputable def numerator (x : Fin n → ℝ) (v : ℝ) : ℝ := ∏ k, (v - x k)
noncomputable def blaschke (x : Fin n → ℝ) (v : ℝ) : ℝ :=
  numerator x v / denominator x v

theorem nodal_negative_ne_zero (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    {u : ℝ} (hu : 0 < u) :
    (Lagrange.nodal Finset.univ x).eval (-u) ≠ 0 := by
  rw [Lagrange.eval_nodal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have := hx i
  linarith

theorem rational_defect (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    1 / (v + u) - ∑ j, cardinal x j v / (x j + u) =
      numerator x v / ((v + u) * (Lagrange.nodal Finset.univ x).eval (-u)) := by
  have he := rational_error_factor x hx hinj (Lagrange.nodal Finset.univ x)
    Lagrange.nodal_ne_zero (by simp [Lagrange.degree_nodal]) hu hv
  have hnodes (j : Fin n) : (Lagrange.nodal Finset.univ x).eval (x j) = 0 :=
    Lagrange.eval_nodal_at_node (Finset.mem_univ j)
  simp only [hnodes, zero_div, zero_mul, Finset.sum_const_zero, sub_zero] at he
  have hn := nodal_negative_ne_zero x hx hu
  have huv : v + u ≠ 0 := ne_of_gt (add_pos hv hu)
  rw [Lagrange.eval_nodal] at he
  change numerator x v / (v + u) = _ at he
  apply (eq_div_iff (mul_ne_zero huv hn)).mpr
  field_simp at he ⊢
  nlinarith [he]


theorem negative_nodal_ratio (x : Fin n → ℝ) (u : ℝ) :
    (Lagrange.nodal Finset.univ (fun k => -x k)).eval (-u) /
      (Lagrange.nodal Finset.univ x).eval (-u) = blaschke x u := by
  simp only [Lagrange.eval_nodal, blaschke, numerator, denominator,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro k _
  have ha : -u - -x k = -(u - x k) := by ring
  have hb : -u - x k = -(u + x k) := by ring
  rw [ha, hb, neg_div_neg_eq]

theorem residual_kernel (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    1 / (u + v) - ∑ j, regressionWeight x j v / (u + x j) =
      blaschke x u * blaschke x v / (u + v) := by
  let p := Lagrange.nodal Finset.univ (fun k => -x k)
  have he := rational_error_factor x hx hinj p Lagrange.nodal_ne_zero
    (by simp [p, Lagrange.degree_nodal]) hu hv
  rw [rational_defect x hx hinj hu hv] at he
  have hp (t : ℝ) : p.eval t = denominator x t := by
    simp only [p, Lagrange.eval_nodal, sub_neg_eq_add, denominator]
  rw [hp v] at he
  simp_rw [hp] at he
  have hneg : denominator x (-u) /
      (Lagrange.nodal Finset.univ x).eval (-u) = blaschke x u := by
    exact (hp (-u)).symm ▸ negative_nodal_ratio x u
  have hd := denominator_ne_zero x hx hv
  have hs : (∑ j, regressionWeight x j v / (u + x j)) =
      (∑ j, denominator x (x j) / (x j + u) * cardinal x j v) /
        denominator x v := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    unfold regressionWeight
    rw [add_comm u (x j)]
    ring
  rw [hs]
  have hright : denominator x (-u) *
      (numerator x v / ((v + u) * (Lagrange.nodal Finset.univ x).eval (-u))) =
      blaschke x u * numerator x v / (v + u) := by
    rw [← hneg, div_mul_eq_div_mul_one_div]
    ring
  rw [hright] at he
  rw [add_comm u v]
  change _ = blaschke x u * (numerator x v / denominator x v) / (v + u)
  apply (mul_right_inj' hd).mp
  field_simp at he ⊢
  nlinarith [he]


noncomputable def normalizedWeight (x : Fin n → ℝ) (j : Fin n) (v : ℝ) : ℝ :=
  Real.sqrt v / Real.sqrt (x j) * regressionWeight x j v

noncomputable def normalizedKernel (u v : ℝ) : ℝ :=
  Real.sqrt u * (1 / (u + v)) * Real.sqrt v

theorem normalized_normal_equations (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x) (i : Fin n) {v : ℝ} (hv : 0 < v) :
    ∑ j, normalizedWeight x j v * normalizedKernel (x i) (x j) =
      normalizedKernel (x i) v := by
  have hterm (j : Fin n) : normalizedWeight x j v * normalizedKernel (x i) (x j) =
      (Real.sqrt (x i) * Real.sqrt v) * (regressionWeight x j v / (x i + x j)) := by
    have hs : Real.sqrt (x j) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hx j))
    unfold normalizedWeight normalizedKernel
    field_simp
  simp_rw [hterm]
  rw [← Finset.mul_sum, normal_equations x hx hinj i hv]
  unfold normalizedKernel
  rw [add_comm v (x i)]
  ring

theorem normalized_residual_kernel (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    normalizedKernel u v - ∑ j, normalizedWeight x j v * normalizedKernel u (x j) =
      blaschke x u * blaschke x v * normalizedKernel u v := by
  have hterm (j : Fin n) : normalizedWeight x j v * normalizedKernel u (x j) =
      (Real.sqrt u * Real.sqrt v) * (regressionWeight x j v / (u + x j)) := by
    have hs : Real.sqrt (x j) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hx j))
    unfold normalizedWeight normalizedKernel
    field_simp
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have he := residual_kernel x hx hinj hu hv
  unfold normalizedKernel
  calc
    _ = (Real.sqrt u * Real.sqrt v) *
      (1 / (u + v) - ∑ j, regressionWeight x j v / (u + x j)) := by ring
    _ = _ := by rw [he]; ring

end Erdos524.CauchyKernel
