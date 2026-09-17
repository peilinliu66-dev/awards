import Mathlib

/-! Elementary arithmetic for the explicit long-cycle threshold f(k) = 5*k+5. -/
namespace JSP842

theorem closed_bound_le_threshold (m k t : ℕ)
    (hm : 4 * k + 5 ≤ m) (ht : 1 ≤ t) (htm : 2 * t ≤ m - 1) :
    (m - t).choose 2 + t * t + k * t + (k + 1).choose 2 ≤
      (m - 1).choose 2 + (k + 2).choose 2 := by
  have hm1 : 1 ≤ m := by omega
  have htm' : t ≤ m := by omega
  have hmR : (4 : ℚ) * k + 5 ≤ m := by exact_mod_cast hm
  have htR : (1 : ℚ) ≤ t := by exact_mod_cast ht
  have htmR : (2 : ℚ) * t ≤ (m : ℚ) - 1 := by
    have h : (2 : ℚ) * t + 1 ≤ m := by
      exact_mod_cast (show 2 * t + 1 ≤ m by omega)
    linarith
  have hneg : (3 : ℚ) * t + 2 * k + 4 - 2 * m ≤ 0 := by linarith
  have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr htR) hneg
  have hreal : (((m - t).choose 2 + t * t + k * t + (k + 1).choose 2 : ℕ) : ℚ) ≤
      (((m - 1).choose 2 + (k + 2).choose 2 : ℕ) : ℚ) := by
    push_cast
    simp only [Nat.cast_choose_two, Nat.cast_sub htm', Nat.cast_sub hm1,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    nlinarith
  exact_mod_cast hreal

theorem isolated_bound_le_threshold (m k : ℕ) :
    (m - 1).choose 2 + (k + 1).choose 2 ≤
      (m - 1).choose 2 + (k + 2).choose 2 := by
  exact Nat.add_le_add_left (Nat.choose_le_choose 2 (by omega)) _

theorem remaining_vertices_large (n k : ℕ) (hn : 5 * k + 5 ≤ n) :
    k ≤ n ∧ 4 * k + 5 ≤ n - k := by omega

#print axioms closed_bound_le_threshold
#print axioms isolated_bound_le_threshold
end JSP842
