import Erdos524.LogTanhPotential

namespace Erdos524.CauchyKernel
open scoped BigOperators

noncomputable def pairEnergy {n : ℕ} (t : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then logTanhPotential (t j - t i) else 0

theorem log_det_normalized_exp {n : ℕ} (t : Fin n → ℝ) (ht : StrictMono t) :
    Real.log (normalized (fun i => Real.exp (t i))).det =
      -(n : ℝ) * Real.log 2 - 2 * pairEnergy t := by
  have hne (i j : Fin n) :
      (if i < j then Real.tanh ((t j-t i)/2)^2 else 1) ≠ 0 := by
    split_ifs with hij
    · have he : Real.exp (t j) - Real.exp (t i) ≠ 0 :=
        sub_ne_zero.mpr (ne_of_gt (Real.exp_lt_exp.mpr (ht hij)))
      rw [← cauchy_ratio_exp]
      exact pow_ne_zero _ (div_ne_zero he (ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))))
    · norm_num
  rw [det_normalized_fin _ (fun i => Real.exp_pos (t i))]
  simp_rw [cauchy_ratio_exp]
  rw [Real.log_mul (pow_ne_zero _ (by norm_num))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j _ => hne i j)))]
  rw [Real.log_pow, Real.log_div (by norm_num) (by norm_num), Real.log_one]
  rw [Real.log_prod (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j _ => hne i j))]
  simp_rw [Real.log_prod (fun j _ => hne _ j)]
  have he (i j : Fin n) :
      Real.log (if i < j then Real.tanh ((t j-t i)/2)^2 else 1) =
        -2 * (if i < j then logTanhPotential (t j-t i) else 0) := by
    split_ifs <;> simp [Real.log_pow, logTanhPotential]
  simp_rw [he, ← Finset.mul_sum]
  unfold pairEnergy
  ring


theorem pairEnergy_affine_mesh_le {m : ℕ} (a : ℝ) {r : ℝ} (hr : 0 < r) :
    pairEnergy (fun i : Fin m => a + (i : ℝ)/r) ≤ (m : ℝ) * r * (Real.pi^2/4) := by
  have hp (i j : Fin m) :
      (if i < j then logTanhPotential ((a+(j:ℝ)/r)-(a+(i:ℝ)/r)) else 0) =
      (if i.val < j.val then logTanhPotential ((j.val-i.val : ℕ)/r) else 0) := by
    change (if i.val < j.val then _ else _) = _
    split_ifs with h
    · congr 1
      rw [Nat.cast_sub (Nat.le_of_lt h)]
      ring
    · rfl
  unfold pairEnergy
  simp only [hp]
  have hfin (i : Fin m) : (∑ j : Fin m, if i.val < j.val then
      logTanhPotential ((j.val-i.val : ℕ)/r) else 0) =
      ∑ j ∈ Finset.range m, if i.val < j then logTanhPotential ((j-i.val : ℕ)/r) else 0 :=
    Fin.sum_univ_eq_sum_range (fun j => if i.val < j then logTanhPotential ((j-i.val : ℕ)/r) else 0) m
  simp_rw [hfin]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range m,
    if i < j then logTanhPotential ((j-i : ℕ)/r) else 0) m]
  have hrow (i : ℕ) : (∑ j ∈ Finset.range m,
      if i < j then logTanhPotential ((j-i : ℕ)/r) else 0) =
      ∑ j ∈ Finset.Ico (i+1) m, logTanhPotential ((j-i : ℕ)/r) := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  simp_rw [hrow]
  exact block_pair_energy_le hr m

theorem log_det_affine_mesh_lower {m : ℕ} (a : ℝ) {r : ℝ} (hr : 0 < r) :
    -(m : ℝ)*Real.log 2 - (m : ℝ)*r*(Real.pi^2/2) ≤
      Real.log (normalized (fun i : Fin m => Real.exp (a+(i:ℝ)/r))).det := by
  have ht : StrictMono (fun i : Fin m => a+(i:ℝ)/r) := by
    intro i j hij
    have hcast : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    simpa only [add_comm] using add_lt_add_left ((div_lt_div_iff_of_pos_right hr).mpr hcast) a
  rw [log_det_normalized_exp _ ht]
  have he := pairEnergy_affine_mesh_le (m := m) a hr
  linarith


theorem cross_pair_energy_le {m n : ℕ} (s : Fin m → ℝ) (t : Fin n → ℝ)
    {gap : ℝ} (hgap : Real.log 2 ≤ gap) (hsep : ∀ i j, gap ≤ t j - s i) :
    (∑ i, ∑ j, logTanhPotential (t j - s i)) ≤
      (m : ℝ) * (n : ℝ) * (4 * Real.exp (-gap)) := by
  have hgpos : 0 < gap := lt_of_lt_of_le (Real.log_pos (by norm_num)) hgap
  calc
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin n, 4 * Real.exp (-gap) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact (logTanhPotential_antitone hgpos (lt_of_lt_of_le hgpos (hsep i j))
        (hsep i j)).trans (logTanhPotential_tail hgap)
    _ = _ := by simp; ring

end Erdos524.CauchyKernel
