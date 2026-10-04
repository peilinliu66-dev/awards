import Erdos524.LogCauchyInverse

namespace Erdos524.CauchyKernel
open scoped BigOperators

theorem model_row_energy_le (n i : ℕ) (hi : i ≤ n) {r : ℝ} (hr : 0 < r) :
    (∑ k ∈ Finset.range n, if k < i then logTanhPotential ((i-k : ℕ)/r)
      else logTanhPotential ((k+1-i : ℕ)/r)) ≤ r*(Real.pi^2/2) := by
  let f : ℕ → ℝ := fun k => if k < i then logTanhPotential ((i-k : ℕ)/r)
      else logTanhPotential ((k+1-i : ℕ)/r)
  change (∑ k ∈ Finset.range n, f k) ≤ _
  rw [← Finset.sum_range_add_sum_Ico f hi]
  have hleft : (∑ k ∈ Finset.range i, f k) =
      ∑ k ∈ Finset.range i, logTanhPotential ((k+1 : ℕ)/r) := by
    calc
      _ = ∑ k ∈ Finset.range i, logTanhPotential (((i-1-k)+1 : ℕ)/r) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hki : k < i := Finset.mem_range.mp hk
        simp only [f, if_pos hki]
        have he : i-k = (i-1-k)+1 := by omega
        rw [he]
      _ = _ := Finset.sum_range_reflect (fun k => logTanhPotential ((k+1 : ℕ)/r)) i
  have hright : (∑ k ∈ Finset.Ico i n, f k) =
      ∑ k ∈ Finset.range (n-i), logTanhPotential ((k+1 : ℕ)/r) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    have hki : ¬i+k < i := by omega
    simp only [f, if_neg hki]
    have he : i+k+1-i = k+1 := by omega
    rw [he]
  rw [hleft, hright]
  have h1 := sum_logTanhPotential_mesh_le hr i
  have h2 := sum_logTanhPotential_mesh_le hr (n-i)
  linarith


theorem separated_grid_strictMono {m : ℕ} (t : Fin m → ℝ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j : Fin m, i < j → ((j:ℝ)-(i:ℝ))/r ≤ t j-t i) : StrictMono t := by
  intro i j hij
  have hc : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  have hp := div_pos (sub_pos.mpr hc) hr
  have h := hsep i j hij
  linarith

theorem separated_row_energy_le {n : ℕ} (t : Fin (n+1) → ℝ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j : Fin (n+1), i < j → ((j:ℝ)-(i:ℝ))/r ≤ t j-t i) (i : Fin (n+1)) :
    (∑ k : Fin n, logTanhPotential |t (i.succAbove k)-t i|) ≤ r*(Real.pi^2/2) := by
  have hterm (k : Fin n) : logTanhPotential |t (i.succAbove k)-t i| ≤
      if k.val < i.val then logTanhPotential ((i.val-k.val : ℕ)/r)
      else logTanhPotential ((k.val+1-i.val : ℕ)/r) := by
    by_cases hk : k.val < i.val
    · rw [if_pos hk, Fin.succAbove_of_castSucc_lt i k hk]
      have hs := hsep k.castSucc i hk
      have hd : 0 < ((i.val-k.val : ℕ) : ℝ)/r := by
        apply div_pos _ hr
        exact_mod_cast Nat.sub_pos_of_lt hk
      have he : ((i.val-k.val : ℕ) : ℝ)/r = ((i:ℝ)-(k.castSucc:ℝ))/r := by
        rw [Nat.cast_sub (Nat.le_of_lt hk)]
        rfl
      rw [← he] at hs
      have hdiff : t k.castSucc-t i < 0 := by linarith
      rw [abs_of_neg hdiff]
      have hp : 0 < -(t k.castSucc-t i) := neg_pos.mpr hdiff
      exact logTanhPotential_antitone hd hp (by linarith)
    · rw [if_neg hk, Fin.succAbove_of_le_castSucc i k (Nat.le_of_not_gt hk)]
      have hlt : i < k.succ := by change i.val < k.val+1; omega
      have hs := hsep i k.succ hlt
      have hd : 0 < ((k.val+1-i.val : ℕ) : ℝ)/r := by
        apply div_pos _ hr
        exact_mod_cast Nat.sub_pos_of_lt hlt
      have he : ((k.val+1-i.val : ℕ) : ℝ)/r = ((k.succ:ℝ)-(i:ℝ))/r := by
        rw [Nat.cast_sub (by omega : i.val ≤ k.val+1)]
        rfl
      rw [← he] at hs
      have hdiff : 0 < t k.succ-t i := by linarith
      rw [abs_of_pos hdiff]
      exact logTanhPotential_antitone hd hdiff hs
  calc
    _ ≤ ∑ k : Fin n, if k.val < i.val then logTanhPotential ((i.val-k.val : ℕ)/r)
        else logTanhPotential ((k.val+1-i.val : ℕ)/r) :=
      Finset.sum_le_sum (fun k _ => hterm k)
    _ ≤ _ := by
      rw [Fin.sum_univ_eq_sum_range (fun k => if k < i.val then logTanhPotential ((i.val-k : ℕ)/r)
        else logTanhPotential ((k+1-i.val : ℕ)/r)) n]
      exact model_row_energy_le n i.val (by omega) hr

theorem separated_inverse_diagonal_le {n : ℕ} (t : Fin (n+1) → ℝ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j : Fin (n+1), i < j → ((j:ℝ)-(i:ℝ))/r ≤ t j-t i) (i : Fin (n+1)) :
    (normalized (fun j => Real.exp (t j)))⁻¹ i i ≤ 2*Real.exp (r*Real.pi^2) := by
  rw [inverse_diagonal_exp_eq t (separated_grid_strictMono t hr hsep).injective i]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have h := separated_row_energy_le t hr hsep i
  linarith

theorem separated_inverse_trace_le {n : ℕ} (t : Fin (n+1) → ℝ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j : Fin (n+1), i < j → ((j:ℝ)-(i:ℝ))/r ≤ t j-t i) :
    Matrix.trace ((normalized (fun j => Real.exp (t j)))⁻¹) ≤
      (n+1 : ℝ)*2*Real.exp (r*Real.pi^2) := by
  unfold Matrix.trace
  calc
    _ ≤ ∑ _i : Fin (n+1), 2*Real.exp (r*Real.pi^2) :=
      Finset.sum_le_sum (fun i _ => separated_inverse_diagonal_le t hr hsep i)
    _ = _ := by simp; ring

end Erdos524.CauchyKernel
