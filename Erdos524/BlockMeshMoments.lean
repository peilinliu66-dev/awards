import Erdos524.BlockMesh

namespace Erdos524.CauchyKernel
open scoped BigOperators

noncomputable def cellDeficit (L : ℝ) {K : ℕ} (j : Fin K) : ℝ :=
  L * (1 - (2*(j : ℝ)+1)/(2*K))

theorem sum_range_natCast_sq_six (m : ℕ) :
    6 * (∑ i ∈ Finset.range m, (i : ℝ)^2) =
      (m : ℝ)*((m : ℝ)-1)*(2*(m : ℝ)-1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith

theorem sum_cellDeficit {K : ℕ} (hK : 0 < K) (L : ℝ) :
    (∑ j : Fin K, cellDeficit L j) = (K : ℝ)*L/2 := by
  have hk : (K : ℝ) ≠ 0 := by positivity
  have hsum : (∑ j : Fin K, (j : ℝ)) = (K : ℝ)*((K : ℝ)-1)/2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℝ)) K]
    have h := sum_range_natCast_twice K
    linarith
  unfold cellDeficit
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  <;> ring

theorem sum_cellDeficit_sq {K : ℕ} (hK : 0 < K) (L : ℝ) :
    (∑ j : Fin K, (cellDeficit L j)^2) =
      L^2 * ((K : ℝ)/3 - 1/(12*K)) := by
  have hk : (K : ℝ) ≠ 0 := by positivity
  have hsum : (∑ j : Fin K, (j : ℝ)) = (K : ℝ)*((K : ℝ)-1)/2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℝ)) K]
    have h := sum_range_natCast_twice K
    linarith
  have hsq : (∑ j : Fin K, (j : ℝ)^2) =
      (K : ℝ)*((K : ℝ)-1)*(2*(K : ℝ)-1)/6 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℝ)^2) K]
    have h := sum_range_natCast_sq_six K
    linarith
  have he (j : Fin K) : (cellDeficit L j)^2 =
      L^2 * (1 - (2*(j:ℝ)+1)/K + (4*(j:ℝ)^2+4*(j:ℝ)+1)/(4*(K:ℝ)^2)) := by
    unfold cellDeficit
    field_simp
    <;> ring
  simp_rw [he]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_div, hsum, hsq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  <;> ring


theorem cellDeficit_pos {K : ℕ} (hK : 0 < K) {L : ℝ} (hL : 0 < L) (j : Fin K) :
    0 < cellDeficit L j := by
  have hj : (j : ℝ)+1 ≤ K := by exact_mod_cast j.isLt
  have hk : (0 : ℝ) < K := by positivity
  unfold cellDeficit
  apply mul_pos hL
  apply sub_pos.mpr
  apply (div_lt_one (by positivity : (0 : ℝ)<2*K)).mpr
  linarith

theorem blockCount_loss_le {d : ℝ} (hd : 0 ≤ d) (width : ℝ) :
    -(blockCount (2*d/Real.pi^2) width : ℝ)*d/2 ≤ -width*d^2/Real.pi^2+d/2 := by
  have h := (blockCount_lower (2*d/Real.pi^2) width).le
  have hm := mul_le_mul_of_nonneg_right h hd
  ring_nf at hm ⊢
  linarith

theorem block_count_objective_le {K : ℕ} (hK : 0 < K) {L : ℝ} (hL : 0 < L)
    (width : ℝ) :
    (∑ j : Fin K, -(blockCount (2*cellDeficit L j/Real.pi^2) width : ℝ)*cellDeficit L j/2) ≤
      -width/Real.pi^2 * (L^2*((K : ℝ)/3-1/(12*K))) + (K : ℝ)*L/4 := by
  calc
    _ ≤ ∑ j : Fin K, (-width*(cellDeficit L j)^2/Real.pi^2+cellDeficit L j/2) :=
      Finset.sum_le_sum (fun j _ => blockCount_loss_le (cellDeficit_pos hK hL j).le width)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,
        sum_cellDeficit_sq hK L, sum_cellDeficit hK L]
      ring

theorem block_leading_coefficient {K : ℕ} (hK : 0 < K) (L : ℝ) :
    ((2*L/K-8*Real.log L)/Real.pi^2) * (L^2*((K : ℝ)/3-1/(12*K))) =
      (2/(3*Real.pi^2))*(1-1/(4*(K : ℝ)^2))*L^3 -
      (8/Real.pi^2)*((K : ℝ)/3-1/(12*K))*L^2*Real.log L := by
  have hk : (K : ℝ) ≠ 0 := by positivity
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  <;> ring

end Erdos524.CauchyKernel
