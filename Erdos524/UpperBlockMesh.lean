import Erdos524.BlockPointSet

namespace Erdos524.CauchyKernel
open scoped BigOperators

noncomputable def upperCenter (L : ℝ) {K : ℕ} (j : Fin K) : ℝ := (2*(j:ℝ)+1)*L/K
noncomputable def upperDensity (L : ℝ) {K : ℕ} (j : Fin K) : ℝ := 2*cellDeficit L j/Real.pi^2
noncomputable def upperWidth (L G : ℝ) (K : ℕ) : ℝ := 2*L/K-2*G
noncomputable def upperCount (L G : ℝ) {K : ℕ} (j : Fin K) : ℕ :=
  blockCount (upperDensity L j) (upperWidth L G K)
noncomputable def upperPointSet (L G : ℝ) (K : ℕ) : Finset ℝ :=
  blockPointSet (upperCenter L) (upperDensity L) (upperCount L G : Fin K → ℕ)

theorem upperDensity_pos {K : ℕ} (hK : 0<K) {L : ℝ} (hL : 0<L) (j : Fin K) :
    0 < upperDensity L j := by
  unfold upperDensity
  exact div_pos (mul_pos (by norm_num) (cellDeficit_pos hK hL j)) (sq_pos_of_pos Real.pi_pos)

theorem upperDensity_le {K : ℕ} (hK : 0<K) {L : ℝ} (hL : 0<L) (j : Fin K) :
    upperDensity L j ≤ 2*L/Real.pi^2 := by
  unfold upperDensity cellDeficit
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos Real.pi_pos)).mpr
  have h : 0 ≤ (2*(j:ℝ)+1)/(2*K) := by positivity
  nlinarith

theorem upperCount_le {K : ℕ} (hK : 0<K) {L G : ℝ} (hL : 0<L)
    (hw : 0 ≤ upperWidth L G K) (j : Fin K) :
    (upperCount L G j : ℝ) ≤ upperDensity L j * upperWidth L G K :=
  blockCount_le (upperDensity_pos hK hL j).le hw

theorem upperCenter_separation {K : ℕ} (hK : 0<K) {L G : ℝ} (hL : 0<L)
    (j k : Fin K) (hjk : j<k) :
    upperWidth L G K + 2*G ≤ upperCenter L k-upperCenter L j := by
  have hc : (j:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast hjk
  have hk : (0 : ℝ)<K := by positivity
  unfold upperWidth upperCenter
  rw [sub_add_cancel, ← sub_div]
  apply (div_le_div_iff_of_pos_right hk).mpr
  nlinarith

theorem upperPointSet_separated {K : ℕ} (hK : 0<K) {L G : ℝ} (hL : 0<L)
    (hw : 0 ≤ upperWidth L G K) (hg : 1/(2*L/Real.pi^2) ≤ 2*G) :
    ∀ x ∈ upperPointSet L G K, ∀ y ∈ upperPointSet L G K,
      x<y → 1/(2*L/Real.pi^2) ≤ y-x := by
  apply blockPointSet_separated _ _ _ (fun j => upperDensity_pos hK hL j)
    (by positivity) (fun j => upperDensity_le hK hL j)
    (fun j => upperCount_le hK hL hw j)
    (fun j k h => upperCenter_separation hK hL j k h) hg


theorem sum_upperDensity {K : ℕ} (hK : 0<K) (L : ℝ) :
    (∑ j : Fin K, upperDensity L j) = (K : ℝ)*L/Real.pi^2 := by
  unfold upperDensity
  rw [← Finset.sum_div, ← Finset.mul_sum, sum_cellDeficit hK L]
  ring

theorem upperPointSet_card_bound {K : ℕ} (hK : 0<K) {L G : ℝ}
    (hL : 0<L) (hG : 0≤G) (hw : 0≤upperWidth L G K) :
    ((upperPointSet L G K).card : ℝ) ≤ 2*L^2/Real.pi^2 := by
  have hk : (K : ℝ) ≠ 0 := by positivity
  have hc : ((upperPointSet L G K).card : ℝ) ≤ ∑ j : Fin K, (upperCount L G j : ℝ) := by
    exact_mod_cast blockPointSet_card_le (upperCenter L) (upperDensity L) (upperCount L G : Fin K → ℕ)
  calc
    _ ≤ ∑ j : Fin K, (upperCount L G j : ℝ) := hc
    _ ≤ ∑ j : Fin K, upperDensity L j*upperWidth L G K :=
      Finset.sum_le_sum (fun j _ => upperCount_le hK hL hw j)
    _ = ((K : ℝ)*L/Real.pi^2)*upperWidth L G K := by
      rw [← Finset.sum_mul, sum_upperDensity hK L]
    _ ≤ ((K : ℝ)*L/Real.pi^2)*(2*L/K) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold upperWidth
      linarith
    _ = _ := by field_simp

theorem upperPointSet_min {K : ℕ} (hK : 0<K) {L G : ℝ}
    (hL : 0<L) (hw : 0≤upperWidth L G K) {x : ℝ} (hx : x ∈ upperPointSet L G K) : G ≤ x := by
  classical
  obtain ⟨⟨j,a⟩, _, rfl⟩ := Finset.mem_image.mp hx
  have h := (abs_le.mp (blockPoint_within (upperCenter L j) (upperDensity_pos hK hL j)
    (upperCount_le hK hL hw j) a)).1
  have he : upperCenter L j-upperWidth L G K/2 = G+2*(j:ℝ)*L/K := by
    unfold upperCenter upperWidth
    ring
  have hn : 0 ≤ 2*(j:ℝ)*L/K := by positivity
  linarith

theorem upperPointSet_trace_bound {K n : ℕ} (hK : 0<K) {L G : ℝ}
    (hL : 0<L) (hw : 0≤upperWidth L G K) (hg : 1/(2*L/Real.pi^2)≤2*G)
    (hn : (upperPointSet L G K).card = n+1) :
    Matrix.trace ((normalized (fun j : Fin (n+1) => Real.exp ((upperPointSet L G K).orderEmbOfFin hn j)))⁻¹) ≤
      (n+1 : ℝ)*2*Real.exp (2*L) := by
  have he := ordered_set_inverse_trace_le (upperPointSet L G K) hn
    (by positivity : 0<2*L/Real.pi^2) (upperPointSet_separated hK hL hw hg)
  have hp : Real.pi^2 ≠ 0 := ne_of_gt (sq_pos_of_pos Real.pi_pos)
  simpa only [div_mul_cancel₀ _ hp] using he

end Erdos524.CauchyKernel
