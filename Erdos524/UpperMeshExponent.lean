import Erdos524.SetMeshEnergy

namespace Erdos524.CauchyKernel
open scoped BigOperators

theorem upperCenter_deficit {K : ℕ} (L : ℝ) (j : Fin K) :
    L-upperCenter L j/2 = cellDeficit L j := by
  unfold upperCenter cellDeficit
  ring

theorem upperPointSet_card_eq {K : ℕ} (hK : 0<K) {L G : ℝ}
    (hL : 0<L) (hG : 0<G) (hw : 0≤upperWidth L G K) :
    (upperPointSet L G K).card = ∑ j : Fin K, upperCount L G j :=
  blockPointSet_card_eq _ _ _ (fun j => upperDensity_pos hK hL j)
    (fun j => upperCount_le hK hL hw j)
    (fun j k h => upperCenter_separation hK hL j k h) (by linarith)

theorem upperPointSet_deficit_sum {K : ℕ} (hK : 0<K) {L G : ℝ}
    (hL : 0<L) (hG : 0<G) (hw : 0≤upperWidth L G K) :
    (∑ x ∈ upperPointSet L G K, (L-x/2)) =
      ∑ j : Fin K, (upperCount L G j : ℝ)*cellDeficit L j := by
  have he := blockPointSet_deficit_sum (upperCenter L) (upperDensity L) (upperCount L G : Fin K → ℕ)
    (fun j => upperDensity_pos hK hL j) (fun j => upperCount_le hK hL hw j)
    (fun j k h => upperCenter_separation hK hL j k h) (by linarith : 0<2*G) L
  simpa only [upperCenter_deficit, upperPointSet] using he

theorem upperPointSet_rowEnergy_bound {K : ℕ} (hK : 0<K) {L G : ℝ}
    (hL : 0<L) (hg : Real.log 2 ≤ 2*G) (hw : 0≤upperWidth L G K) :
    setRowEnergy (upperPointSet L G K) ≤
      (∑ j : Fin K, (upperCount L G j : ℝ)*cellDeficit L j) +
      ((upperPointSet L G K).card : ℝ)^2*(4*Real.exp (-2*G)) := by
  have hG : 0<G := by have := Real.log_pos (by norm_num : (1:ℝ)<2); linarith
  have he := blockPointSet_rowEnergy_le (upperCenter L) (upperDensity L) (upperCount L G : Fin K → ℕ)
    (fun j => upperDensity_pos hK hL j) (fun j => upperCount_le hK hL hw j)
    (fun j k h => upperCenter_separation hK hL j k h) hg
  have hd (j : Fin K) : (upperCount L G j : ℝ)*upperDensity L j*(Real.pi^2/2) =
      (upperCount L G j : ℝ)*cellDeficit L j := by
    unfold upperDensity
    field_simp
  have hc : ((upperPointSet L G K).card : ℝ) = ∑ j : Fin K, (upperCount L G j : ℝ) := by
    exact_mod_cast upperPointSet_card_eq hK hL hG hw
  simp only [hd] at he
  rw [← hc] at he
  simpa only [neg_mul, upperPointSet] using he

theorem upper_mesh_exponent_bound {K n : ℕ} (hK : 0<K) {L G : ℝ}
    (hL : 0<L) (hg : Real.log 2 ≤ 2*G) (hw : 0≤upperWidth L G K)
    (hn : (upperPointSet L G K).card=n) :
    -(∑ x ∈ upperPointSet L G K, (L-x/2)) -
      Real.log (normalized (fun j : Fin n => Real.exp ((upperPointSet L G K).orderEmbOfFin hn j))).det/2 ≤
      (n : ℝ)*Real.log 2/2 - upperWidth L G K/Real.pi^2 *
        (L^2*((K : ℝ)/3-1/(12*K))) + (K : ℝ)*L/4 +
        2*(n : ℝ)^2*Real.exp (-2*G) := by
  have hG : 0<G := by have := Real.log_pos (by norm_num : (1:ℝ)<2); linarith
  rw [log_det_ordered_set, upperPointSet_deficit_sum hK hL hG hw]
  have he := upperPointSet_rowEnergy_bound hK hL hg hw
  rw [hn] at he
  have hf := block_count_objective_le hK hL (upperWidth L G K)
  change (∑ j : Fin K, -(upperCount L G j : ℝ)*cellDeficit L j/2) ≤ _ at hf
  have hs : (∑ j : Fin K, -(upperCount L G j : ℝ)*cellDeficit L j/2) =
      -(∑ j : Fin K, (upperCount L G j : ℝ)*cellDeficit L j)/2 := by
    simp only [neg_mul, Finset.sum_neg_distrib, ← Finset.sum_div, neg_div]
  rw [hs] at hf
  ring_nf at he hf ⊢
  linarith

end Erdos524.CauchyKernel
