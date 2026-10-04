import Erdos524.UpperBlockMesh
import Erdos524.FiniteKernelPerturbation
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Erdos524.CauchyKernel
open scoped BigOperators

theorem two_mul_le_exp {z : ℝ} (hz : 0 ≤ z) : 2*z ≤ Real.exp z := by
  have h := Real.add_one_le_exp (z/2)
  have he : Real.exp z = Real.exp (z/2)^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  have hp : 0 ≤ Real.exp (z/2)+1+z/2 := by positivity
  have hm := mul_nonneg (sub_nonneg.mpr h) hp
  nlinarith [sq_nonneg (z/2-1)]

theorem cutoff_scalar_bound {L N : ℝ} (hL : 2 ≤ L) (hN : 0 ≤ N) (hNmax : N ≤ L^2) :
    2*N^2*Real.exp (2*L-2*L^4) ≤ 1 := by
  have hL2 : 4 ≤ L^2 := by nlinarith
  have hpow : 2*L ≤ L^4 := by
    have h1 : 2*L ≤ L^2 := by nlinarith
    have h2 := mul_nonneg (sq_nonneg L) (by linarith : 0 ≤ L^2-1)
    nlinarith
  have hNsq : N^2 ≤ L^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hNmax) (by positivity : 0 ≤ L^2+N)]
  calc
    _ ≤ 2*L^4*Real.exp (-L^4) := by
      apply mul_le_mul
      · nlinarith
      · exact Real.exp_le_exp.mpr (by linarith)
      · positivity
      · positivity
    _ ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
      exact two_mul_le_exp (by positivity)

theorem upperPointSet_card_le_sq {K : ℕ} (hK : 0<K) {L G : ℝ}
    (hL : 0<L) (hG : 0≤G) (hw : 0≤upperWidth L G K) :
    ((upperPointSet L G K).card : ℝ) ≤ L^2 := by
  apply (upperPointSet_card_bound hK hL hG hw).trans
  apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
  have hp := Real.pi_gt_three
  nlinarith [mul_nonneg (sq_nonneg L) (by nlinarith : 0 ≤ Real.pi^2-2)]


theorem upper_mesh_gap_condition {L : ℝ} (hL : 2≤L) :
    1/(2*L/Real.pi^2) ≤ 2*(4*Real.log L) := by
  have hlpos : 0<L := by linarith
  have hlog : (1/2 : ℝ) ≤ Real.log L := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<2) hL
    have hb := Real.log_two_gt_d9
    linarith
  rw [one_div_div]
  apply (div_le_iff₀ (by positivity : 0<2*L)).mpr
  have hp := Real.pi_lt_four
  have hm := mul_nonneg (sub_nonneg.mpr hlog) (by linarith : 0≤L-2)
  nlinarith [Real.pi_pos]

theorem upper_mesh_energy_gap {L : ℝ} (hL : 2≤L) : Real.log 2 ≤ 2*(4*Real.log L) := by
  have h := Real.log_le_log (by norm_num : (0:ℝ)<2) hL
  have hp := Real.log_pos (by norm_num : (1:ℝ)<2)
  linarith

theorem upper_mesh_exp_min {K : ℕ} (hK : 0<K) {L : ℝ} (hL : 2≤L)
    (hw : 0≤upperWidth L (4*Real.log L) K) {x : ℝ}
    (hx : x ∈ upperPointSet L (4*Real.log L) K) : L^4 ≤ Real.exp x := by
  have hlpos : 0<L := by linarith
  have he := Real.exp_le_exp.mpr (upperPointSet_min hK hlpos hw hx)
  have hp : Real.exp (4*Real.log L) = L^4 := by
    rw [show (4:ℝ) = (4:ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hlpos]
  rwa [hp] at he

theorem upper_mesh_actual_half_gap {K n : ℕ} (hK : 0<K) {L : ℝ} (hL : 2≤L)
    (hw : 0≤upperWidth L (4*Real.log L) K)
    (hn : (upperPointSet L (4*Real.log L) K).card=n+1) :
    (Erdos524.FiniteKernelPerturbation.normalizedFiniteKernel
      (fun i : Fin (n+1) => Real.exp ((upperPointSet L (4*Real.log L) K).orderEmbOfFin hn i)) -
      (1/2 : ℝ) • normalized
        (fun i : Fin (n+1) => Real.exp ((upperPointSet L (4*Real.log L) K).orderEmbOfFin hn i))).PosSemidef := by
  have hlpos : 0<L := by linarith
  have hG : 0≤4*Real.log L := by
    have := Real.log_nonneg (by linarith : 1≤L)
    positivity
  have hsize := upperPointSet_card_le_sq hK hlpos hG hw
  rw [hn] at hsize
  have hsep := ordered_set_full_separation (upperPointSet L (4*Real.log L) K) hn
    (by positivity : 0<2*L/Real.pi^2)
    (upperPointSet_separated hK hlpos hw (upper_mesh_gap_condition hL))
  apply Erdos524.FiniteKernelPerturbation.separated_normalizedFiniteKernel_half_gap _
    (by positivity : 0<2*L/Real.pi^2) hsep (L^4)
  · intro i
    exact upper_mesh_exp_min hK hL hw ((upperPointSet L (4*Real.log L) K).orderEmbOfFin_mem hn i)
  · have he := cutoff_scalar_bound hL (by positivity : (0:ℝ)≤(n+1:ℝ)) (by simpa using hsize)
    have hp : Real.pi^2 ≠ 0 := ne_of_gt (sq_pos_of_pos Real.pi_pos)
    simpa only [div_mul_cancel₀ _ hp] using he

end Erdos524.CauchyKernel
