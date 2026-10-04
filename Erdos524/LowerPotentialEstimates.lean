import Erdos524.AffinePotentialBoundary
import Erdos524.AffineLowerMeshMoments
import Erdos524.RegressionWeightBounds

namespace Erdos524.QuantileCounting
open Set
open scoped BigOperators
open Erdos524.CauchyKernel Erdos524.RegressionWeightBounds

noncomputable def lowerPotential (L t : ℝ) : ℝ :=
  affinePotential (lowerLeft L) (lowerRight L) (lowerIntercept L) lowerSlope t

theorem lower_full_potential (L t : ℝ) :
    (lowerIntercept L-lowerSlope*t)*(Real.pi^2/2)=L-t/2+100*Real.log L := by
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold lowerIntercept lowerSlope
  field_simp
  <;> ring

theorem exp_neg_nat_log {L : ℝ} (hL : 0<L) (k : ℕ) :
    Real.exp (-(k:ℝ)*Real.log L)=1/L^k := by
  rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hL,one_div]

theorem lower_tail_error_small {L : ℝ} (hL : 16≤L) :
    8*lowerIntercept L*Real.exp (-4*Real.log L)+
      32*lowerSlope*Real.exp (-2*Real.log L)≤1 := by
  have hlpos : 0<L := by linarith
  have hlog : Real.log L≤L := by have := Real.log_le_sub_one_of_pos hlpos; linarith
  have hp : 1≤Real.pi^2 := by have := Real.pi_gt_three; nlinarith
  have he : 8*lowerIntercept L*Real.exp (-4*Real.log L)+
      32*lowerSlope*Real.exp (-2*Real.log L) =
      (16*(L+100*Real.log L)+32*L^2)/(Real.pi^2*L^4) := by
    have h4 := exp_neg_nat_log hlpos 4
    have h2 := exp_neg_nat_log hlpos 2
    norm_num at h4 h2
    simp only [neg_mul]
    rw [h4,h2]
    unfold lowerIntercept lowerSlope
    field_simp
    <;> ring
  rw [he]
  apply (div_le_one (by positivity : 0<Real.pi^2*L^4)).mpr
  have h1 : 16*L≤L^2 := by nlinarith
  have h2 : 256≤L^2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg L)
  have h4 := mul_le_mul_of_nonneg_right hp (pow_nonneg hlpos.le 4)
  nlinarith

theorem lower_boundary_error_small {L : ℝ} (hL : 16≤L) :
    32*lowerSlope*Real.exp (-4*Real.log L)≤1 := by
  have he := lower_tail_error_small hL
  have hp : 0≤8*lowerIntercept L*Real.exp (-4*Real.log L) := by
    have hl : 0≤Real.log L := Real.log_nonneg (by linarith)
    unfold lowerIntercept
    positivity
  have hlog : 0≤Real.log L := Real.log_nonneg (by linarith)
  have hexp := Real.exp_le_exp.mpr (show -4*Real.log L≤ -2*Real.log L by linarith)
  have hm := mul_le_mul_of_nonneg_left hexp (show 0≤32*lowerSlope by unfold lowerSlope; positivity)
  linarith

theorem lowerPotential_interior {L t : ℝ} (hL : 16≤L) (ht0 : 0≤t)
    (ht : t≤2*L+4*Real.log L) :
    |lowerPotential L t-(L-t/2+100*Real.log L)|≤1 := by
  have hL2 : 2≤L := by linarith
  have hlog : 0≤Real.log L := Real.log_nonneg (by linarith)
  have hB : 0<lowerSlope := by unfold lowerSlope; positivity
  have hv := lower_parameters_valid hL2
  have htRight : t≤lowerRight L := by unfold lowerRight; linarith
  have hprod := mul_le_mul_of_nonneg_left htRight hB.le
  have hρ : 0≤lowerIntercept L-lowerSlope*t := by linarith [hv.2.2]
  have hρA : |lowerIntercept L-lowerSlope*t|≤lowerIntercept L := by
    rw [abs_of_nonneg hρ]
    nlinarith
  have hgap : Real.log 2≤4*Real.log L := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<2) hL2
    linarith
  have he := affinePotential_interior_error (lowerLeft L) (lowerRight L) (lowerIntercept L) lowerSlope t
    hB.le hgap (by unfold lowerLeft; linarith) (by unfold lowerRight; linarith)
  rw [lower_full_potential] at he
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρA (by norm_num : (0:ℝ)≤8))
    (Real.exp_pos (-4*Real.log L)).le
  have hh : -(1/2:ℝ)*(4*Real.log L)= -2*Real.log L := by ring
  rw [hh] at he
  change |lowerPotential L t-(L-t/2+100*Real.log L)|≤_ at he
  have hb := lower_tail_error_small hL
  simp only [neg_mul] at he hm hb
  linarith


theorem lowerPotential_boundary {L t : ℝ} (hL : 16≤L) (ht : t≤lowerRight L) :
    lowerPotential L t≤L-t/2+100*Real.log L+1 := by
  have hL2 : 2≤L := by linarith
  have hlog : 0≤Real.log L := Real.log_nonneg (by linarith)
  have hB : 0<lowerSlope := by unfold lowerSlope; positivity
  have hmargin : lowerSlope*(8*Real.log L)≤lowerIntercept L-lowerSlope*t := by
    have he : lowerIntercept L-lowerSlope*t-lowerSlope*(8*Real.log L)=
        lowerSlope*(2*L+192*Real.log L-t) := by unfold lowerIntercept lowerSlope; ring
    have ht' : 0≤2*L+192*Real.log L-t := by unfold lowerRight at ht; linarith
    have hm := mul_nonneg hB.le ht'
    linarith
  have he := affinePotential_boundary_upper (lowerLeft L) (lowerRight L) (lowerIntercept L) lowerSlope t
    hB (by have h := upper_mesh_energy_gap hL2; linarith) hmargin
  rw [lower_full_potential] at he
  have hh : -(1/2:ℝ)*(8*Real.log L)= -4*Real.log L := by ring
  rw [hh] at he
  have hb := lower_boundary_error_small hL
  change lowerPotential L t≤_ at he
  linarith

theorem lower_log_max_bound {L M : ℝ} (hL : 16≤L) (hM0 : 1≤M) (hM : M≤L) :
    Real.log (4*M)≤2*Real.log L := by
  have h4 : 4*M≤L^2 := by nlinarith
  have he := Real.log_le_log (by positivity : 0<4*M) h4
  rwa [Real.log_pow] at he

theorem lower_log_half {L : ℝ} (hL : 16≤L) : (1/2:ℝ)≤Real.log L := by
  have h := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : 2≤L)
  have hb := Real.log_two_gt_d9
  linarith

theorem omittedPotential_even_sum {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    omittedPotential s i t = ∑ j ∈ Finset.univ.erase i, evenPotential (s j-t) := by
  unfold omittedPotential
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg logTanhPotential (abs_sub_comm t (s j))

theorem lower_node_potential_120 {L : ℝ} (hL : 16≤L)
    (hM0 : 1≤lowerIntercept L-lowerSlope*lowerLeft L)
    (hM : lowerIntercept L-lowerSlope*lowerLeft L≤L)
    (mesh : LowerMesh L) (i : Fin ⌊lowerTotal L⌋₊) :
    omittedPotential mesh.node i (mesh.node i)≤L-mesh.node i/2+120*Real.log L := by
  dsimp only [LowerMesh,lowerTotal] at mesh i ⊢
  obtain ⟨hab,hB,hr⟩ := lower_parameters_valid (by linarith : 2≤L)
  have he := affine_node_potential_upper hab hB hr hM0 mesh i
  have hb := lowerPotential_boundary hL (mesh.node_mem i).2
  have hl := lower_log_max_bound hL hM0 hM
  have hh := lower_log_half hL
  have he' : omittedPotential mesh.node i (mesh.node i)≤lowerPotential L (mesh.node i)+
      2*Real.log (4*(lowerIntercept L-lowerSlope*lowerLeft L)) := by
    rw [← omittedPotential_even_sum mesh.node i (mesh.node i)] at he
    exact he
  linarith

theorem lower_omitted_potential_80 {L t : ℝ} (hL : 16≤L)
    (hM0 : 1≤lowerIntercept L-lowerSlope*lowerLeft L)
    (hM : lowerIntercept L-lowerSlope*lowerLeft L≤L)
    (mesh : LowerMesh L) (ht0 : 0≤t) (ht : t≤2*L+4*Real.log L)
    (hne : ∀ j, t≠mesh.node j) (i : Fin ⌊lowerTotal L⌋₊) :
    L-t/2+80*Real.log L≤omittedPotential mesh.node i t := by
  dsimp only [LowerMesh,lowerTotal] at mesh i ⊢
  obtain ⟨hab,hB,hr⟩ := lower_parameters_valid (by linarith : 2≤L)
  have he := affine_omitted_potential_lower hab hB hr hM0 mesh i t
    (fun j _ => Ne.symm (hne j))
  have hb := abs_le.mp (lowerPotential_interior hL ht0 ht)
  have hl := lower_log_max_bound hL hM0 hM
  have hh := lower_log_half hL
  have he' : lowerPotential L t-6*Real.log (4*(lowerIntercept L-lowerSlope*lowerLeft L))-2≤
      omittedPotential mesh.node i t := by
    rw [← omittedPotential_even_sum mesh.node i t] at he
    exact he
  linarith [hb.1]

end Erdos524.QuantileCounting
