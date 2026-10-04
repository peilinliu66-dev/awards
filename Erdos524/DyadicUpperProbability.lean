import Mathlib.Tactic
import Erdos524.DyadicMesh
import Erdos524.RandomPolynomialMaximal
import Mathlib.Analysis.PSeries
import Mathlib.Probability.BorelCantelli

namespace Erdos524.DyadicUpperProbability
open MeasureTheory ProbabilityTheory Filter Set
open Erdos524.DyadicMesh Erdos524.RandomPolynomialModel

noncomputable def threshold (c : ℝ) (k Q j : ℕ) : ℝ :=
  c*Real.sqrt (2*(point k Q j:ℝ)*Real.log (k+2:ℝ))
noncomputable def badEvent (c : ℝ) (Q k : ℕ) : Set Ω :=
  ⋃ j : Fin Q, {ω | ∃ n≤point k Q (j.val+1), threshold c k Q j.val≤fullNorm ω n}

theorem point_pos (k Q j : ℕ) : 0<point k Q j := by
  have h := point_lower k Q j
  have hp : 0<2^k := pow_pos (by norm_num) _
  omega

theorem threshold_pos {c : ℝ} (hc : 0<c) (k Q j : ℕ) : 0<threshold c k Q j := by
  unfold threshold
  have hp : (0:ℝ)<point k Q j := by exact_mod_cast point_pos k Q j
  have hl : 0<Real.log (k+2:ℝ) := Real.log_pos (by have hh := Nat.cast_nonneg (α := ℝ) k; linarith)
  positivity

theorem mesh_one_probability {c : ℝ} (hc : 0<c) {Q k : ℕ} (hQ : 0<Q) (hQk : Q≤2^k) (j : ℕ) :
    P.real {ω | ∃ n≤point k Q (j+1), threshold c k Q j≤fullNorm ω n}≤
      4*(k+2:ℝ)^(-(c^2/(1+2/(Q:ℝ)))) := by
  have h := fullNorm_maximal_tail (point_pos k Q (j+1)) (threshold_pos hc k Q j)
  have hA : (0:ℝ)<point k Q j := by exact_mod_cast point_pos k Q j
  have hB : (0:ℝ)<point k Q (j+1) := by exact_mod_cast point_pos k Q (j+1)
  have hQp : (0:ℝ)<Q := by exact_mod_cast hQ
  have hR : 0<1+2/(Q:ℝ) := by positivity
  have hk : (0:ℝ)<k+2 := by positivity
  have hlog : 0≤Real.log (k+2:ℝ) := Real.log_nonneg (by have hh := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hsq : (threshold c k Q j)^2=c^2*(2*(point k Q j:ℝ)*Real.log (k+2:ℝ)) := by
    unfold threshold
    rw [mul_pow,Real.sq_sqrt (by positivity)]
  rw [hsq] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [Real.rpow_def_of_pos hk]
  apply Real.exp_le_exp.mpr
  have hratio := point_step_ratio k Q j hQ hQk
  have hp0 : 0≤c^2/(1+2/(Q:ℝ)) := by positivity
  have hp := mul_le_mul_of_nonneg_left hratio hp0
  have he : c^2/(1+2/(Q:ℝ))*((1+2/(Q:ℝ))*(point k Q j:ℝ))=c^2*(point k Q j:ℝ) := by field_simp
  rw [he] at hp
  have hmul := mul_le_mul_of_nonneg_right hp hlog
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(point k Q (j+1):ℝ))).mpr
  nlinarith

theorem badEvent_probability {c : ℝ} (hc : 0<c) {Q k : ℕ} (hQ : 0<Q) (hQk : Q≤2^k) :
    P.real (badEvent c Q k)≤(4*(Q:ℝ))*(k+2:ℝ)^(-(c^2/(1+2/(Q:ℝ)))) := by
  unfold badEvent
  have h := measureReal_iUnion_fintype_le (μ := P)
    (fun j : Fin Q => {ω | ∃ n≤point k Q (j.val+1), threshold c k Q j.val≤fullNorm ω n})
  apply h.trans
  calc
    _ ≤ ∑ _j : Fin Q, 4*(k+2:ℝ)^(-(c^2/(1+2/(Q:ℝ)))) :=
      Finset.sum_le_sum (fun j _ => mesh_one_probability hc hQ hQk j.val)
    _ = _ := by simp; ring

theorem ae_eventual_mesh_maximum {c : ℝ} (hc : 0<c) {Q : ℕ} (hQ : 0<Q)
    (hmargin : 1+2/(Q:ℝ)<c^2) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ j<Q, ∀ n≤point k Q (j+1), fullNorm ω n<threshold c k Q j := by
  have hQp : (0:ℝ)<Q := by exact_mod_cast hQ
  have hR : 0<1+2/(Q:ℝ) := by positivity
  have hp : 1<c^2/(1+2/(Q:ℝ)) := (lt_div_iff₀ hR).mpr (by simpa using hmargin)
  have hsum : Summable (fun k : ℕ => (4*(Q:ℝ))*(k+2:ℝ)^(-(c^2/(1+2/(Q:ℝ))))) := by
    have hs := Real.summable_nat_rpow.mpr (by linarith : -(c^2/(1+2/(Q:ℝ))) < -1)
    have hs' := (summable_nat_add_iff 2).mpr hs
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hs'.mul_left (4*(Q:ℝ))
  have hsP : Summable (fun k : ℕ => P.real (badEvent c Q k)) := by
    apply Summable.of_norm_bounded_eventually_nat hsum
    filter_upwards [eventually_ge_atTop Q] with k hk
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    exact badEvent_probability hc hQ (hk.trans (index_le_two_pow k))
  have hfinite : (∑' k, P (badEvent c Q k))≠⊤ := by
    have h := hsP.tsum_ofReal_lt_top
    simp only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top P _)] at h
    exact ne_of_lt h
  filter_upwards [ae_eventually_notMem hfinite] with ω hω
  filter_upwards [hω] with k hk
  intro j hj n hn
  apply lt_of_not_ge
  intro hbad
  exact hk (Set.mem_iUnion.mpr ⟨⟨j,hj⟩,n,hn,hbad⟩)

end Erdos524.DyadicUpperProbability
