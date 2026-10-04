import Erdos524.UpperMeshNonempty
import Erdos524.UpperMeshProbability

namespace Erdos524.CauchyKernel
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory WithLp
open Erdos524.FiniteKernelPerturbation Erdos524.GaussianBoxDensity

 theorem eventually_upperWidth_one {K : ℕ} (hK : 0<K) :
    ∀ᶠ L : ℝ in atTop, 1≤upperWidth L (4*Real.log L) K := by
  have hk : (0 : ℝ)<K := by positivity
  have hsmall := Real.isLittleO_log_id_atTop.bound (by positivity : (0:ℝ)<1/(8*K))
  filter_upwards [hsmall, eventually_ge_atTop (max (K:ℝ) 1)] with L hlog hL
  have hL1 : 1≤L := le_trans (le_max_right _ _) hL
  have hLK : (K:ℝ)≤L := le_trans (le_max_left _ _) hL
  rw [id_eq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL1),
    abs_of_nonneg (by linarith : 0≤L)] at hlog
  unfold upperWidth
  have hb : 8*Real.log L ≤ L/K := by
    have he : 8*((1/(8*K))*L) = L/K := by field_simp
    nlinarith
  have hd : 1≤L/K := (le_div_iff₀ hk).mpr (by simpa using hLK)
  ring_nf at hb hd ⊢
  linarith

theorem eventually_upperPointSet_nonempty {K : ℕ} (hK : 0<K) :
    ∀ᶠ L : ℝ in atTop, (upperPointSet L (4*Real.log L) K).Nonempty := by
  filter_upwards [eventually_upperWidth_one hK, eventually_ge_atTop (Real.pi^2)] with L hw hL
  exact upperPointSet_nonempty hK hL hw


theorem mesh_cross_error_le_two {L N : ℝ} (hL : 2≤L) (hN : 0≤N) (hNmax : N≤L^2) :
    2*N^2*Real.exp (-2*(4*Real.log L)) ≤ 2 := by
  have hlpos : 0<L := by linarith
  have hexp : Real.exp (8*Real.log L) = L^8 := by
    rw [show (8:ℝ) = (8:ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hlpos]
  rw [show -2*(4*Real.log L) = -(8*Real.log L) by ring, Real.exp_neg, hexp,
    ← div_eq_mul_inv]
  apply (div_le_iff₀ (pow_pos hlpos 8)).mpr
  have hNsq : N^2≤L^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hNmax) (by positivity : 0≤L^2+N)]
  have h4 : (1:ℝ)≤L^4 := by simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) (by linarith : 1≤L) 4
  nlinarith [mul_nonneg (pow_nonneg hlpos.le 4) (sub_nonneg.mpr h4)]

theorem eventually_log_remainder_le {C ε : ℝ} (hC : 0<C) (heps : 0<ε) :
    ∀ᶠ L : ℝ in atTop, C*L^2*(Real.log L+1) ≤ ε*L^3 := by
  have hs := Real.isLittleO_log_id_atTop.bound (by positivity : 0<ε/(2*C))
  filter_upwards [hs, eventually_ge_atTop (max 1 (2*C/ε))] with L hlog hL
  have hL1 : 1≤L := le_trans (le_max_left _ _) hL
  have hbound : 2*C/ε≤L := le_trans (le_max_right _ _) hL
  rw [id_eq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL1),
    abs_of_nonneg (by linarith : 0≤L)] at hlog
  have hlogC : C*Real.log L ≤ ε*L/2 := by
    have h := mul_le_mul_of_nonneg_left hlog hC.le
    have he : C*(ε/(2*C)*L) = ε*L/2 := by field_simp
    rwa [he] at h
  have hCL : C≤ε*L/2 := by
    have h := (div_le_iff₀ heps).mp hbound
    nlinarith
  have hsum : C*(Real.log L+1)≤ε*L := by nlinarith
  have h := mul_le_mul_of_nonneg_right hsum (sq_nonneg L)
  nlinarith


noncomputable def upperLeading (K : ℕ) : ℝ :=
  (2/(3*Real.pi^2))*(1-1/(4*(K:ℝ)^2))
noncomputable def upperCorrection (K : ℕ) : ℝ :=
  (8/Real.pi^2)*((K:ℝ)/3-1/(12*K))
noncomputable def boxConstant : ℝ := 2*Real.log 2-Real.log (Real.sqrt (2*Real.pi))
noncomputable def upperRemainderConstant (K : ℕ) : ℝ :=
  |upperCorrection K|+(K:ℝ)+|boxConstant|+2
noncomputable def upperMeshExponent (K : ℕ) (L N : ℝ) : ℝ :=
  -upperWidth L (4*Real.log L) K / Real.pi^2 * (L^2*((K:ℝ)/3-1/(12*K))) +
    (K:ℝ)*L/4 + 2*N^2*Real.exp (-2*(4*Real.log L)) + N*boxConstant

theorem upperMeshExponent_identity {K : ℕ} (hK : 0<K) (L N : ℝ) :
    upperMeshExponent K L N = -upperLeading K*L^3 + upperCorrection K*L^2*Real.log L +
      (K:ℝ)*L/4 + 2*N^2*Real.exp (-2*(4*Real.log L)) + N*boxConstant := by
  have he := block_leading_coefficient hK L
  unfold upperMeshExponent upperLeading upperCorrection upperWidth
  ring_nf at he ⊢
  linarith

theorem upperRemainderConstant_pos (K : ℕ) : 0<upperRemainderConstant K := by
  unfold upperRemainderConstant
  positivity

theorem upperMeshExponent_remainder {K : ℕ} (hK : 0<K) {L N : ℝ}
    (hL : 2≤L) (hN : 0≤N) (hNmax : N≤L^2) :
    upperMeshExponent K L N ≤ -upperLeading K*L^3 +
      upperRemainderConstant K*L^2*(Real.log L+1) := by
  rw [upperMeshExponent_identity hK]
  have hlog : 0≤Real.log L := Real.log_nonneg (by linarith)
  have hLsq : 1≤L^2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_right (le_abs_self (upperCorrection K))
    (mul_nonneg (sq_nonneg L) hlog)
  have hk : (K:ℝ)*L/4 ≤ (K:ℝ)*L^2 := by
    have h := mul_le_mul_of_nonneg_left (by nlinarith : L/4≤L^2) (Nat.cast_nonneg K : (0:ℝ)≤K)
    nlinarith
  have ht := mesh_cross_error_le_two hL hN hNmax
  have hc : N*boxConstant ≤ L^2*|boxConstant| :=
    (mul_le_mul_of_nonneg_left (le_abs_self boxConstant) hN).trans
      (mul_le_mul_of_nonneg_right hNmax (abs_nonneg _))
  have hp := mul_nonneg (abs_nonneg (upperCorrection K)) (sq_nonneg L)
  have hq := mul_nonneg (by positivity : (0:ℝ)≤(K:ℝ)+|boxConstant|+2)
    (mul_nonneg (sq_nonneg L) hlog)
  unfold upperRemainderConstant
  nlinarith

theorem eventually_upperMeshExponent {K : ℕ} (hK : 0<K) {ε : ℝ} (heps : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ N : ℝ, 0≤N → N≤L^2 →
      upperMeshExponent K L N ≤ -(upperLeading K-ε)*L^3 := by
  filter_upwards [eventually_log_remainder_le (upperRemainderConstant_pos K) heps,
    eventually_ge_atTop (2:ℝ)] with L herr hL
  intro N hN hNmax
  have he := upperMeshExponent_remainder hK hL hN hNmax
  nlinarith


theorem eventually_upper_mesh_probability {K : ℕ} (hK : 0<K) {ε : ℝ} (heps : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∃ n : ℕ, ∃ hn : (upperPointSet L (4*Real.log L) K).card=n+1,
      let t := (upperPointSet L (4*Real.log L) K).orderEmbOfFin hn
      (multivariateGaussian 0 (normalizedFiniteKernel (fun i => Real.exp (t i))))
        (ofLp ⁻¹' box (fun i => Real.exp (-(L-t i/2)))) ≤
      ENNReal.ofReal (Real.exp (-(upperLeading K-ε)*L^3)) := by
  filter_upwards [eventually_upperWidth_one hK, eventually_upperPointSet_nonempty hK,
    eventually_upperMeshExponent hK heps, eventually_ge_atTop (2:ℝ)] with L hw hne herr hL
  let s := upperPointSet L (4*Real.log L) K
  have hc : 0<s.card := Finset.card_pos.mpr hne
  let n := s.card-1
  have hn : s.card=n+1 := by dsimp [n]; omega
  refine ⟨n, hn, ?_⟩
  have hwidth : 0≤upperWidth L (4*Real.log L) K := by linarith
  have hp := Erdos524.UpperMeshProbability.upper_mesh_gaussian_probability hK hL hwidth hn
  have hG : 0≤4*Real.log L := by
    have := Real.log_nonneg (by linarith : 1≤L)
    positivity
  have hsize := upperPointSet_card_le_sq hK (by linarith : 0<L) hG hwidth
  change (s.card : ℝ)≤L^2 at hsize
  rw [hn] at hsize
  have he := herr (n+1) (by positivity) (by simpa using hsize)
  change _ ≤ ENNReal.ofReal (Real.exp (upperMeshExponent K L (n+1))) at hp
  exact hp.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))


theorem exists_upperLeading_close {ε : ℝ} (heps : 0<ε) :
    ∃ K : ℕ, 0<K ∧ 2/(3*Real.pi^2)-ε/2 ≤ upperLeading K := by
  let a : ℝ := 2/(3*Real.pi^2)
  have ha : 0<a := by dsimp [a]; positivity
  obtain ⟨K,hK⟩ := exists_nat_gt (max 1 (a/ε+1))
  have hk1 : (1:ℝ)<K := lt_of_le_of_lt (le_max_left _ _) hK
  have hk0 : 0<K := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ)<1) hk1)
  have hkbound : a/ε+1<(K:ℝ) := lt_of_le_of_lt (le_max_right _ _) hK
  have hax : a≤ε*K := by
    have hdiv : a/ε≤(K:ℝ) := by linarith
    have hm := (div_le_iff₀ heps).mp hdiv
    linarith
  have hkpow : (K:ℝ)≤2*(K:ℝ)^2 := by nlinarith
  have hb : a≤2*ε*(K:ℝ)^2 := by
    have hm := mul_le_mul_of_nonneg_left hkpow heps.le
    nlinarith
  have hgap : a/(4*(K:ℝ)^2)≤ε/2 := by
    apply (div_le_iff₀ (by positivity : 0<4*(K:ℝ)^2)).mpr
    nlinarith
  refine ⟨K,hk0,?_⟩
  unfold upperLeading
  change a-ε/2≤a*(1-1/(4*(K:ℝ)^2))
  have he : a*(1-1/(4*(K:ℝ)^2)) = a-a/(4*(K:ℝ)^2) := by ring
  rw [he]
  linarith

theorem sharp_finite_mesh_upper {ε : ℝ} (heps : 0<ε) :
    ∃ K : ℕ, 0<K ∧ ∀ᶠ L : ℝ in atTop,
      ∃ n : ℕ, ∃ hn : (upperPointSet L (4*Real.log L) K).card=n+1,
        let t := (upperPointSet L (4*Real.log L) K).orderEmbOfFin hn
        (multivariateGaussian 0 (normalizedFiniteKernel (fun i => Real.exp (t i))))
          (ofLp ⁻¹' box (fun i => Real.exp (-(L-t i/2)))) ≤
        ENNReal.ofReal (Real.exp (-(2/(3*Real.pi^2)-ε)*L^3)) := by
  obtain ⟨K,hK,hclose⟩ := exists_upperLeading_close heps
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_upper_mesh_probability hK (by linarith : 0<ε/2),
    eventually_ge_atTop (0:ℝ)] with L hprob hL
  obtain ⟨n,hn,hp⟩ := hprob
  refine ⟨n,hn,hp.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))⟩
  have hm := mul_le_mul_of_nonneg_right hclose (pow_nonneg hL 3)
  nlinarith

end Erdos524.CauchyKernel
