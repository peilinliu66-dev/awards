import Erdos524.GeometricWalkPayment

namespace Erdos524.UpperEnvelopeLower
open Filter MeasureTheory ProbabilityTheory
open Erdos524.RandomPolynomialModel Erdos524.GeometricWalkScale Erdos524.GeometricWalkProbability
open Erdos524.GeometricWalkPayment Erdos524.DyadicUpperScale Erdos524.UpperEnvelopeBound

theorem ae_frequent_upper_envelope {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    ∀ᵐ ω ∂P, ∃ᶠ N in atTop, a*upperScale N≤fullNorm ω N := by
  obtain ⟨c,B,hc,hca,hB,hp,hpay⟩ := choose_geometric_parameters ha ha1
  have ht := (endpoint_strictMono hB).tendsto_atTop
  filter_upwards [ae_frequent_freshSum_large hB hc hp,ae_eventual_upper_envelope (by norm_num : (1:ℝ)<2)] with ω hf ho
  have hfreq : ∃ᶠ j in atTop, a*upperScale (endpoint B (j+1))≤fullNorm ω (endpoint B (j+1)) := by
    apply ((hf.and_eventually (ht.eventually ho)).and_eventually (eventually_scale_step hB)).mono
    intro j hj
    have hm : (0:ℝ)<blockLength B j := by exact_mod_cast blockLength_pos hB j
    have hlarge := (div_lt_iff₀ (Real.sqrt_pos.mpr hm)).mp hj.1.1
    change c*upperScale (endpoint B (j+1))<freshSum B j ω*Real.sqrt (blockLength B j:ℝ) at hlarge
    have hold : fullNorm ω (endpoint B j)≤(c-a)*upperScale (endpoint B (j+1)) := by
      have h0 : 0≤upperScale (endpoint B j) := Real.sqrt_nonneg _
      have h1 := mul_le_mul_of_nonneg_right hpay h0
      have h2 := mul_le_mul_of_nonneg_left hj.2 (sub_pos.mpr hca).le
      nlinarith [hj.1.2]
    have hsum := walkSum_split ω (endpoint B j) (blockLength B j)
    have he : endpoint B j+blockLength B j=endpoint B (j+1) :=
      Nat.add_sub_of_le ((endpoint_strictMono hB).monotone (Nat.le_succ j))
    rw [he] at hsum
    change walkSum ω (endpoint B (j+1))=walkSum ω (endpoint B j)+freshSum B j ω*Real.sqrt (blockLength B j:ℝ) at hsum
    have hprev := (abs_le.mp (walkSum_abs_le ω (endpoint B j))).1
    have hnext := (le_abs_self (walkSum ω (endpoint B (j+1)))).trans (walkSum_abs_le ω (endpoint B (j+1)))
    linarith
  apply frequently_atTop.mpr
  intro N
  obtain ⟨j,hj,hlarge⟩ := frequently_atTop.mp hfreq N
  exact ⟨endpoint B (j+1),hj.trans ((Nat.le_succ j).trans ((endpoint_strictMono hB).id_le _)),hlarge⟩

theorem ae_frequent_upper_ratio {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    ∀ᵐ ω ∂P, ∃ᶠ N in atTop, a≤fullNorm ω N/upperScale N := by
  filter_upwards [ae_frequent_upper_envelope ha ha1] with ω hω
  exact (hω.and_eventually eventually_upperScale_pos).mono (fun N h => (le_div_iff₀ h.2).mpr h.1)

theorem ae_upper_normalized_limsup_ge_one :
    ∀ᵐ ω ∂P, 1≤limsup (fun N => fullNorm ω N/upperScale N) atTop := by
  have hcount : ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ᶠ N in atTop,
      1-1/(k+2:ℝ)≤fullNorm ω N/upperScale N := by
    apply ae_all_iff.mpr
    intro k
    have hk : (1:ℝ)<k+2 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
    exact ae_frequent_upper_ratio (by have := (div_lt_iff₀ (by positivity : (0:ℝ)<k+2)).mpr (show (1:ℝ)<1*(k+2) by linarith); linarith)
      (by have := one_div_pos.mpr (show (0:ℝ)<k+2 by positivity); linarith)
  filter_upwards [hcount,ae_eventual_upper_ratio (by norm_num : (0:ℝ)<1)] with ω hω hu
  have hb : IsBoundedUnder (·≤·) atTop (fun N => fullNorm ω N/upperScale N) := ⟨2,by norm_num at hu ⊢; exact hu⟩
  apply le_of_forall_pos_le_add
  intro ε heps
  obtain ⟨k,hk⟩ := exists_nat_gt (1/ε)
  have hsmall : 1/(k+2:ℝ)≤ε := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<k+2)).mpr
    have h := (div_lt_iff₀ heps).mp hk
    nlinarith
  have h := le_limsup_of_frequently_le (hω k) hb
  linarith

theorem ae_upper_normalized_limsup_eq_one :
    ∀ᵐ ω ∂P, limsup (fun N => fullNorm ω N/upperScale N) atTop=1 := by
  filter_upwards [ae_upper_normalized_limsup_le_one,ae_upper_normalized_limsup_ge_one] with ω hle hge
  exact le_antisymm hle hge

end Erdos524.UpperEnvelopeLower
