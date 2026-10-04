import Erdos524.DyadicUpperScale

namespace Erdos524.UpperEnvelopeBound
open MeasureTheory ProbabilityTheory Filter
open Erdos524.RandomPolynomialModel Erdos524.DyadicMesh Erdos524.DyadicUpperProbability Erdos524.DyadicUpperScale

theorem ae_eventual_upper_envelope {d : ℝ} (hd : 1<d) :
    ∀ᵐ ω ∂P, ∀ᶠ N in atTop, fullNorm ω N≤d*upperScale N := by
  let c : ℝ := (1+d)/2
  have hc1 : 1<c := by dsimp [c]; linarith
  have hc : 0<c := by linarith
  have hcd : c<d := by dsimp [c]; linarith
  have hgap : 0<c^2-1 := by nlinarith
  obtain ⟨Q,hQ⟩ := exists_nat_gt (2/(c^2-1))
  have hQp : (0:ℝ)<Q := (by positivity : (0:ℝ)<2/(c^2-1)).trans hQ
  have hQ0 : 0<Q := by exact_mod_cast hQp
  have hmargin : 1+2/(Q:ℝ)<c^2 := by
    have h := (div_lt_iff₀ hgap).mp hQ
    have he : 2/(Q:ℝ)<c^2-1 := (div_lt_iff₀ hQp).mpr (by nlinarith)
    linarith
  filter_upwards [ae_eventual_mesh_maximum hc hQ0 hmargin] with ω hω
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hω.and (eventually_threshold_le_upperScale hc hcd Q))
  filter_upwards [eventually_ge_atTop (4*2^K)] with N hN
  obtain ⟨k,hk,j,hj,hlo,hhi⟩ := cover_after (fun _ => Q) (fun _ => hQ0) K N hN
  have h := hK k hk
  exact (h.1 j hj N hhi.le).le.trans (h.2 j N hlo)

theorem ae_eventual_upper_ratio {ε : ℝ} (heps : 0<ε) :
    ∀ᵐ ω ∂P, ∀ᶠ N in atTop, fullNorm ω N/upperScale N≤1+ε := by
  filter_upwards [ae_eventual_upper_envelope (show 1<1+ε by linarith)] with ω hω
  filter_upwards [hω,eventually_upperScale_pos] with N hN hpos
  exact (div_le_iff₀ hpos).mpr hN

theorem ae_eventual_upper_ratio_all_slack :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0<ε → ∀ᶠ N in atTop, fullNorm ω N/upperScale N≤1+ε := by
  have hcount : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ N in atTop, fullNorm ω N/upperScale N≤1+1/(k+1:ℝ) := by
    apply ae_all_iff.mpr
    intro k
    exact ae_eventual_upper_ratio (by positivity)
  filter_upwards [hcount] with ω hω
  intro ε heps
  obtain ⟨k,hk⟩ := exists_nat_gt (1/ε)
  have hkpos : (0:ℝ)<k+1 := by positivity
  have hsmall : 1/(k+1:ℝ)≤ε := by
    apply (div_le_iff₀ hkpos).mpr
    have h := (div_lt_iff₀ heps).mp hk
    nlinarith
  exact (hω k).mono (fun N hN => hN.trans (by linarith))

theorem ae_upper_normalized_limsup_le_one :
    ∀ᵐ ω ∂P, limsup (fun N => fullNorm ω N/upperScale N) atTop≤1 := by
  filter_upwards [ae_eventual_upper_ratio_all_slack] with ω hω
  have hcb : IsCoboundedUnder (·≤·) atTop (fun N => fullNorm ω N/upperScale N) :=
    isCoboundedUnder_le_of_le atTop (fun N => div_nonneg (fullNorm_nonneg ω N) (Real.sqrt_nonneg _))
  apply le_of_forall_pos_le_add
  intro ε heps
  exact limsup_le_of_le hcb (hω ε heps)

end Erdos524.UpperEnvelopeBound
