import Erdos524.GeometricWalkProbability
import Erdos524.UpperEnvelopeBound

namespace Erdos524.GeometricWalkPayment
open Filter MeasureTheory ProbabilityTheory
open Erdos524.RandomPolynomialModel Erdos524.GeometricWalkScale Erdos524.DyadicUpperScale

noncomputable def walkSum (ω : Ω) (N : ℕ) : ℝ := ∑ i ∈ Finset.range N, ω i

theorem walkSum_abs_le (ω : Ω) (N : ℕ) : |walkSum ω N|≤fullNorm ω N := by
  have h := fullNorm_evaluation_bound ω N ⟨1,by constructor <;> norm_num⟩
  simpa [Erdos524.PolynomialAbel.polynomial,walkSum] using h

theorem walkSum_split (ω : Ω) (a n : ℕ) :
    walkSum ω (a+n)=walkSum ω a+Erdos524.SignSumGaussianComparison.normalizedSum (finiteBlock a n ω)*Real.sqrt (n:ℝ) := by
  cases n with
  | zero => simp [walkSum,Erdos524.SignSumGaussianComparison.normalizedSum]
  | succ n =>
    unfold walkSum Erdos524.SignSumGaussianComparison.normalizedSum
    rw [div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<((n+1:ℕ):ℝ))))]
    rw [Finset.sum_range_add]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun i => ω (a+i)) (n+1)).symm

theorem eventually_scale_step {B : ℕ} (hB : 1<B) :
    ∀ᶠ j : ℕ in atTop, Real.sqrt (B:ℝ)*upperScale (endpoint B j)≤upperScale (endpoint B (j+1)) := by
  have ht := (endpoint_strictMono hB).tendsto_atTop
  filter_upwards [ht.eventually (loglog_nat_tendsto.eventually (eventually_ge_atTop (0:ℝ))),
    ht.eventually (eventually_ge_atTop (2:ℕ))] with j hl hj
  have hprev : (1:ℝ)<endpoint B j := by exact_mod_cast hj
  have hmono : (endpoint B j:ℝ)≤endpoint B (j+1) := by exact_mod_cast (endpoint_strictMono hB).monotone (Nat.le_succ j)
  have hlogs := Real.log_le_log (Real.log_pos hprev) (Real.log_le_log (by positivity : (0:ℝ)<endpoint B j) hmono)
  have hn0 : 0≤Real.log (Real.log (endpoint B (j+1):ℝ)) := hl.trans hlogs
  have hb0 : (0:ℝ)≤B := Nat.cast_nonneg _
  have hsB := Real.sq_sqrt hb0
  have hs0 := Real.sq_sqrt (show 0≤2*(endpoint B j:ℝ)*Real.log (Real.log (endpoint B j:ℝ)) by positivity)
  have hs1 := Real.sq_sqrt (show 0≤2*(endpoint B (j+1):ℝ)*Real.log (Real.log (endpoint B (j+1):ℝ)) by positivity)
  have he : (endpoint B (j+1):ℝ)=(B:ℝ)*(endpoint B j:ℝ) := by simp [endpoint,pow_succ,mul_comm]
  have hmul := mul_le_mul_of_nonneg_left hlogs (show 0≤2*(endpoint B (j+1):ℝ) by positivity)
  have hsq : (Real.sqrt (B:ℝ)*upperScale (endpoint B j))^2≤(upperScale (endpoint B (j+1)))^2 := by
    unfold upperScale
    rw [mul_pow,hsB,hs0,hs1]
    rw [he] at hmul ⊢
    nlinarith
  exact (sq_le_sq₀ (by unfold upperScale; positivity) (by unfold upperScale; positivity)).mp hsq

theorem choose_geometric_parameters {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    ∃ c : ℝ, ∃ B : ℕ, 0<c ∧ a<c ∧ 1<B ∧ c^2*(B:ℝ)/((B:ℝ)-1)<1 ∧ 2≤(c-a)*Real.sqrt (B:ℝ) := by
  let c := (1+a)/2
  have hc : 0<c := by dsimp [c]; linarith
  have hca : a<c := by dsimp [c]; linarith
  have hc1 : c<1 := by dsimp [c]; linarith
  have hc2 : 0<1-c^2 := by nlinarith
  have hgap : 0<c-a := sub_pos.mpr hca
  obtain ⟨B,hB⟩ := exists_nat_gt (max 2 (max (1/(1-c^2)) (4/(c-a)^2)))
  have hb2 : (2:ℝ)<B := (le_max_left _ _).trans_lt hB
  have hb1 : (1:ℝ)<B := by linarith
  have hBn : 1<B := by exact_mod_cast hb1
  have hbudget : 1/(1-c^2)<(B:ℝ) := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hB)
  have hsq : 4/(c-a)^2<(B:ℝ) := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hB)
  refine ⟨c,B,hc,hca,hBn,?_,?_⟩
  · apply (div_lt_iff₀ (sub_pos.mpr hb1)).mpr
    have h := (div_lt_iff₀ hc2).mp hbudget
    nlinarith
  · have h := (div_lt_iff₀ (sq_pos_of_pos hgap)).mp hsq
    have he := Real.sq_sqrt (show (0:ℝ)≤B by positivity)
    have hpos : 0≤(c-a)*Real.sqrt (B:ℝ) := by positivity
    have hs : 4<((c-a)*Real.sqrt (B:ℝ))^2 := by rw [mul_pow,he]; nlinarith
    nlinarith

end Erdos524.GeometricWalkPayment
