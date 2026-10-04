import Erdos524.GeometricWalkScale
import Erdos524.SparseBlockBorelCantelli

namespace Erdos524.GeometricWalkProbability
open MeasureTheory ProbabilityTheory Filter Set
open Erdos524.RandomPolynomialModel Erdos524.GeometricWalkScale Erdos524.SignSumGaussianComparison
open Erdos524.SignGaussianMoments

noncomputable def freshSum (B j : ℕ) (ω : Ω) : ℝ :=
  normalizedSum (finiteBlock (endpoint B j) (blockLength B j) ω)

theorem measurable_freshSum (B j : ℕ) : Measurable (freshSum B j) :=
  (normalizedSum_measurable _).comp (measurable_finiteBlock _ _)

theorem freshSum_law (B j : ℕ) (x : ℝ) :
    P.real {ω | x<freshSum B j ω}=
      (Measure.pi (fun _ : Fin (blockLength B j) => signLaw)).real {z | x<normalizedSum z} := by
  have h := congrArg (fun μ : Measure (Fin (blockLength B j) → ℝ) => μ.real {z | x<normalizedSum z})
    (finiteBlock_law (endpoint B j) (blockLength B j))
  unfold Measure.real at h
  rw [Measure.map_apply (measurable_finiteBlock _ _) (measurableSet_lt measurable_const (normalizedSum_measurable _))] at h
  exact h

theorem freshSum_events_independent {B : ℕ} (hB : 1<B) (R : ℕ → ℝ) :
    iIndepSet (fun j => {ω | R j<freshSum B j ω}) P := by
  have hi : iIndepFun (freshSum B) P :=
    (consecutive_blocks_independent (endpoint B) (endpoint_strictMono hB)).comp
      (fun j => normalizedSum) (fun j => normalizedSum_measurable _)
  apply (iIndepSet_iff_meas_biInter (fun j => measurableSet_lt measurable_const (measurable_freshSum B j))).mpr
  intro s
  apply hi.meas_biInter
  intro j hj
  exact measurableSet_Ioi.preimage (comap_measurable (freshSum B j))

theorem eventual_freshSum_probability {B : ℕ} (hB : 1<B) {c : ℝ} (hc : 0<c)
    (hp : c^2*(B:ℝ)/((B:ℝ)-1)<1) :
    ∀ᶠ j : ℕ in atTop, 1/(j+2:ℝ)≤P.real {ω | threshold B c j<freshSum B j ω} := by
  have hb : (1:ℝ)<B := by exact_mod_cast hB
  have hp0 : 0<c^2*(B:ℝ)/((B:ℝ)-1) := by positivity
  have ha : 0<Real.log (B:ℝ) := Real.log_pos hb
  have hJ : Tendsto (fun j : ℕ => (j:ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have ht := hJ.eventually (Erdos524.ModerateSignTail.eventual_sum_moderate_lower
    (C := 2*(c^2*(B:ℝ)/((B:ℝ)-1))*|Real.log (Real.log (B:ℝ))|)
    (C₀ := 2*Real.log (B:ℝ)-Real.log ((B:ℝ)-1)) hp0 hp ha)
  filter_upwards [ht,eventually_threshold_bound hB hc] with j hj hx
  rw [freshSum_law]
  apply hj _ (blockLength_pos hB j) _ _ hx.1 hx.2
  rw [log_blockLength hB]
  ring_nf
  rfl

theorem ae_frequent_freshSum_large {B : ℕ} (hB : 1<B) {c : ℝ} (hc : 0<c)
    (hp : c^2*(B:ℝ)/((B:ℝ)-1)<1) :
    ∀ᵐ ω ∂P, ∃ᶠ j in atTop, threshold B c j<freshSum B j ω := by
  let E := fun j => {ω | threshold B c j<freshSum B j ω}
  have hm : ∀ j, MeasurableSet (E j) := fun j => measurableSet_lt measurable_const (measurable_freshSum B j)
  have hd : ∑' j, P (E j)=⊤ := by
    apply Erdos524.FactorialSparseMesh.tsum_eq_top_of_eventual_harmonic
    filter_upwards [eventual_freshSum_probability hB hc hp] with j hj
    exact (ENNReal.ofReal_le_iff_le_toReal (by finiteness : P (E j)≠⊤)).mpr hj
  exact Erdos524.EnvelopeBlocking.ae_frequently_of_independent hm (freshSum_events_independent hB _) hd

end Erdos524.GeometricWalkProbability
