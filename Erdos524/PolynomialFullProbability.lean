import Erdos524.FullPolynomialBox
import Erdos524.FiniteSmallBallBasic

namespace Erdos524.PolynomialFullProbability
open MeasureTheory ProbabilityTheory Set Filter WithLp Matrix
open Erdos524.FullPolynomialBox Erdos524.PolynomialGridCover Erdos524.PolynomialTailScale
open Erdos524.UniformPolynomialTail Erdos524.PhasePolynomialIdentity Erdos524.SignGaussianMoments
open Erdos524.SignConcentration Erdos524.PhaseSignComparison Erdos524.TwoSidedFiniteComparison
open Erdos524.TwoSidedGaussianPolynomialLaw Erdos524.GramGaussianCoupling Erdos524.LaplaceKernelComparison
open Erdos524.FiniteSmallBallEnvelope Erdos524.FiniteSmallBallBasic

theorem grid_probability_le_full_add_tail {N : ℕ} (hN : 0<N) {T η r : ℝ}
    (hT : 0<T) (hTN : T≤N) (hη : 0<η) (hηr : η≤r) :
    (Measure.pi (fun _ : Fin N => signLaw)).real (gridBox N T (r-1/Real.sqrt (N:ℝ)))≤
      (Measure.pi (fun _ : Fin N => signLaw)).real (fullBox N r)+18/(η*Real.sqrt T) := by
  let P := Measure.pi (fun _ : Fin N => signLaw)
  let B : Set (Fin N → ℝ) := {z | ∃ x : ℝ, |x|≤tailRadius N T ∧ η≤|normalizedPolynomial N z x|}
  have hs : gridBox N T (r-1/Real.sqrt (N:ℝ)) ≤ᵐ[P] (fullBox N r ∪ B) := by
    filter_upwards [sign_coordinates_bounded N] with z hz
    intro hg
    by_cases hb : z∈B
    · exact Or.inr hb
    · left
      apply fullBox_of_grid_tail hN hz hg (by linarith)
      intro x hx
      have hh : |normalizedPolynomial N z x|<η := lt_of_not_ge (fun h => hb ⟨x,hx,h⟩)
      exact hh.le.trans hηr
  have he := ENNReal.toReal_mono (show P (fullBox N r ∪ B)≠⊤ by finiteness) (measure_mono_ae hs)
  have hu := measureReal_union_le (μ := P) (fullBox N r) B
  have ht := normalized_polynomial_tail_probability hN hT hTN hη
  change P.real (gridBox N T (r-1/Real.sqrt (N:ℝ)))≤P.real (fullBox N r ∪ B) at he
  change P.real B≤18/(η*Real.sqrt T) at ht
  exact he.trans (hu.trans (add_le_add le_rfl ht))

theorem gridBox_phase_eq (M : ℕ) (T r : ℝ) :
    phaseSignBox M (phases (gridCount (2*M) T)) (doubleParameters (gridParameter (2*M) T)) r=
      (Measure.pi (fun _ : Fin (2*M) => signLaw)).real (gridBox (2*M) T r) := by
  unfold phaseSignBox
  congr 1
  ext z
  change (∀ j, |(phaseMatrix (phases (gridCount (2*M) T)) (doubleParameters (gridParameter (2*M) T))*ᵥz) j|≤r) ↔ _
  simp_rw [phaseMatrix_evaluation]
  constructor
  · intro h
    constructor
    · intro j
      have hh := h (Fin.castAdd (gridCount (2*M) T) j)
      simpa only [phases,doubleParameters,Fin.addCases_left,one_mul,Nat.cast_mul,Nat.cast_ofNat] using hh
    · intro j
      have hh := h (Fin.natAdd (gridCount (2*M) T) j)
      simpa only [phases,doubleParameters,Fin.addCases_right,neg_one_mul,Nat.cast_mul,Nat.cast_ofNat] using hh
  · intro h j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [phases,doubleParameters,Fin.addCases_left,one_mul,Nat.cast_mul,Nat.cast_ofNat] using h.1 k
    · simpa only [phases,doubleParameters,Fin.addCases_right,neg_one_mul,Nat.cast_mul,Nat.cast_ofNat] using h.2 k

theorem smallBallReal_le_gramBox {n : ℕ} (u : Fin (n+1) → ℝ) (hu : ∀ j, 0≤u j) (r : ℝ) :
    smallBallReal r≤gramBoxProbability (fun j => laplace (u j)) intervalMeasure r := by
  let v : Fin (n+1) → NNReal := fun j => ⟨u j,hu j⟩
  have h := finiteSmallBall_le_evaluation r n v
  have ht := ENNReal.toReal_mono (by finiteness) h
  change smallBallReal r≤((multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' Erdos524.GaussianBoxDensity.box (fun _ => r))).toReal at ht
  have he : (ofLp : EuclideanSpace ℝ (Fin (n+1)) → Fin (n+1) → ℝ) ⁻¹' Erdos524.GaussianBoxDensity.box (fun _ => r)=
      {z : EuclideanSpace ℝ (Fin (n+1)) | ∀ j, |z j|≤r} := by
    ext z
    simp only [Erdos524.GaussianBoxDensity.box,Set.mem_preimage,Set.mem_pi,Set.mem_univ,true_implies,Set.mem_Icc,Set.mem_setOf_eq,abs_le]
  rw [he] at ht
  exact ht

theorem full_polynomial_probability_lower {M : ℕ} (hM : 0<M) {T η r b C : ℝ}
    (hT : 0<T) (hTN : T≤(2*M:ℕ)) (hη : 0<η) (hηr : η≤r) (hb : 1≤b) (hC : 0≤C)
    (hlog : Real.log ((gridCount (2*M) T+gridCount (2*M) T)+(gridCount (2*M) T+gridCount (2*M) T))≤b)
    (hcut : ∀ j : Fin 4, ∀ z : ℝ, ‖iteratedDeriv (j.val+1) Erdos524.SmoothCutoff.cutoff z‖≤C) :
    (smallBallReal (r-1/Real.sqrt ((2*M:ℕ):ℝ)-3*η))^2-
      (((75/6:ℝ)*C*b^3)/(η^4*(2*(M:ℝ)))+
        2*(∑ j : Fin (gridCount (2*M) T), (gridParameter (2*M) T j)^2)/((M:ℝ)^2*η^2))-
      18/(η*Real.sqrt T)≤(Measure.pi (fun _ : Fin (2*M) => signLaw)).real (fullBox (2*M) r) := by
  have hu : ∀ j : Fin (gridCount (2*M) T), 0≤gridParameter (2*M) T j := by intro j; unfold gridParameter; positivity
  have hdim : 0<gridCount (2*M) T := by unfold gridCount; omega
  have hc := two_sided_sign_kernel_comparison hM hdim hb hη hC hlog hcut
    (r-1/Real.sqrt ((2*M:ℕ):ℝ)) (gridParameter (2*M) T) hu
  dsimp only at hc
  rw [gridBox_phase_eq] at hc
  have hF := smallBallReal_le_gramBox (gridParameter (2*M) T) hu
    (r-1/Real.sqrt ((2*M:ℕ):ℝ)-3*η)
  have hF0 : 0≤smallBallReal (r-1/Real.sqrt ((2*M:ℕ):ℝ)-3*η) := ENNReal.toReal_nonneg
  have hG0 : 0≤gramBoxProbability (fun j => laplace (gridParameter (2*M) T j)) intervalMeasure
      (r-1/Real.sqrt ((2*M:ℕ):ℝ)-3*η) := measureReal_nonneg
  have hsq := (sq_le_sq₀ hF0 hG0).mpr hF
  have ht := grid_probability_le_full_add_tail (by omega : 0<2*M) hT hTN hη hηr
  linarith [hc.1]

end Erdos524.PolynomialFullProbability
