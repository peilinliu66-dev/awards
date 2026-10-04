import Erdos524.GaussianGridEnvelope

namespace Erdos524.PolynomialFullUpper
open MeasureTheory ProbabilityTheory Set
open Erdos524.FullPolynomialBox Erdos524.PolynomialGridCover Erdos524.PhasePolynomialIdentity
open Erdos524.PolynomialFullProbability Erdos524.SignGaussianMoments Erdos524.TwoSidedFiniteComparison
open Erdos524.GaussianGridEnvelope Erdos524.GaussianGridOscillation Erdos524.GaussianGridProbability
open Erdos524.FiniteSmallBallBasic Erdos524.GramGaussianCoupling Erdos524.LaplaceKernelComparison

theorem fullBox_subset_gridBox (N : ℕ) (T r : ℝ) : fullBox N r⊆gridBox N T r := by
  intro z hz
  have he (j : Fin (gridCount N T)) : |Real.exp (-gridParameter N T j/(N:ℝ))|≤1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · apply neg_nonpos.mpr
      unfold gridParameter
      positivity
    · positivity
  constructor
  · intro j
    exact hz _ (he j)
  · intro j
    apply hz
    simpa only [abs_neg] using he j

theorem full_polynomial_probability_upper {M : ℕ} (hM : 0<M) {T η r b C : ℝ}
    (hη : 0<η) (hr : 0<r+4*η) (hb : 1≤b) (hC : 0≤C)
    (hlog : Real.log ((gridCount (2*M) T+gridCount (2*M) T)+(gridCount (2*M) T+gridCount (2*M) T))≤b)
    (hcut : ∀ j : Fin 4, ∀ z : ℝ, ‖iteratedDeriv (j.val+1) Erdos524.SmoothCutoff.cutoff z‖≤C) :
    (Measure.pi (fun _ : Fin (2*M) => signLaw)).real (fullBox (2*M) r)≤
      (smallBallReal (r+4*η))^2+
      (((75/6:ℝ)*C*b^3)/(η^4*(2*(M:ℝ)))+
        2*(∑ j : Fin (gridCount (2*M) T), (gridParameter (2*M) T j)^2)/((M:ℝ)^2*η^2))+
      2*(Real.sqrt (2*(Real.exp 1)^2/((2*M:ℕ):ℝ))/η+
        Real.exp 1/((r+4*η)*Real.sqrt ((⌈T*((2*M:ℕ):ℝ)⌉₊:ℝ)/((2*M:ℕ):ℝ)+1))) := by
  have hN : 0<2*M := by omega
  have hNp : (0:ℝ)<((2*M:ℕ):ℝ) := by exact_mod_cast hN
  have hu : ∀ j : Fin (gridCount (2*M) T), 0≤gridParameter (2*M) T j := by intro j; unfold gridParameter; positivity
  have hdim : 0<gridCount (2*M) T := by unfold gridCount; omega
  have hc := two_sided_sign_kernel_comparison hM hdim hb hη hC hlog hcut r (gridParameter (2*M) T) hu
  dsimp only at hc
  rw [gridBox_phase_eq] at hc
  have hf := measureReal_mono (μ := Measure.pi (fun _ : Fin (2*M) => signLaw)) (fullBox_subset_gridBox (2*M) T r)
  have hG := grid_probability_sq_le_envelope ⌈T*((2*M:ℕ):ℝ)⌉₊ (h := 1/((2*M:ℕ):ℝ)) (by positivity) hη
    (r := r+3*η) (by linarith)
  have hefun : gridPoints ⌈T*((2*M:ℕ):ℝ)⌉₊ (1/((2*M:ℕ):ℝ))=gridParameter (2*M) T := by
    funext j
    unfold gridPoints gridParameter
    ring
  rw [hefun] at hG
  have her : r+3*η+η=r+4*η := by ring
  rw [her] at hG
  simp only [kernelProbability,mul_one_div] at hG
  calc
    _ ≤ _ := hf
    _ ≤ _ := hc.2
    _ ≤ _ := add_le_add hG le_rfl
    _ = _ := by ring

end Erdos524.PolynomialFullUpper
