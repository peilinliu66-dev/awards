import Erdos524.PhaseGaussianComparison
import Erdos524.PolynomialFiniteComparison

namespace Erdos524.PhaseSignComparison
open MeasureTheory ProbabilityTheory Matrix
open Erdos524.TwoSidedGaussianPolynomialLaw Erdos524.PhaseGaussianComparison
open Erdos524.SignGaussianMoments Erdos524.SmoothCutoff Erdos524.AbsoluteCDFReplacement
open Erdos524.LinearStatistic Erdos524.PolynomialFiniteComparison

noncomputable def phaseSignBox (M : ℕ) {d : ℕ} (σ u : Fin d → ℝ) (r : ℝ) : ℝ :=
  (Measure.pi (fun _ : Fin (2*M) => signLaw)).real {z | ∀ j, |(phaseMatrix σ u*ᵥz) j|≤r}

theorem phaseMatrix_bound {M d : ℕ} (hM : 0<M) (σ u : Fin d → ℝ)
    (hσ : ∀ j, (σ j)^2=1) (hu : ∀ j, 0≤u j) (i : Fin (2*M)) (j : Fin d) :
    |phaseMatrix σ u j i|≤1/Real.sqrt ((2*M:ℕ):ℝ) := by
  have habs : |σ j|=1 := by nlinarith [sq_abs (σ j),hσ j,abs_nonneg (σ j)]
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  have hexp : Real.exp (-u j*((i.val+1:ℕ):ℝ)/(2*(M:ℝ)))≤1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hu j)) (by positivity)
  simp only [phaseMatrix,abs_div,abs_mul,abs_pow,habs,one_pow,one_mul,abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.sqrt_nonneg _),Nat.cast_mul,Nat.cast_ofNat]
  exact div_le_div_of_nonneg_right hexp (Real.sqrt_nonneg _)

theorem absolute_cdf_replacement_positive {N d : ℕ} (hN : 0<N) (hd : 0<d)
    {b η C : ℝ} (hb : 1≤b) (hη : 0<η) (hC : 0≤C) (hlog : Real.log (d+d)≤b)
    (hcut : ∀ j : Fin 4, ∀ z : ℝ, ‖iteratedDeriv (j.val+1) cutoff z‖≤C)
    (r : ℝ) (c : Fin N → Fin d → ℝ) (a : Fin N → ℝ)
    (ha : ∀ i, 0≤a i) (hc : ∀ i j, |c i j|≤a i) :
    let μ := Measure.pi (fun _ : Fin N => signLaw)
    let ν := Measure.pi (fun _ : Fin N => gaussianReal 0 1)
    let E := ((75/6:ℝ)*C*b^3/η^4)*(∑ i, (a i)^4)
    ν.real (absoluteBox c (r-2*η))-E≤μ.real (absoluteBox c r) ∧
      μ.real (absoluteBox c r)≤ν.real (absoluteBox c (r+2*η))+E := by
  cases N with
  | zero => omega
  | succ n => exact absolute_cdf_replacement hd hb hη hC hlog hcut r c a ha hc

theorem phase_sign_gaussian_comparison {M d : ℕ} (hM : 0<M) (hd : 0<d)
    {b η C : ℝ} (hb : 1≤b) (hη : 0<η) (hC : 0≤C) (hlog : Real.log (d+d)≤b)
    (hcut : ∀ j : Fin 4, ∀ z : ℝ, ‖iteratedDeriv (j.val+1) cutoff z‖≤C)
    (r : ℝ) (σ u : Fin d → ℝ) (hσ : ∀ j, (σ j)^2=1) (hu : ∀ j, 0≤u j) :
    let E := ((75/6:ℝ)*C*b^3)/(η^4*(2*(M:ℝ)))
    phaseGaussianBox M σ u (r-2*η)-E≤phaseSignBox M σ u r ∧
      phaseSignBox M σ u r≤phaseGaussianBox M σ u (r+2*η)+E := by
  let c : Fin (2*M) → Fin d → ℝ := fun i j => phaseMatrix σ u j i
  have hN : 0<2*M := by omega
  have h := absolute_cdf_replacement_positive hN hd hb hη hC hlog hcut r c
    (fun _ => 1/Real.sqrt ((2*M:ℕ):ℝ)) (by intro i; positivity) (phaseMatrix_bound hM σ u hσ hu)
  rw [constant_fourth_sum hN] at h
  have he (q : ℝ) : absoluteBox c q={z | ∀ j, |(phaseMatrix σ u*ᵥz) j|≤q} := by
    ext z
    simp only [absoluteBox,linearStatistic,c,Matrix.mulVec,dotProduct,mul_comm]
  simp_rw [he] at h
  have hE : ((75/6:ℝ)*C*b^3/η^4)*(1/((2*M:ℕ):ℝ))=((75/6:ℝ)*C*b^3)/(η^4*(2*(M:ℝ))) := by push_cast; field_simp
  rw [hE] at h
  exact h

end Erdos524.PhaseSignComparison
