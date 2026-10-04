import Erdos524.PhaseSignComparison

namespace Erdos524.TwoSidedFiniteComparison
open MeasureTheory ProbabilityTheory Matrix
open Erdos524.PhaseSignComparison Erdos524.PhaseGaussianComparison
open Erdos524.TwoSidedLaplaceKernels Erdos524.TwoColorKernel Erdos524.GramGaussianCoupling
open Erdos524.TwoSidedGaussianLimit Erdos524.LaplaceKernelComparison Erdos524.SmoothCutoff

theorem phase_sign_kernel_comparison {M d : ℕ} (hM : 0<M) (hd : 0<d)
    {b η C : ℝ} (hb : 1≤b) (hη : 0<η) (hC : 0≤C) (hlog : Real.log (d+d)≤b)
    (hcut : ∀ j : Fin 4, ∀ z : ℝ, ‖iteratedDeriv (j.val+1) cutoff z‖≤C)
    (r : ℝ) (σ u : Fin d → ℝ) (hσ : ∀ j, (σ j)^2=1) (hu : ∀ j, 0≤u j) :
    let E := ((75/6:ℝ)*C*b^3)/(η^4*(2*(M:ℝ)))+(∑ j, (u j)^2)/((M:ℝ)^2*η^2)
    gramBoxProbability (fun j => exactPair (σ j) (u j)) colorMeasure (r-3*η)-E≤phaseSignBox M σ u r ∧
      phaseSignBox M σ u r≤gramBoxProbability (fun j => exactPair (σ j) (u j)) colorMeasure (r+3*η)+E := by
  dsimp only
  have hs := phase_sign_gaussian_comparison hM hd hb hη hC hlog hcut r σ u hσ hu
  have hl := phaseGaussianBox_lower hM σ u hσ hu hη (r-2*η)
  have hr := phaseGaussianBox_upper hM σ u hσ hu hη (r+2*η)
  have he1 : r-2*η-η=r-3*η := by ring
  have he2 : r+2*η+η=r+3*η := by ring
  rw [he1] at hl
  rw [he2] at hr
  dsimp only at hs
  constructor <;> linarith [hs.1,hs.2]

noncomputable def phases (d : ℕ) : Fin (d+d) → ℝ := Fin.addCases (fun _ => 1) (fun _ => -1)
noncomputable def doubleParameters {d : ℕ} (u : Fin d → ℝ) : Fin (d+d) → ℝ := Fin.addCases u u

theorem two_sided_sign_kernel_comparison {M d : ℕ} (hM : 0<M) (hd : 0<d)
    {b η C : ℝ} (hb : 1≤b) (hη : 0<η) (hC : 0≤C) (hlog : Real.log ((d+d)+(d+d))≤b)
    (hcut : ∀ j : Fin 4, ∀ z : ℝ, ‖iteratedDeriv (j.val+1) cutoff z‖≤C)
    (r : ℝ) (u : Fin d → ℝ) (hu : ∀ j, 0≤u j) :
    let E := ((75/6:ℝ)*C*b^3)/(η^4*(2*(M:ℝ)))+2*(∑ j, (u j)^2)/((M:ℝ)^2*η^2)
    (gramBoxProbability (fun j => laplace (u j)) intervalMeasure (r-3*η))^2-E≤phaseSignBox M (phases d) (doubleParameters u) r ∧
      phaseSignBox M (phases d) (doubleParameters u) r≤(gramBoxProbability (fun j => laplace (u j)) intervalMeasure (r+3*η))^2+E := by
  have hp : ∀ j, (phases d j)^2=1 := by
    intro j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;> simp only [phases,Fin.addCases_left,Fin.addCases_right] <;> norm_num
  have hu' : ∀ j, 0≤doubleParameters u j := by
    intro j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;> simpa only [doubleParameters,Fin.addCases_left,Fin.addCases_right] using hu k
  have h := phase_sign_kernel_comparison hM (by omega : 0<d+d) hb hη hC
    (by simpa only [Nat.cast_add] using hlog) hcut r (phases d) (doubleParameters u) hp hu'
  have he : (fun j => exactPair (phases d j) (doubleParameters u j))=exactFamily u := by
    funext j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;> simp only [phases,doubleParameters,exactFamily,Fin.addCases_left,Fin.addCases_right]
  have hsum : (∑ j, (doubleParameters u j)^2)=2*∑ j, (u j)^2 := by
    rw [Fin.sum_univ_add]
    simp only [doubleParameters,Fin.addCases_left,Fin.addCases_right]
    ring
  dsimp only at h ⊢
  rw [he,hsum,exactFamily_box_square u hu,exactFamily_box_square u hu] at h
  exact h

end Erdos524.TwoSidedFiniteComparison
