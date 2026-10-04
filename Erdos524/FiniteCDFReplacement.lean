import Erdos524.FiniteLindeberg
import Erdos524.SmoothedCDFSandwich

namespace Erdos524.FiniteCDFReplacement
open MeasureTheory ProbabilityTheory
open Erdos524.LinearStatistic Erdos524.SignGaussianMoments Erdos524.SmoothedCDFSandwich
open Erdos524.FiniteLindeberg Erdos524.SmoothCutoff

theorem finite_cdf_replacement {n d : ℕ} (hd : 0<d)
    {b η C : ℝ} (hb : 1≤b) (hη : 0<η) (hC : 0≤C) (hlog : Real.log d≤b)
    (hcut : ∀ j : Fin 4, ∀ z : ℝ, ‖iteratedDeriv (j.val+1) cutoff z‖≤C)
    (r : ℝ) (c : Fin (n+1) → Fin d → ℝ) (a : Fin (n+1) → ℝ)
    (ha : ∀ i, 0≤a i) (hc : ∀ i j, |c i j|≤a i) :
    let μ := Measure.pi (fun _ : Fin (n+1) => signLaw)
    let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
    let E := ((75/6:ℝ)*C*b^3/η^4)*(∑ i, (a i)^4)
    ν.real (coordBox c (r-2*η))-E≤μ.real (coordBox c r) ∧
      μ.real (coordBox c r)≤ν.real (coordBox c (r+2*η))+E := by
  dsimp only
  have hb' : 0<b := by linarith
  have hminus := finite_sign_gaussian_replacement hd hb hη hC hcut (r-η) c a ha hc
  have hplus := finite_sign_gaussian_replacement hd hb hη hC hcut (r+η) c a ha hc
  have hsm := smoothStatistic_integral_sandwich hd hb' hη hlog c
    (Measure.pi (fun _ : Fin (n+1) => signLaw)) (r := r-η)
  have hgm := smoothStatistic_integral_sandwich hd hb' hη hlog c
    (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) (r := r-η)
  have hsp := smoothStatistic_integral_sandwich hd hb' hη hlog c
    (Measure.pi (fun _ : Fin (n+1) => signLaw)) (r := r+η)
  have hgp := smoothStatistic_integral_sandwich hd hb' hη hlog c
    (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) (r := r+η)
  have he1 : r-η+η=r := by ring
  have he2 : r-η-η=r-2*η := by ring
  have he3 : r+η-η=r := by ring
  have he4 : r+η+η=r+2*η := by ring
  rw [he1] at hsm
  rw [he2] at hgm
  rw [he3] at hsp
  rw [he4] at hgp
  have hm := (abs_le.mp hminus).1
  have hp := (abs_le.mp hplus).2
  constructor <;> linarith [hsm.2,hgm.1,hsp.1,hgp.2]

end Erdos524.FiniteCDFReplacement
