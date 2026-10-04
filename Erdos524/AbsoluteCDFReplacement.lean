import Erdos524.FiniteCDFReplacement

namespace Erdos524.AbsoluteCDFReplacement
open MeasureTheory ProbabilityTheory
open Erdos524.LinearStatistic Erdos524.SignGaussianMoments Erdos524.SmoothedCDFSandwich
open Erdos524.FiniteCDFReplacement Erdos524.SmoothCutoff

noncomputable def signedCoefficients {N d : ℕ} (c : Fin N → Fin d → ℝ) : Fin N → Fin (d+d) → ℝ :=
  fun i => Fin.addCases (c i) (fun j => -c i j)

noncomputable def absoluteBox {N d : ℕ} (c : Fin N → Fin d → ℝ) (r : ℝ) : Set (Fin N → ℝ) :=
  {z | ∀ j, |linearStatistic c z j|≤r}

theorem coordBox_signed_eq {N d : ℕ} (c : Fin N → Fin d → ℝ) (r : ℝ) :
    coordBox (signedCoefficients c) r=absoluteBox c r := by
  ext z
  constructor
  · intro hz j
    have hp := hz (Fin.castAdd d j)
    have hn := hz (Fin.natAdd d j)
    simp only [linearStatistic,signedCoefficients,Fin.addCases_left] at hp
    simp only [linearStatistic,signedCoefficients,Fin.addCases_right,mul_neg,Finset.sum_neg_distrib] at hn
    change |∑ x, z x*c x j|≤r
    exact abs_le.mpr ⟨by linarith,hp⟩
  · intro hz j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [linearStatistic,signedCoefficients,Fin.addCases_left] using (abs_le.mp (hz k)).2
    · simp only [linearStatistic,signedCoefficients,Fin.addCases_right,mul_neg,Finset.sum_neg_distrib]
      have h := (abs_le.mp (hz k)).1
      unfold linearStatistic at h
      linarith

theorem absolute_cdf_replacement {n d : ℕ} (hd : 0<d)
    {b η C : ℝ} (hb : 1≤b) (hη : 0<η) (hC : 0≤C) (hlog : Real.log (d+d)≤b)
    (hcut : ∀ j : Fin 4, ∀ z : ℝ, ‖iteratedDeriv (j.val+1) cutoff z‖≤C)
    (r : ℝ) (c : Fin (n+1) → Fin d → ℝ) (a : Fin (n+1) → ℝ)
    (ha : ∀ i, 0≤a i) (hc : ∀ i j, |c i j|≤a i) :
    let μ := Measure.pi (fun _ : Fin (n+1) => signLaw)
    let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
    let E := ((75/6:ℝ)*C*b^3/η^4)*(∑ i, (a i)^4)
    ν.real (absoluteBox c (r-2*η))-E≤μ.real (absoluteBox c r) ∧
      μ.real (absoluteBox c r)≤ν.real (absoluteBox c (r+2*η))+E := by
  have hs : ∀ i j, |signedCoefficients c i j|≤a i := by
    intro i j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [signedCoefficients,Fin.addCases_left,Fin.addCases_right,abs_neg] using hc i k
    · simpa only [signedCoefficients,Fin.addCases_left,Fin.addCases_right,abs_neg] using hc i k
  have h := finite_cdf_replacement (by omega : 0<d+d) hb hη hC
    (by simpa only [Nat.cast_add] using hlog) hcut r (signedCoefficients c) a ha hs
  simpa only [coordBox_signed_eq] using h

end Erdos524.AbsoluteCDFReplacement
