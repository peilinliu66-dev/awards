import Erdos524.AbsoluteCDFReplacement

namespace Erdos524.PolynomialFiniteComparison
open MeasureTheory ProbabilityTheory
open Erdos524.LinearStatistic Erdos524.SignGaussianMoments Erdos524.AbsoluteCDFReplacement
open Erdos524.SmoothCutoff

noncomputable def polynomialCoefficients (N : ℕ) {d : ℕ} (x : Fin d → ℝ) : Fin N → Fin d → ℝ :=
  fun i j => (x j)^(i.val+1)/Real.sqrt N

theorem polynomialCoefficients_bound {N d : ℕ} (hN : 0<N) (x : Fin d → ℝ)
    (hx : ∀ j, |x j|≤1) (i : Fin N) (j : Fin d) :
    |polynomialCoefficients N x i j|≤1/Real.sqrt N := by
  have hs : 0<Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  unfold polynomialCoefficients
  rw [abs_div,abs_of_pos hs,abs_pow]
  apply div_le_div_of_nonneg_right _ hs.le
  exact pow_le_one₀ (abs_nonneg _) (hx j)

theorem constant_fourth_sum {N : ℕ} (hN : 0<N) :
    (∑ _i : Fin N, (1/Real.sqrt (N:ℝ))^4)=1/(N:ℝ) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hs := Real.sq_sqrt hNp.le
  have hsn : Real.sqrt (N:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr hNp)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hp : Real.sqrt (N:ℝ)^4=(N:ℝ)^2 := by nlinarith [sq_nonneg (Real.sqrt (N:ℝ)^2-(N:ℝ))]
  rw [div_pow,one_pow,hp]
  field_simp

theorem polynomial_finite_cdf_comparison {n d : ℕ} (hd : 0<d)
    {b η C : ℝ} (hb : 1≤b) (hη : 0<η) (hC : 0≤C) (hlog : Real.log (d+d)≤b)
    (hcut : ∀ j : Fin 4, ∀ z : ℝ, ‖iteratedDeriv (j.val+1) cutoff z‖≤C)
    (r : ℝ) (x : Fin d → ℝ) (hx : ∀ j, |x j|≤1) :
    let c := polynomialCoefficients (n+1) x
    let μ := Measure.pi (fun _ : Fin (n+1) => signLaw)
    let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
    let E := ((75/6:ℝ)*C*b^3)/(η^4*(n+1))
    ν.real (absoluteBox c (r-2*η))-E≤μ.real (absoluteBox c r) ∧
      μ.real (absoluteBox c r)≤ν.real (absoluteBox c (r+2*η))+E := by
  have h := absolute_cdf_replacement hd hb hη hC hlog hcut r
    (polynomialCoefficients (n+1) x) (fun _ => 1/Real.sqrt ((n+1:ℕ):ℝ))
    (by intro i; positivity) (polynomialCoefficients_bound (N := n+1) (by omega) x hx)
  rw [constant_fourth_sum (by omega)] at h
  have he : ((75/6:ℝ)*C*b^3/η^4)*(1/(n+1))=((75/6:ℝ)*C*b^3)/(η^4*(n+1)) := by field_simp <;> ring
  simpa only [Nat.cast_add,Nat.cast_one,he] using h

end Erdos524.PolynomialFiniteComparison
