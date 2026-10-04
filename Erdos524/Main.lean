import Erdos524.LogarithmicLiminf
import Erdos524.ConstantTermUpperEnvelope

/-!
# Erdős problem 524: the full lower and upper envelopes

On the actual product probability space of independent uniform signs, let
`littlewoodMaximum ω N` be the supremum norm on `[-1,1]` of
`∑ i in range (N+1), ω i * x^i`, including the independent constant term.

The original logarithmic lower envelope and the sharp upper envelope are
proved together in `erdos_524`. The stronger inverse-small-ball normalization
is stated separately in `erdos_524_inverse_refinement`. Its distribution `F`
is the explicitly defined infimum of finite Gaussian Laplace-covariance box
probabilities. No identification with an Itô-integral process is assumed.

Proof-source credit: Letwin–Sawhney, arXiv:2604.19294v1, Theorem 1.1;
the upper envelope is attributed there to Salem–Zygmund. This is a formal
recovery of known mathematics, not a claim of a new analytic result.
-/

namespace Erdos524

open Set Filter MeasureTheory
open Erdos524.RandomPolynomialModel Erdos524.FiniteSmallBallInverse

noncomputable def littlewoodPolynomial (ω : Ω) (N : ℕ) : C(Interval, ℝ) :=
  ⟨fun x ↦ ∑ i ∈ Finset.range (N + 1), ω i * (x : ℝ) ^ i, by fun_prop⟩

noncomputable def littlewoodMaximum (ω : Ω) (N : ℕ) : ℝ := ‖littlewoodPolynomial ω N‖

theorem littlewoodPolynomial_eq_withConstant (ω : Ω) (N : ℕ) :
    littlewoodPolynomial ω N = withConstantPolyCM ω N := by
  ext x
  exact (withConstantPolyCM_sum_range ω N x).symm

theorem littlewoodMaximum_eq_withConstantNorm (ω : Ω) (N : ℕ) :
    littlewoodMaximum ω N = withConstantNorm ω N := congrArg norm (littlewoodPolynomial_eq_withConstant ω N)

/-- The full original lower and upper envelopes for the constant-term polynomial. -/
theorem erdos_524 :
    ∀ᵐ ω ∂P,
      (liminf (fun N : ℕ ↦ Real.log (littlewoodMaximum ω N / Real.sqrt (N : ℝ)) /
        (Real.log (Real.log (N : ℝ))) ^ (1 / 3 : ℝ)) atTop =
          -(3 * Real.pi ^ 2 / 4) ^ (1 / 3 : ℝ)) ∧
      (limsup (fun N : ℕ ↦ littlewoodMaximum ω N /
        Real.sqrt ((N : ℝ) * Real.log (Real.log (N : ℝ)))) atTop = Real.sqrt 2) := by
  filter_upwards [LogarithmicLiminf.ae_constant_logarithmic_liminf,
    ConstantTermUpperEnvelope.ae_constant_explicit_upper_limsup_sqrt_two] with ω hl hu
  simpa only [littlewoodMaximum_eq_withConstantNorm] using And.intro hl hu

/-- Stronger inverse normalization, using the explicitly formalized finite Gaussian envelope. -/
theorem erdos_524_inverse_refinement :
    ∀ᵐ ω ∂P,
      liminf (fun N : ℕ ↦ littlewoodMaximum ω N /
        (Real.sqrt (N : ℝ) * smallBallInverse ((Real.sqrt (Real.log (N : ℝ)))⁻¹))) atTop = 1 := by
  filter_upwards [ConstantTermInverseLiminf.ae_constant_explicit_inverse_liminf_eq_one] with ω hω
  simpa only [littlewoodMaximum_eq_withConstantNorm] using hω

/-- Both original endpoints and the stronger finite-envelope inverse refinement, jointly almost surely. -/
theorem erdos_524_complete :
    ∀ᵐ ω ∂P,
      (liminf (fun N : ℕ ↦ littlewoodMaximum ω N /
        (Real.sqrt (N : ℝ) * smallBallInverse ((Real.sqrt (Real.log (N : ℝ)))⁻¹))) atTop = 1) ∧
      (liminf (fun N : ℕ ↦ Real.log (littlewoodMaximum ω N / Real.sqrt (N : ℝ)) /
        (Real.log (Real.log (N : ℝ))) ^ (1 / 3 : ℝ)) atTop =
          -(3 * Real.pi ^ 2 / 4) ^ (1 / 3 : ℝ)) ∧
      (limsup (fun N : ℕ ↦ littlewoodMaximum ω N /
        Real.sqrt ((N : ℝ) * Real.log (Real.log (N : ℝ)))) atTop = Real.sqrt 2) := by
  filter_upwards [erdos_524, erdos_524_inverse_refinement] with ω h h'
  exact ⟨h', h⟩

end Erdos524
