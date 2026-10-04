import Erdos524.TwoSidedFiniteComparison

namespace Erdos524.PhasePolynomialIdentity
open Matrix
open Erdos524.TwoSidedGaussianPolynomialLaw

noncomputable def normalizedPolynomial (N : ℕ) (z : Fin N → ℝ) (x : ℝ) : ℝ :=
  (∑ i : Fin N, z i*x^(i.val+1))/Real.sqrt N

theorem phaseMatrix_evaluation {M d : ℕ} (σ u : Fin d → ℝ) (z : Fin (2*M) → ℝ) (j : Fin d) :
    (phaseMatrix σ u*ᵥz) j=normalizedPolynomial (2*M) z (σ j*Real.exp (-u j/(2*(M:ℝ)))) := by
  simp only [Matrix.mulVec,dotProduct,phaseMatrix,normalizedPolynomial,Nat.cast_mul,Nat.cast_ofNat]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow,← Real.exp_nat_mul]
  have he : ((i.val+1:ℕ):ℝ)*(-u j/(2*(M:ℝ)))=-u j*((i.val+1:ℕ):ℝ)/(2*(M:ℝ)) := by ring
  rw [he]
  ring

theorem phasePoint_mem_interval {M : ℕ} (hM : 0<M) {σ u : ℝ} (hσ : σ^2=1) (hu : 0≤u) :
    |σ*Real.exp (-u/(2*(M:ℝ)))|≤1 := by
  have ha : |σ|=1 := by nlinarith [sq_abs σ,abs_nonneg σ]
  rw [abs_mul,ha,one_mul,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) (by positivity)

end Erdos524.PhasePolynomialIdentity
