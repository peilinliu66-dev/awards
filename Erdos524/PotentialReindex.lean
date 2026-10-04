import Erdos524.RegressionWeightBounds

namespace Erdos524.RegressionWeightBounds
open scoped BigOperators
open Erdos524.CauchyKernel

variable {n m : ℕ}

theorem omittedPotential_eq_sum_sub (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    omittedPotential s i t = (∑ j, logTanhPotential |t - s j|) - logTanhPotential |t - s i| :=
  Finset.sum_erase_eq_sub (Finset.mem_univ i)

theorem omittedPotential_equiv (s : Fin n → ℝ) (e : Fin m ≃ Fin n) (i : Fin m) (t : ℝ) :
    omittedPotential (fun j ↦ s (e j)) i t = omittedPotential s (e i) t := by
  rw [omittedPotential_eq_sum_sub, omittedPotential_eq_sum_sub,
    e.sum_comp (fun j ↦ logTanhPotential |t - s j|)]

theorem sum_own_potential_equiv (s : Fin n → ℝ) (e : Fin m ≃ Fin n) :
    (∑ i, omittedPotential (fun j ↦ s (e j)) i (s (e i))) =
      ∑ i, omittedPotential s i (s i) := by
  simp_rw [omittedPotential_equiv]
  exact e.sum_comp (fun i ↦ omittedPotential s i (s i))

end Erdos524.RegressionWeightBounds
