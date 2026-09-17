import Mathlib

/-!
An auxiliary module for JSP-000698 / Erdős 842.

This module proves the algebraic bridge from a nonzero central coefficient to
a proper three-colouring. It does not itself prove the central-coefficient
parity theorem or claim to solve the original graph problem.
-/

namespace JSP698

open Finset MvPolynomial

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]

def exponentTwo (V : Type*) [Fintype V] : V →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 2)

@[simp] theorem exponentTwo_apply (v : V) : exponentTwo V v = 2 := by
  simp [exponentTwo]

@[simp] theorem exponentTwo_degree : (exponentTwo V).degree = 2 * Fintype.card V := by
  simp [Finsupp.degree_eq_sum, Nat.mul_comm]

def edgePolynomial (left right : E → V) : MvPolynomial V ℤ :=
  ∏ e, (X (left e) - X (right e))

theorem edgePolynomial_totalDegree_le (left right : E → V) :
    (edgePolynomial left right).totalDegree ≤ Fintype.card E := by
  classical
  calc
    (edgePolynomial left right).totalDegree
        ≤ ∑ e : E, (X (left e) - X (right e) : MvPolynomial V ℤ).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ ∑ _e : E, 1 := by
      apply Finset.sum_le_sum
      intro e _
      exact (totalDegree_sub _ _).trans (by simp)
    _ = Fintype.card E := by simp

theorem threeIntegerColours_of_centralCoeff_ne_zero
    (left right : E → V)
    (hcount : Fintype.card E ≤ 2 * Fintype.card V)
    (hcoeff : (edgePolynomial left right).coeff (exponentTwo V) ≠ 0) :
    ∃ c : V → ℤ, (∀ v, c v ∈ ({0, 1, 2} : Finset ℤ)) ∧
      ∀ e, c (left e) ≠ c (right e) := by
  classical
  have hlower : (exponentTwo V).degree ≤ (edgePolynomial left right).totalDegree := by
    simpa [Finsupp.degree_apply, Finsupp.sum] using
      (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff))
  have hdegree : (edgePolynomial left right).totalDegree = (exponentTwo V).degree := by
    apply Nat.le_antisymm
    · simpa only [exponentTwo_degree] using
        (edgePolynomial_totalDegree_le left right).trans hcount
    · exact hlower
  obtain ⟨c, hc, hnonzero⟩ :=
    MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero
      (edgePolynomial left right) (exponentTwo V) hcoeff hdegree
      (fun _ => ({0, 1, 2} : Finset ℤ)) (by intro v; norm_num)
  refine ⟨c, hc, ?_⟩
  intro e heq
  apply hnonzero
  simp only [edgePolynomial, map_prod, eval_sub, eval_X]
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  exact sub_eq_zero.mpr heq

theorem threeColours_of_centralCoeff_ne_zero
    (left right : E → V)
    (hcount : Fintype.card E ≤ 2 * Fintype.card V)
    (hcoeff : (edgePolynomial left right).coeff (exponentTwo V) ≠ 0) :
    ∃ c : V → Fin 3, ∀ e, c (left e) ≠ c (right e) := by
  classical
  obtain ⟨c, hc, hedge⟩ := threeIntegerColours_of_centralCoeff_ne_zero
    left right hcount hcoeff
  have hrange (v : V) : 0 ≤ c v ∧ c v < 3 := by
    have hv := hc v
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h | h <;> omega
  let d : V → Fin 3 := fun v => ⟨(c v).toNat, by
    have := hrange v
    omega⟩
  refine ⟨d, ?_⟩
  intro e heq
  apply hedge e
  have hnat := congrArg Fin.val heq
  dsimp [d] at hnat
  have := hrange (left e)
  have := hrange (right e)
  omega

theorem threeColours_of_centralCoeff_mod_four
    (left right : E → V)
    (hcount : Fintype.card E ≤ 2 * Fintype.card V)
    (hcoeff : (edgePolynomial left right).coeff (exponentTwo V) % 4 = 2) :
    ∃ c : V → Fin 3, ∀ e, c (left e) ≠ c (right e) := by
  apply threeColours_of_centralCoeff_ne_zero left right hcount
  omega

#print axioms threeColours_of_centralCoeff_ne_zero
#print axioms threeColours_of_centralCoeff_mod_four

end

end JSP698
