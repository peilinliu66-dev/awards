import Erdos524.PolynomialAbel
import Erdos524.SignWalkMaximalMoment

namespace Erdos524.FinitePolynomialAbel
open Erdos524.PolynomialAbel Erdos524.FiniteSignWalk

noncomputable def finitePolynomial {N : ℕ} (z : Fin N → ℝ) (x : ℝ) : ℝ := ∑ i, z i*x^(i.val+1)
noncomputable def extendCoefficients {N : ℕ} (z : Fin N → ℝ) (i : ℕ) : ℝ := if h : i<N then z ⟨i,h⟩ else 0

theorem sum_range_indicator {N k : ℕ} (hk : k≤N) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, if i<k then f i else 0)=∑ i ∈ Finset.range k, f i := by
  calc
    _ = ∑ i ∈ Finset.range k, if i<k then f i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hk)
      intro i hi hik
      simp only [Finset.mem_range] at hik
      simp [hik]
    _ = _ := Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))

theorem extend_partialSum {N : ℕ} (z : Fin N → ℝ) {k : ℕ} (hk : k≤N) :
    partialSum (extendCoefficients z) k=walkPrefix z k := by
  let f : ℕ → ℝ := fun i => if i<k then extendCoefficients z i else 0
  have he : walkPrefix z k=∑ i : Fin N, f i.val := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [f,extendCoefficients,dif_pos i.isLt]
  rw [he,Fin.sum_univ_eq_sum_range f]
  exact (sum_range_indicator hk (extendCoefficients z)).symm

theorem extend_polynomial {N : ℕ} (z : Fin N → ℝ) (x : ℝ) :
    polynomial (extendCoefficients z) N x=finitePolynomial z x := by
  have h := Fin.sum_univ_eq_sum_range (fun i => extendCoefficients z i*x^(i+1)) N
  simp only [extendCoefficients,dif_pos (show ∀ i : Fin N, i.val<N from fun i => i.isLt)] at h
  symm
  calc
    _ = ∑ i : Fin N, extendCoefficients z i.val*x^(i.val+1) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [extendCoefficients,dif_pos i.isLt]
    _ = _ := h

theorem finitePolynomial_abs_le_walkMax {N : ℕ} (z : Fin N → ℝ) {x : ℝ} (hx : 0≤x) (hx1 : x≤1) :
    |finitePolynomial z x|≤walkMax z := by
  rw [← extend_polynomial]
  apply polynomial_abs_le (extendCoefficients z) N hx hx1 (norm_nonneg _)
  intro k hk
  rw [extend_partialSum z hk]
  exact norm_le_pi_norm (fun k : Fin (N+1) => walkPrefix z k.val) ⟨k,by omega⟩

theorem finitePolynomial_split {n m : ℕ} (z : Fin (n+m) → ℝ) (x : ℝ) :
    finitePolynomial z x=finitePolynomial (fun i => z (Fin.castAdd m i)) x+
      x^n*finitePolynomial (fun i => z (Fin.natAdd n i)) x := by
  unfold finitePolynomial
  rw [Fin.sum_univ_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.val_natAdd]
  rw [show n+i.val+1=n+(i.val+1) by omega,pow_add]
  ring

end Erdos524.FinitePolynomialAbel
