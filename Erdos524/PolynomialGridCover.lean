import Erdos524.UniformPolynomialTail

namespace Erdos524.PolynomialGridCover
open MeasureTheory Set
open Erdos524.PolynomialLaplaceGrid Erdos524.PhasePolynomialIdentity
open Erdos524.PolynomialTailScale Erdos524.UniformPolynomialTail

noncomputable def gridCount (N : ℕ) (T : ℝ) : ℕ := ⌈T*(N:ℝ)⌉₊+1
noncomputable def gridParameter (N : ℕ) (T : ℝ) (j : Fin (gridCount N T)) : ℝ := (j:ℝ)/(N:ℝ)

theorem normalizedPolynomial_exp {N : ℕ} (z : Fin N → ℝ) (u : ℝ) :
    normalizedPolynomial N z (Real.exp (-u/(N:ℝ)))=normalizedLaplace N z u := by
  unfold normalizedPolynomial normalizedLaplace
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Real.exp_nat_mul]
  congr 2
  ring

theorem normalizedPolynomial_neg {N : ℕ} (z : Fin N → ℝ) (x : ℝ) :
    normalizedPolynomial N z (-x)=normalizedPolynomial N (alternatingVector z) x := by
  change Erdos524.FinitePolynomialAbel.finitePolynomial z (-x)/Real.sqrt N=
    Erdos524.FinitePolynomialAbel.finitePolynomial (alternatingVector z) x/Real.sqrt N
  rw [finitePolynomial_neg_argument]

theorem parameter_of_positive_point {N : ℕ} (hN : 0<N) {T x : ℝ} (hx : 0<x) (hx1 : x≤1)
    (hxa : tailRadius N T≤x) :
    ∃ u : ℝ, 0≤u ∧ u≤T ∧ Real.exp (-u/(N:ℝ))=x := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  refine ⟨-(N:ℝ)*Real.log x,?_,?_,?_⟩
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (Real.log_nonpos hx.le hx1)
  · have hh := Real.log_le_log (Real.exp_pos (-T/(N:ℝ))) hxa
    rw [Real.log_exp] at hh
    have ht : -T≤Real.log x*(N:ℝ) := (div_le_iff₀ hNp).mp hh
    nlinarith
  · have he : -(-(N:ℝ)*Real.log x)/(N:ℝ)=Real.log x := by field_simp
    rw [he,Real.exp_log hx]

theorem grid_covers_core {N : ℕ} (hN : 0<N) (z : Fin N → ℝ) (hz : ∀ i, |z i|≤1)
    {T r x : ℝ} (hx : 0<x) (hx1 : x≤1) (hxa : tailRadius N T≤x)
    (hgrid : ∀ j : Fin (gridCount N T), |normalizedPolynomial N z (Real.exp (-gridParameter N T j/(N:ℝ)))|≤r) :
    |normalizedPolynomial N z x|≤r+1/Real.sqrt (N:ℝ) := by
  obtain ⟨u,hu,huT,hux⟩ := parameter_of_positive_point hN hx hx1 hxa
  obtain ⟨j,hj,hj0,hju⟩ := exists_grid_point hN hu huT
  let i : Fin (gridCount N T) := ⟨j,by unfold gridCount; omega⟩
  have hdist := normalizedLaplace_grid_error hN z hz hu hj0 (by rwa [abs_sub_comm])
  have hg := hgrid i
  rw [normalizedPolynomial_exp] at hg
  rw [← hux,normalizedPolynomial_exp]
  have htri := abs_add_le (normalizedLaplace N z u-normalizedLaplace N z ((j:ℝ)/(N:ℝ)))
    (normalizedLaplace N z ((j:ℝ)/(N:ℝ)))
  rw [sub_add_cancel] at htri
  rw [abs_sub_comm] at hdist
  exact htri.trans (by change _≤r+_; dsimp only [gridParameter,i] at hg; linarith)

end Erdos524.PolynomialGridCover
