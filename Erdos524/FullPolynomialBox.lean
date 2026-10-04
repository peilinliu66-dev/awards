import Erdos524.PolynomialGridCover

namespace Erdos524.FullPolynomialBox
open MeasureTheory Set Filter
open Erdos524.PolynomialGridCover Erdos524.PolynomialTailScale Erdos524.UniformPolynomialTail
open Erdos524.PhasePolynomialIdentity Erdos524.SignGaussianMoments Erdos524.SignConcentration

noncomputable def fullBox (N : ℕ) (r : ℝ) : Set (Fin N → ℝ) :=
  {z | ∀ x : ℝ, |x|≤1 → |normalizedPolynomial N z x|≤r}
noncomputable def gridBox (N : ℕ) (T r : ℝ) : Set (Fin N → ℝ) :=
  {z | (∀ j : Fin (gridCount N T), |normalizedPolynomial N z (Real.exp (-gridParameter N T j/(N:ℝ)))|≤r) ∧
       (∀ j : Fin (gridCount N T), |normalizedPolynomial N z (-Real.exp (-gridParameter N T j/(N:ℝ)))|≤r)}

theorem fullBox_closed (N : ℕ) (r : ℝ) : IsClosed (fullBox N r) := by
  have he : fullBox N r=⋂ x : {x : ℝ // |x|≤1}, {z | |normalizedPolynomial N z x.val|≤r} := by
    ext z
    simp only [fullBox,Set.mem_setOf_eq,Set.mem_iInter,Subtype.forall]
  rw [he]
  apply isClosed_iInter
  intro x
  apply isClosed_le _ continuous_const
  unfold normalizedPolynomial
  fun_prop

theorem gridBox_closed (N : ℕ) (T r : ℝ) : IsClosed (gridBox N T r) := by
  have he : gridBox N T r=
      (⋂ j : Fin (gridCount N T), {z | |normalizedPolynomial N z (Real.exp (-gridParameter N T j/(N:ℝ)))|≤r}) ∩
      (⋂ j : Fin (gridCount N T), {z | |normalizedPolynomial N z (-Real.exp (-gridParameter N T j/(N:ℝ)))|≤r}) := by
    ext z
    simp only [gridBox,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_iInter]
  rw [he]
  apply IsClosed.inter <;> apply isClosed_iInter <;> intro j <;> apply isClosed_le _ continuous_const <;>
    unfold normalizedPolynomial <;> fun_prop

theorem sign_coordinates_bounded (N : ℕ) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => signLaw), ∀ i, |z i|≤1 := by
  apply ae_all_iff.mpr
  intro i
  have hm := measurePreserving_eval (fun _ : Fin N => signLaw) i
  have h := signLaw_ae_interval
  rw [← hm.map_eq] at h
  have hp := ae_of_ae_map hm.aemeasurable h
  filter_upwards [hp] with z hz
  exact abs_le.mpr hz

theorem fullBox_of_grid_tail {N : ℕ} (hN : 0<N) {z : Fin N → ℝ} (hz : ∀ i, |z i|≤1)
    {T q r : ℝ} (hg : z∈gridBox N T q) (hqr : q+1/Real.sqrt (N:ℝ)≤r)
    (htail : ∀ x : ℝ, |x|≤tailRadius N T → |normalizedPolynomial N z x|≤r) : z∈fullBox N r := by
  intro x hx
  by_cases hxa : |x|≤tailRadius N T
  · exact htail x hxa
  · have hrad : 0<tailRadius N T := Real.exp_pos _
    have hxabs : 0 < |x| := hrad.trans (lt_of_not_ge hxa)
    by_cases hx0 : 0≤x
    · have hxp : 0<x := by rwa [abs_of_nonneg hx0] at hxabs
      exact (grid_covers_core hN z hz hxp ((le_abs_self x).trans hx)
        (by rw [abs_of_nonneg hx0] at hxa; linarith) hg.1).trans hqr
    · have hxneg : 0 < -x := by linarith
      have hxneg1 : -x≤1 := by simpa only [abs_of_neg (lt_of_not_ge hx0)] using hx
      have hxnegrad : tailRadius N T≤-x := by
        rw [abs_of_neg (lt_of_not_ge hx0)] at hxa
        linarith
      have hzA : ∀ i, |alternatingVector z i|≤1 := by
        intro i
        simpa [alternatingVector,abs_mul,abs_pow] using hz i
      have hgridA : ∀ j : Fin (gridCount N T),
          |normalizedPolynomial N (alternatingVector z) (Real.exp (-gridParameter N T j/(N:ℝ)))|≤q := by
        intro j
        simpa only [normalizedPolynomial_neg] using hg.2 j
      have h := grid_covers_core hN (alternatingVector z) hzA hxneg hxneg1 hxnegrad hgridA
      rw [← normalizedPolynomial_neg,neg_neg] at h
      exact h.trans hqr

end Erdos524.FullPolynomialBox
