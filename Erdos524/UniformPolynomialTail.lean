import Erdos524.PolynomialTailScale
import Erdos524.PhasePolynomialIdentity
import Erdos524.SignSymmetry

namespace Erdos524.UniformPolynomialTail
open MeasureTheory ProbabilityTheory Filter
open Erdos524.PolynomialBlockTail Erdos524.PolynomialTailScale Erdos524.FinitePolynomialAbel
open Erdos524.PhasePolynomialIdentity Erdos524.SignGaussianMoments Erdos524.SignSymmetry

noncomputable def alternatingVector {N : ℕ} (z : Fin N → ℝ) : Fin N → ℝ := fun i => (-1)^(i.val+1)*z i

theorem finitePolynomial_neg_argument {N : ℕ} (z : Fin N → ℝ) (x : ℝ) :
    finitePolynomial z (-x)=finitePolynomial (alternatingVector z) x := by
  unfold finitePolynomial alternatingVector
  apply Finset.sum_congr rfl
  intro i hi
  rw [neg_eq_neg_one_mul x,mul_pow]
  ring

theorem alternatingVector_map (N : ℕ) :
    (Measure.pi (fun _ : Fin N => signLaw)).map (alternatingVector (N := N))=Measure.pi (fun _ : Fin N => signLaw) := by
  apply pi_sign_map_phases
  intro i
  rw [← pow_mul,Nat.mul_comm, pow_mul]
  norm_num

theorem exists_normalized_tail_dominator {N : ℕ} (hN : 0<N) {T : ℝ} (hT : 0<T) (hTN : T≤N) :
    ∃ W : (Fin N → ℝ) → ℝ, Measurable W ∧ Integrable W (Measure.pi (fun _ : Fin N => signLaw)) ∧
      (∀ z, 0≤W z) ∧
      (∀ z x, |x|≤tailRadius N T → |normalizedPolynomial N z x|≤W z) ∧
      (∫ z, W z ∂Measure.pi (fun _ : Fin N => signLaw))≤18/Real.sqrt T := by
  obtain ⟨V,hVm,hVi,hV0,hVb,hVE⟩ := exists_polynomial_tail_dominator N (blockLength N T)
    (blockLength_pos hN hT) (tailRadius_nonneg N T) (tailRadius_lt_one hN hT)
  let P := Measure.pi (fun _ : Fin N => signLaw)
  have hA : Measurable (alternatingVector (N := N)) := by unfold alternatingVector; fun_prop
  have hmp : MeasurePreserving (alternatingVector (N := N)) P P := ⟨hA,alternatingVector_map N⟩
  have hVA : Integrable (fun z => V (alternatingVector z)) P := hmp.integrable_comp_of_integrable hVi
  have hSN : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  refine ⟨fun z => (V z+V (alternatingVector z))/Real.sqrt (N:ℝ),
    (hVm.add (hVm.comp hA)).div_const _,(hVi.add hVA).div_const _,?_,?_,?_⟩
  · intro z
    exact div_nonneg (add_nonneg (hV0 z) (hV0 _)) hSN.le
  · intro z x hx
    unfold normalizedPolynomial
    change |finitePolynomial z x/Real.sqrt (N:ℝ)|≤_
    rw [abs_div,abs_of_pos hSN]
    apply div_le_div_of_nonneg_right _ hSN.le
    by_cases hx0 : 0≤x
    · exact (hVb z x hx0 ((le_abs_self x).trans hx)).trans (le_add_of_nonneg_right (hV0 _))
    · have hxneg : 0≤-x := by linarith
      have hxrad : -x≤tailRadius N T := by simpa only [abs_of_neg (lt_of_not_ge hx0)] using hx
      have hb := hVb (alternatingVector z) (-x) hxneg hxrad
      rw [← finitePolynomial_neg_argument,neg_neg] at hb
      exact hb.trans (le_add_of_nonneg_left (hV0 z))
  · rw [integral_div,integral_add hVi hVA]
    have he := congrArg (fun μ : Measure (Fin N → ℝ) => ∫ z, V z ∂μ) (alternatingVector_map N)
    rw [integral_map hA.aemeasurable hVm.aestronglyMeasurable] at he
    rw [he]
    have hb := normalized_tail_budget hN hT hTN
    have hE := div_le_div_of_nonneg_right hVE hSN.le
    rw [add_div]
    calc
      _ ≤ 9/Real.sqrt T+9/Real.sqrt T := add_le_add (hE.trans hb) (hE.trans hb)
      _ = _ := by ring

theorem normalized_polynomial_tail_probability {N : ℕ} (hN : 0<N) {T η : ℝ}
    (hT : 0<T) (hTN : T≤N) (hη : 0<η) :
    (Measure.pi (fun _ : Fin N => signLaw)).real
      {z | ∃ x : ℝ, |x|≤tailRadius N T ∧ η≤|normalizedPolynomial N z x|}≤18/(η*Real.sqrt T) := by
  obtain ⟨W,hWm,hWi,hW0,hWb,hWE⟩ := exists_normalized_tail_dominator hN hT hTN
  have hs : {z : Fin N → ℝ | ∃ x : ℝ, |x|≤tailRadius N T ∧ η≤|normalizedPolynomial N z x|}⊆{z | η≤W z} := by
    rintro z ⟨x,hx,hh⟩
    exact hh.trans (hWb z x hx)
  have hm := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hW0) hWi η
  have hp : (Measure.pi (fun _ : Fin N => signLaw)).real {z | η≤W z}≤(∫ z, W z ∂Measure.pi (fun _ : Fin N => signLaw))/η := by
    apply (le_div_iff₀ hη).mpr
    simpa only [mul_comm] using hm
  calc
    _ ≤ _ := measureReal_mono hs
    _ ≤ _ := hp
    _ ≤ (18/Real.sqrt T)/η := div_le_div_of_nonneg_right hWE hη.le
    _ = _ := by field_simp

end Erdos524.UniformPolynomialTail
