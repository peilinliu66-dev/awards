import Erdos524.FinitePolynomialAbel
import Erdos524.SignCoordinateRestriction

namespace Erdos524.PolynomialBlockTail
open MeasureTheory ProbabilityTheory
open Erdos524.FinitePolynomialAbel Erdos524.FiniteSignWalk
open Erdos524.SignCoordinateRestriction Erdos524.SignGaussianMoments

 theorem exists_polynomial_tail_dominator (N m : ℕ) (hm : 0<m) {a : ℝ} (ha : 0≤a) (ha1 : a<1) :
    ∃ W : (Fin N → ℝ) → ℝ, Measurable W ∧ Integrable W (Measure.pi (fun _ : Fin N => signLaw)) ∧
      (∀ z, 0≤W z) ∧ (∀ z x, 0≤x → x≤a → |finitePolynomial z x|≤W z) ∧
      (∫ z, W z ∂Measure.pi (fun _ : Fin N => signLaw))≤3*Real.sqrt (m:ℝ)/(1-a^m) := by
  have hap : 0≤a^m := pow_nonneg ha _
  have hap1 : a^m<1 := pow_lt_one₀ ha ha1 (by omega)
  have hden : 0<1-a^m := by linarith
  let B : ℝ := 3*Real.sqrt (m:ℝ)/(1-a^m)
  have hB0 : 0≤B := by dsimp only [B]; positivity
  have hBbase : 3*Real.sqrt (m:ℝ)≤B := by
    dsimp only [B]
    apply (le_div_iff₀ hden).mpr
    nlinarith [Real.sqrt_nonneg (m:ℝ)]
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hNm : N≤m
    · refine ⟨walkMax,(walkMax_continuous N).measurable,walkMax_integrable N,fun z => norm_nonneg _,?_,?_⟩
      · intro z x hx hxa
        exact finitePolynomial_abs_le_walkMax z hx (hxa.trans ha1.le)
      · by_cases hN : N=0
        · subst N
          simpa [walkMax,walkPrefix] using hB0
        · have h := integral_walkMax_le (Nat.pos_of_ne_zero hN)
          exact h.trans ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hNm)) (by norm_num)).trans hBbase)
    · have hmN : m≤N := by omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmN
      obtain ⟨W,hWm,hWi,hW0,hWb,hWE⟩ := ih k (by omega)
      let H : (Fin (m+k) → ℝ) → ℝ := fun z => walkMax (fun i => z (Fin.castAdd k i))
      let T : (Fin (m+k) → ℝ) → ℝ := fun z => W (fun i => z (Fin.natAdd m i))
      have hH : Integrable H (Measure.pi (fun _ : Fin (m+k) => signLaw)) :=
        integrable_pi_sign_restriction (Fin.castAdd k) (Fin.castAdd_injective _ _) walkMax (walkMax_integrable m)
      have hT : Integrable T (Measure.pi (fun _ : Fin (m+k) => signLaw)) :=
        integrable_pi_sign_restriction (Fin.natAdd m) (Fin.natAdd_injective _ _) W hWi
      refine ⟨fun z => H z+a^m*T z,?_,hH.add (hT.const_mul _),?_,?_,?_⟩
      · apply Measurable.add
        · exact (walkMax_continuous m).measurable.comp (by fun_prop)
        · exact measurable_const.mul (hWm.comp (by fun_prop))
      · intro z
        exact add_nonneg (norm_nonneg _) (mul_nonneg hap (hW0 _))
      · intro z x hx hxa
        rw [finitePolynomial_split]
        calc
          _ ≤ |finitePolynomial (fun i => z (Fin.castAdd k i)) x|+
              |x^m*finitePolynomial (fun i => z (Fin.natAdd m i)) x| := abs_add_le _ _
          _ ≤ H z+a^m*T z := by
            apply add_le_add (finitePolynomial_abs_le_walkMax _ hx (hxa.trans ha1.le))
            rw [abs_mul,abs_of_nonneg (pow_nonneg hx _)]
            exact (mul_le_mul_of_nonneg_left (hWb _ x hx hxa) (pow_nonneg hx _)).trans
              (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxa m) (hW0 _))
      · rw [integral_add hH (hT.const_mul _),integral_const_mul]
        have heH := integral_pi_sign_restriction (Fin.castAdd k) (Fin.castAdd_injective _ _) walkMax (walkMax_continuous m).measurable
        have heT := integral_pi_sign_restriction (Fin.natAdd m) (Fin.natAdd_injective _ _) W hWm
        change (∫ z, H z ∂Measure.pi (fun _ : Fin (m+k) => signLaw))=_ at heH
        change (∫ z, T z ∂Measure.pi (fun _ : Fin (m+k) => signLaw))=_ at heT
        rw [heH,heT]
        calc
          _ ≤ 3*Real.sqrt (m:ℝ)+a^m*B := add_le_add (integral_walkMax_le hm) (mul_le_mul_of_nonneg_left hWE hap)
          _ = B := by dsimp only [B]; field_simp; ring

end Erdos524.PolynomialBlockTail
