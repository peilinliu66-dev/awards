import Erdos524.SmoothCutoff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Erdos524.SoftMaximum
open scoped BigOperators

noncomputable def partition {n : ℕ} (β : ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, Real.exp (β*x i)
noncomputable def softMax {n : ℕ} (β : ℝ) (x : Fin n → ℝ) : ℝ := Real.log (partition β x)/β

 theorem partition_pos {n : ℕ} (hn : 0<n) (β : ℝ) (x : Fin n → ℝ) : 0<partition β x := by
  apply Finset.sum_pos'
  · intro i _; exact (Real.exp_pos _).le
  · exact ⟨⟨0,hn⟩,Finset.mem_univ _,Real.exp_pos _⟩

theorem coord_le_softMax {n : ℕ} {β : ℝ} (hβ : 0<β) (x : Fin n → ℝ) (i : Fin n) :
    x i≤softMax β x := by
  have hn : 0<n := Nat.pos_of_ne_zero (fun h => by subst n; exact Fin.elim0 i)
  have hs : Real.exp (β*x i)≤partition β x := by
    unfold partition
    exact Finset.single_le_sum (fun j _ => (Real.exp_pos (β*x j)).le) (Finset.mem_univ i)
  have hl := Real.log_le_log (Real.exp_pos _) hs
  rw [Real.log_exp] at hl
  unfold softMax
  apply (le_div_iff₀ hβ).mpr
  nlinarith

theorem softMax_le {n : ℕ} (hn : 0<n) {β : ℝ} (hβ : 0<β)
    (x : Fin n → ℝ) (M : ℝ) (hM : ∀ i, x i≤M) :
    softMax β x≤M+Real.log n/β := by
  have hnp : (0:ℝ)<n := by positivity
  have hs : partition β x≤(n:ℝ)*Real.exp (β*M) := by
    calc
      _ ≤ ∑ _i : Fin n, Real.exp (β*M) :=
        Finset.sum_le_sum (fun i _ => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hM i) hβ.le))
      _ = _ := by simp
  have hl := Real.log_le_log (partition_pos hn β x) hs
  rw [Real.log_mul (ne_of_gt hnp) (Real.exp_ne_zero _),Real.log_exp] at hl
  unfold softMax
  apply (div_le_iff₀ hβ).mpr
  have he : (M+Real.log n/β)*β=M*β+Real.log n := by field_simp
  rw [he]
  nlinarith

noncomputable def directionalMoment {n : ℕ} (β : ℝ) (x v : Fin n → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (∑ i, (v i)^k*Real.exp (β*(x i+t*v i))) / partition β (fun i => x i+t*v i)

theorem directionalMoment_zero {n : ℕ} (hn : 0<n) (β : ℝ) (x v : Fin n → ℝ) (t : ℝ) :
    directionalMoment β x v 0 t=1 := by
  unfold directionalMoment
  simp only [pow_zero,one_mul]
  exact div_self (ne_of_gt (partition_pos hn β _))

theorem directionalMoment_abs_le {n : ℕ} (hn : 0<n) (β : ℝ) (x v : Fin n → ℝ)
    {a : ℝ} (ha : 0≤a) (hv : ∀ i, |v i|≤a) (k : ℕ) (t : ℝ) :
    |directionalMoment β x v k t|≤a^k := by
  have hz := partition_pos hn β (fun i => x i+t*v i)
  unfold directionalMoment
  rw [abs_div,abs_of_pos hz]
  apply (div_le_iff₀ hz).mpr
  calc
    _ ≤ ∑ i, |(v i)^k*Real.exp (β*(x i+t*v i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, a^k*Real.exp (β*(x i+t*v i)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_pow,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hv i) k) (Real.exp_pos _).le
    _ = _ := by rw [← Finset.mul_sum]; rfl

end Erdos524.SoftMaximum
