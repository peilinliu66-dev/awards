import Erdos524.FiniteL2Variation
import Erdos524.LaplaceIncrementBudget
import Mathlib.Data.Fin.Tuple.Sort

namespace Erdos524.FiniteCellVariation
open MeasureTheory Filter
open Erdos524.FiniteChaining Erdos524.FiniteL2Variation Erdos524.LaplaceIncrementBudget

 theorem abs_sub_le_twice_variation {n : ℕ} (x : Fin (n+1) → ℝ) (i j : Fin (n+1)) :
    |x i-x j|≤2*∑ k : Fin n, |x k.castSucc-x k.succ| := by
  have hb (i : Fin (n+1)) : |x i-x (Fin.last n)|≤∑ k : Fin n, |x k.castSucc-x k.succ| := by
    have h := abs_le_last_add_variation (fun k => x k-x (Fin.last n)) i
    have he (k : Fin n) : (x k.castSucc-x (Fin.last n))-(x k.succ-x (Fin.last n))=x k.castSucc-x k.succ := by ring
    simp only [sub_self,abs_zero,zero_add,he] at h
    exact h
  have ht := abs_sub_le (x i) (x (Fin.last n)) (x j)
  rw [abs_sub_comm (x (Fin.last n)) (x j)] at ht
  linarith [hb i,hb j]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem exists_cell_variation {n : ℕ} (p : Fin (n+1) → ℝ) (X : Ω → Fin (n+1) → ℝ)
    (hXm : ∀ i, Measurable (fun ω => X ω i)) (hX : ∀ i, MemLp (fun ω => X ω i) 2 P)
    {a b : ℝ} (ha : 0≤a) (hlo : ∀ i, a≤p i) (hhi : ∀ i, p i≤b)
    (hinc : ∀ i j, (∫ ω, (X ω i-X ω j)^2 ∂P)≤(Real.exp 1*(rootBudget (p i)-rootBudget (p j)))^2) :
    ∃ V : Ω → ℝ, Measurable V ∧ MemLp V 2 P ∧ (∀ ω, 0≤V ω) ∧
      (∀ ω i j, |X ω i-X ω j|≤V ω) ∧
      (∫ ω, (V ω)^2 ∂P)≤(2*Real.exp 1*(rootBudget a-rootBudget b))^2 := by
  classical
  let e := Tuple.sort p
  let Y : Ω → Fin (n+1) → ℝ := fun ω i => X ω (e i)
  let D : Fin n → Ω → ℝ := fun k ω => Y ω k.castSucc-Y ω k.succ
  let A : Fin n → ℝ := fun k => Real.exp 1*(rootBudget (p (e k.castSucc))-rootBudget (p (e k.succ)))
  have hm : Monotone (fun i => p (e i)) := Tuple.monotone_sort p
  have hD (k : Fin n) : MemLp (D k) 2 P := (hX _).sub (hX _)
  have hA (k : Fin n) : 0≤A k := by
    apply mul_nonneg (Real.exp_pos 1).le
    apply sub_nonneg.mpr
    exact rootBudget_antitone (ha.trans (hlo _)) (hm (by change k.val≤k.val+1; omega))
  have hDb : ∀ k, (∫ ω, (D k ω)^2 ∂P)≤(A k)^2 := fun k => hinc _ _
  have hsum := integral_squared_abs_sum_le D hD A hA hDb
  have heA : (∑ k, A k)=Real.exp 1*(rootBudget (p (e 0))-rootBudget (p (e (Fin.last n)))) := by
    dsimp only [A]
    rw [← Finset.mul_sum,Finset.sum_sub_distrib]
    congr 1
    have h1 := Fin.sum_univ_castSucc (fun i : Fin (n+1) => rootBudget (p (e i)))
    have h2 := Fin.sum_univ_succ (fun i : Fin (n+1) => rootBudget (p (e i)))
    linarith
  have hab : a≤b := (hlo 0).trans (hhi 0)
  have hgap : 0≤Real.exp 1*(rootBudget a-rootBudget b) :=
    mul_nonneg (Real.exp_pos 1).le (sub_nonneg.mpr (rootBudget_antitone ha hab))
  have hAb : (∑ k, A k)≤Real.exp 1*(rootBudget a-rootBudget b) := by
    rw [heA]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
    have h1 := rootBudget_antitone ha (hlo (e 0))
    have h2 := rootBudget_antitone (ha.trans (hlo (e (Fin.last n)))) (hhi (e (Fin.last n)))
    linarith
  have hsq : (∑ k, A k)^2≤(Real.exp 1*(rootBudget a-rootBudget b))^2 :=
    (sq_le_sq₀ (Finset.sum_nonneg (fun k _ => hA k)) hgap).mpr hAb
  refine ⟨fun ω => 2*∑ k, |D k ω|,?_,?_,?_,?_,?_⟩
  · apply measurable_const.mul
    apply Finset.measurable_sum
    intro k hk
    exact continuous_abs.measurable.comp ((hXm _).sub (hXm _))
  · apply MemLp.const_mul
    apply memLp_finsetSum Finset.univ
    intro k hk
    simpa only [Real.norm_eq_abs] using (hD k).norm
  · intro ω
    positivity
  · intro ω i j
    have h := abs_sub_le_twice_variation (Y ω) (e.symm i) (e.symm j)
    simpa only [Y,D,e.apply_symm_apply] using h
  · have he : (fun ω => (2*∑ k, |D k ω|)^2)=(fun ω => 4*(∑ k, |D k ω|)^2) := by funext ω; ring
    rw [he,integral_const_mul]
    nlinarith [hsum.trans hsq]

end Erdos524.FiniteCellVariation
