import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

namespace Erdos524.SmoothCutoff
open Set Filter
open scoped BigOperators

noncomputable def cutoff (x : ℝ) : ℝ := 1-Real.smoothTransition x

theorem cutoff_one {x : ℝ} (hx : x≤0) : cutoff x=1 := by
  simp [cutoff,Real.smoothTransition.zero_of_nonpos hx]

theorem cutoff_zero {x : ℝ} (hx : 1≤x) : cutoff x=0 := by
  simp [cutoff,Real.smoothTransition.one_of_one_le hx]

theorem cutoff_mem_Icc (x : ℝ) : cutoff x ∈ Icc (0:ℝ) 1 := by
  have h1 := Real.smoothTransition.nonneg x
  have h2 := Real.smoothTransition.le_one x
  unfold cutoff
  constructor <;> linarith

theorem cutoff_contDiff (n : ℕ) : ContDiff ℝ n cutoff := by
  unfold cutoff
  exact contDiff_const.sub Real.smoothTransition.contDiff

theorem cutoff_deriv_compact : HasCompactSupport (deriv cutoff) := by
  apply HasCompactSupport.intro (K := Icc (0:ℝ) 1) isCompact_Icc
  intro x hx
  by_cases h0 : x<0
  · have he : cutoff =ᶠ[nhds x] (fun _ : ℝ => 1) := by
      filter_upwards [isOpen_Iio.mem_nhds h0] with y hy
      exact cutoff_one hy.le
    simpa using he.deriv_eq
  · have h1 : 1<x := lt_of_not_ge (fun h => hx ⟨le_of_not_gt h0,h⟩)
    have he : cutoff =ᶠ[nhds x] (fun _ : ℝ => 0) := by
      filter_upwards [isOpen_Ioi.mem_nhds h1] with y hy
      exact cutoff_zero hy.le
    simpa using he.deriv_eq

theorem cutoff_iterated_deriv_compact (n : ℕ) : HasCompactSupport (iteratedDeriv (n+1) cutoff) := by
  induction n with
  | zero => simpa only [Nat.zero_add,iteratedDeriv_one] using cutoff_deriv_compact
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

theorem exists_cutoff_derivative_bound : ∃ C : ℝ, 1≤C ∧
    ∀ j : Fin 4, ∀ x : ℝ, ‖iteratedDeriv (j.val+1) cutoff x‖≤C := by
  classical
  have hb (j : Fin 4) : ∃ C : ℝ, ∀ x : ℝ, ‖iteratedDeriv (j.val+1) cutoff x‖≤C :=
    (cutoff_iterated_deriv_compact j.val).exists_bound_of_continuous
      ((cutoff_contDiff (j.val+1)).continuous_iteratedDeriv (j.val+1) (le_refl _))
  choose C hC using hb
  refine ⟨1+∑ j : Fin 4, |C j|,?_,?_⟩
  · have h : 0≤∑ j : Fin 4, |C j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    linarith
  · intro j x
    have h1 := hC j x
    have h2 := le_abs_self (C j)
    have h3 := Finset.single_le_sum (fun k _ => abs_nonneg (C k)) (Finset.mem_univ j)
    linarith

end Erdos524.SmoothCutoff
