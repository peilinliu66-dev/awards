import Erdos524.SeparatedGridInverse
import Mathlib.Data.Finset.Sort

namespace Erdos524.CauchyKernel
open scoped BigOperators

theorem full_separation_of_adjacent {n : ℕ} (t : Fin (n+1) → ℝ) {r : ℝ} (hr : 0 < r)
    (hstep : ∀ i : Fin n, 1/r ≤ t i.succ-t i.castSucc) :
    ∀ i j : Fin (n+1), i < j → ((j:ℝ)-(i:ℝ))/r ≤ t j-t i := by
  have hm : Monotone (fun i : Fin (n+1) => t i-(i:ℝ)/r) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have h := hstep i
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    rw [add_div]
    linarith
  intro i j hij
  have h := hm (le_of_lt hij)
  rw [sub_div]
  linarith

theorem ordered_set_full_separation (s : Finset ℝ) {n : ℕ} (hn : s.card = n+1)
    {r : ℝ} (hr : 0 < r)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x < y → 1/r ≤ y-x) :
    ∀ i j : Fin (n+1), i < j →
      ((j:ℝ)-(i:ℝ))/r ≤ s.orderEmbOfFin hn j-s.orderEmbOfFin hn i := by
  apply full_separation_of_adjacent _ hr
  intro i
  exact hsep _ (s.orderEmbOfFin_mem hn i.castSucc) _ (s.orderEmbOfFin_mem hn i.succ)
    ((s.orderEmbOfFin hn).strictMono (by simp))

theorem ordered_set_inverse_trace_le (s : Finset ℝ) {n : ℕ} (hn : s.card = n+1)
    {r : ℝ} (hr : 0 < r)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x < y → 1/r ≤ y-x) :
    Matrix.trace ((normalized (fun j : Fin (n+1) => Real.exp (s.orderEmbOfFin hn j)))⁻¹) ≤
      (n+1 : ℝ)*2*Real.exp (r*Real.pi^2) :=
  separated_inverse_trace_le _ hr (ordered_set_full_separation s hn hr hsep)

end Erdos524.CauchyKernel
