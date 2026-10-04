import Erdos524.FiniteCellVariation

namespace Erdos524.GaussianGridBudget
open Erdos524.LaplaceIncrementBudget

noncomputable def cellBudget (h : ℝ) (j : ℕ) : ℝ :=
  2*Real.exp 1*(rootBudget ((j:ℝ)*h)-rootBudget (((j+1:ℕ):ℝ)*h))

theorem rootBudget_nonneg (u : ℝ) : 0≤rootBudget u := by unfold rootBudget; positivity

theorem cellBudget_nonneg {h : ℝ} (hh : 0≤h) (j : ℕ) : 0≤cellBudget h j := by
  unfold cellBudget
  apply mul_nonneg (by positivity)
  apply sub_nonneg.mpr
  apply rootBudget_antitone (by positivity)
  push_cast
  nlinarith

theorem sum_cellBudget_sq_le (J : ℕ) {h : ℝ} (hh : 0≤h) :
    (∑ j : Fin J, (cellBudget h j.val)^2)≤2*(Real.exp 1)^2*h := by
  let d : ℕ → ℝ := fun j => rootBudget ((j:ℝ)*h)-rootBudget (((j+1:ℕ):ℝ)*h)
  have hd (j : ℕ) : 0≤d j := by
    apply sub_nonneg.mpr
    apply rootBudget_antitone (by positivity)
    push_cast
    nlinarith
  have hdb (j : ℕ) : d j≤h/2 := by
    have hx : (j:ℝ)*h≤((j+1:ℕ):ℝ)*h := by push_cast; nlinarith
    have hb := rootBudget_gap (by positivity : (0:ℝ)≤(j:ℝ)*h) hx
    have he : ((j+1:ℕ):ℝ)*h-(j:ℝ)*h=h := by push_cast; ring
    simpa only [d,he] using hb
  have htel : (∑ j : Fin J, d j.val)=1-rootBudget ((J:ℝ)*h) := by
    change (∑ j : Fin J, ((fun i : Fin (J+1) => rootBudget ((i:ℝ)*h)) j.castSucc - (fun i : Fin (J+1) => rootBudget ((i:ℝ)*h)) j.succ))=_
    rw [Finset.sum_sub_distrib]
    have h1 := Fin.sum_univ_castSucc (fun i : Fin (J+1) => rootBudget ((i:ℝ)*h))
    have h2 := Fin.sum_univ_succ (fun i : Fin (J+1) => rootBudget ((i:ℝ)*h))
    simp only [Fin.val_zero,Nat.cast_zero,zero_mul,Fin.val_last] at h1 h2
    have hr : rootBudget 0=1 := by simp [rootBudget]
    rw [hr] at h2
    linarith
  have hsum : (∑ j : Fin J, d j.val)≤1 := by rw [htel]; linarith [rootBudget_nonneg ((J:ℝ)*h)]
  have hsq : (∑ j : Fin J, (d j.val)^2)≤h/2 := by
    calc
      _ ≤ ∑ j : Fin J, (h/2)*d j.val := Finset.sum_le_sum (fun j _ => by nlinarith [hd j.val,hdb j.val])
      _ = (h/2)*(∑ j : Fin J, d j.val) := by rw [Finset.mul_sum]
      _ ≤ h/2 := by nlinarith
  have he : (∑ j : Fin J, (cellBudget h j.val)^2)=4*(Real.exp 1)^2*(∑ j : Fin J, (d j.val)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    unfold cellBudget d
    ring
  rw [he]
  nlinarith [sq_nonneg (Real.exp 1)]

end Erdos524.GaussianGridBudget
