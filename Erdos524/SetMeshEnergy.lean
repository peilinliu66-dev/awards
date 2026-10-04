import Erdos524.UpperBlockMesh

namespace Erdos524.CauchyKernel
open scoped BigOperators

@[simp] theorem logTanhPotential_zero : logTanhPotential 0 = 0 := by
  simp [logTanhPotential]

noncomputable def setRowEnergy (s : Finset ℝ) : ℝ :=
  ∑ x ∈ s, ∑ y ∈ s, logTanhPotential |y-x|

theorem sum_ordered_set (s : Finset ℝ) {n : ℕ} (hn : s.card=n) (f : ℝ → ℝ) :
    (∑ i : Fin n, f (s.orderEmbOfFin hn i)) = ∑ x ∈ s, f x := by
  have he := (s.orderIsoOfFin hn).toEquiv.sum_comp (fun x : s => f x)
  change (∑ i : Fin n, f (s.orderEmbOfFin hn i)) = ∑ x : s, f x at he
  rw [Finset.sum_coe_sort] at he
  exact he

theorem potential_abs_split (x y : ℝ) : logTanhPotential |y-x| =
    (if x<y then logTanhPotential (y-x) else 0) +
      (if y<x then logTanhPotential (x-y) else 0) := by
  rcases lt_trichotomy x y with h | h | h
  · rw [if_pos h, if_neg (not_lt_of_ge h.le), abs_of_pos (sub_pos.mpr h), add_zero]
  · subst y; simp
  · rw [if_neg (not_lt_of_ge h.le), if_pos h, abs_of_neg (sub_neg.mpr h), zero_add, neg_sub]

theorem rowEnergy_eq_twice_pairEnergy {n : ℕ} (t : Fin n → ℝ) (ht : StrictMono t) :
    (∑ i, ∑ j, logTanhPotential |t j-t i|) = 2*pairEnergy t := by
  simp_rw [potential_abs_split, ht.lt_iff_lt, Finset.sum_add_distrib]
  have he : (∑ i : Fin n, ∑ j : Fin n, if j < i then logTanhPotential (t i-t j) else 0) = pairEnergy t := by
    rw [Finset.sum_comm]
    rfl
  rw [he]
  change pairEnergy t+pairEnergy t = _
  ring

theorem log_det_ordered_set {n : ℕ} (s : Finset ℝ) (hn : s.card=n) :
    Real.log (normalized (fun j : Fin n => Real.exp (s.orderEmbOfFin hn j))).det =
      -(n : ℝ)*Real.log 2-setRowEnergy s := by
  rw [log_det_normalized_exp _ (s.orderEmbOfFin hn).strictMono]
  rw [← rowEnergy_eq_twice_pairEnergy _ (s.orderEmbOfFin hn).strictMono]
  have he : (∑ i : Fin n, ∑ j : Fin n,
      logTanhPotential |s.orderEmbOfFin hn j-s.orderEmbOfFin hn i|) = setRowEnergy s := by
    have hrow (i : Fin n) := sum_ordered_set s hn
      (fun y => logTanhPotential |y-s.orderEmbOfFin hn i|)
    simp_rw [hrow]
    exact sum_ordered_set s hn (fun x => ∑ y ∈ s, logTanhPotential |y-x|)
  rw [he]


theorem block_row_energy_le {m : ℕ} (center : ℝ) {r : ℝ} (hr : 0 < r) (i : Fin m) :
    (∑ j : Fin m, logTanhPotential |blockPoint center r j-blockPoint center r i|) ≤
      r*(Real.pi^2/2) := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [Fin.sum_univ_succAbove _ i]
    simp only [sub_self, abs_zero, logTanhPotential_zero, zero_add]
    exact separated_row_energy_le (blockPoint center r) hr
      (fun a b _ => (blockPoint_gap center r a b).ge) i

theorem block_total_row_energy_le (m : ℕ) (center : ℝ) {r : ℝ} (hr : 0 < r) :
    (∑ i : Fin m, ∑ j : Fin m, logTanhPotential |blockPoint center r j-blockPoint center r i|) ≤
      (m : ℝ)*r*(Real.pi^2/2) := by
  calc
    _ ≤ ∑ _i : Fin m, r*(Real.pi^2/2) := Finset.sum_le_sum (fun i _ => block_row_energy_le center hr i)
    _ = _ := by simp; ring

theorem sum_blockPointSet {K : ℕ} (center r : Fin K → ℝ) (count : Fin K → ℕ)
    {width gap : ℝ} (hr : ∀ j, 0 < r j) (hcount : ∀ j, (count j : ℝ) ≤ r j*width)
    (hcenters : ∀ j k : Fin K, j < k → width+gap ≤ center k-center j)
    (hgap : 0 < gap) (f : ℝ → ℝ) :
    (∑ x ∈ blockPointSet center r count, f x) =
      ∑ j, ∑ a : Fin (count j), f (blockPoint (center j) (r j) a) := by
  classical
  unfold blockPointSet
  rw [Finset.sum_image]
  · rw [Fintype.sum_sigma]
  · intro p _ q _ he
    exact block_family_injective center r count hr hcount hcenters hgap he


theorem blockPointSet_rowEnergy_le {K : ℕ} (center r : Fin K → ℝ) (count : Fin K → ℕ)
    {width gap : ℝ} (hr : ∀ j, 0 < r j) (hcount : ∀ j, (count j : ℝ) ≤ r j*width)
    (hcenters : ∀ j k : Fin K, j < k → width+gap ≤ center k-center j)
    (hgap : Real.log 2 ≤ gap) :
    setRowEnergy (blockPointSet center r count) ≤
      (∑ j, (count j : ℝ)*r j*(Real.pi^2/2)) +
        (∑ j, (count j : ℝ))^2*(4*Real.exp (-gap)) := by
  classical
  have hgpos : 0 < gap := lt_of_lt_of_le (Real.log_pos (by norm_num)) hgap
  have hcross (j k : Fin K) (hjk : j ≠ k) (a : Fin (count j)) (b : Fin (count k)) :
      logTanhPotential |blockPoint (center k) (r k) b-blockPoint (center j) (r j) a| ≤
        4*Real.exp (-gap) := by
    have hab : gap ≤ |blockPoint (center k) (r k) b-blockPoint (center j) (r j) a| := by
      rcases lt_or_gt_of_ne hjk with h | h
      · exact (block_family_cross_gap center r count hr hcount hcenters h a b).trans (le_abs_self _)
      · have hh := block_family_cross_gap center r count hr hcount hcenters h b a
        have ha := neg_le_abs (blockPoint (center k) (r k) b-blockPoint (center j) (r j) a)
        linarith
    exact (logTanhPotential_antitone hgpos (lt_of_lt_of_le hgpos hab) hab).trans
      (logTanhPotential_tail hgap)
  have hblock (j k : Fin K) :
      (∑ a : Fin (count j), ∑ b : Fin (count k),
        logTanhPotential |blockPoint (center k) (r k) b-blockPoint (center j) (r j) a|) ≤
      (if j=k then (count j : ℝ)*r j*(Real.pi^2/2) else 0) +
        (count j : ℝ)*(count k : ℝ)*(4*Real.exp (-gap)) := by
    by_cases hjk : j=k
    · subst k
      rw [if_pos rfl]
      exact (block_total_row_energy_le (count j) (center j) (hr j)).trans
        (le_add_of_nonneg_right (by positivity))
    · rw [if_neg hjk, zero_add]
      calc
        _ ≤ ∑ _a : Fin (count j), ∑ _b : Fin (count k), 4*Real.exp (-gap) := by
          apply Finset.sum_le_sum
          intro a _
          exact Finset.sum_le_sum (fun b _ => hcross j k hjk a b)
        _ = _ := by simp; ring
  have hsum (f : ℝ → ℝ) := sum_blockPointSet center r count hr hcount hcenters hgpos f
  unfold setRowEnergy
  rw [hsum]
  have hinner (x : ℝ) := hsum (fun y => logTanhPotential |y-x|)
  simp_rw [hinner]
  have hswap (j : Fin K) :
      (∑ a : Fin (count j), ∑ k : Fin K, ∑ b : Fin (count k),
        logTanhPotential |blockPoint (center k) (r k) b-blockPoint (center j) (r j) a|) =
      ∑ k : Fin K, ∑ a : Fin (count j), ∑ b : Fin (count k),
        logTanhPotential |blockPoint (center k) (r k) b-blockPoint (center j) (r j) a| :=
    Finset.sum_comm
  simp_rw [hswap]
  calc
    _ ≤ ∑ j : Fin K, ∑ k : Fin K,
        ((if j=k then (count j : ℝ)*r j*(Real.pi^2/2) else 0) +
          (count j : ℝ)*(count k : ℝ)*(4*Real.exp (-gap))) :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hblock j k))
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      simp only [← Finset.sum_mul]
      ring

end Erdos524.CauchyKernel
