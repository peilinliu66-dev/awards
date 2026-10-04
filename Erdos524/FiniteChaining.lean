import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! Dimension-free finite telescoping bounds, without process existence assumptions. -/

namespace Erdos524.FiniteChaining

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem abs_le_last_add_variation {n : ℕ} (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    |x i| ≤ |x (Fin.last n)| + ∑ j : Fin n, |x j.castSucc - x j.succ| := by
  induction n with
  | zero =>
    have hi : i = 0 := by apply Fin.ext; have := i.isLt; omega
    simp [hi]
  | succ n ih =>
    have hvar : (∑ j : Fin (n + 1), |x j.castSucc - x j.succ|) =
        (∑ j : Fin n, |x j.castSucc.castSucc - x j.succ.castSucc|) +
          |x (Fin.last n).castSucc - x (Fin.last (n + 1))| := by
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [hvar]
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · have hs : 0 ≤ ∑ j : Fin n, |x j.castSucc.castSucc - x j.succ.castSucc| :=
        Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
      linarith [abs_nonneg (x (Fin.last n).castSucc - x (Fin.last (n + 1)))]
    · have h := ih (fun k ↦ x k.castSucc) j
      have ht : |x (Fin.last n).castSucc| ≤
          |x (Fin.last n).castSucc - x (Fin.last (n + 1))| + |x (Fin.last (n + 1))| := by
        simpa only [sub_add_cancel] using
          abs_add_le (x (Fin.last n).castSucc - x (Fin.last (n + 1))) (x (Fin.last (n + 1)))
      linarith

theorem norm_le_last_add_variation {n : ℕ} (x : Fin (n + 1) → ℝ) :
    ‖x‖ ≤ |x (Fin.last n)| + ∑ j : Fin n, |x j.castSucc - x j.succ| := by
  apply (pi_norm_le_iff_of_nonneg
    (add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))).2
  intro i
  rw [Real.norm_eq_abs]
  exact abs_le_last_add_variation x i

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem integral_abs_le_sqrt_second_moment {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (∫ ω, |X ω| ∂P) ≤ Real.sqrt (∫ ω, (X ω) ^ 2 ∂P) := by
  have ha : MemLp (fun ω ↦ |X ω|) 2 P := by simpa only [Real.norm_eq_abs] using hX.norm
  have hv := variance_nonneg (fun ω ↦ |X ω|) P
  rw [variance_eq_sub ha] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  have hsq : 0 ≤ ∫ ω, (X ω) ^ 2 ∂P := integral_nonneg fun ω ↦ sq_nonneg _
  nlinarith [Real.sq_sqrt hsq, Real.sqrt_nonneg (∫ ω, (X ω) ^ 2 ∂P)]

theorem integral_norm_le_l2_variation {n : ℕ} {X : Ω → (Fin (n + 1) → ℝ)}
    (hX : ∀ i, MemLp (fun ω ↦ X ω i) 2 P) :
    (∫ ω, ‖X ω‖ ∂P) ≤
      Real.sqrt (∫ ω, (X ω (Fin.last n)) ^ 2 ∂P) +
        ∑ j : Fin n, Real.sqrt (∫ ω, (X ω j.castSucc - X ω j.succ) ^ 2 ∂P) := by
  have hvec : MemLp X 2 P := memLp_pi_iff.mpr hX
  have hint : Integrable (fun ω ↦ ‖X ω‖) P := (hvec.integrable (by norm_num)).norm
  have hlast : Integrable (fun ω ↦ |X ω (Fin.last n)|) P :=
    ((hX _).integrable (by norm_num)).abs
  have hdiff (j : Fin n) : MemLp (fun ω ↦ X ω j.castSucc - X ω j.succ) 2 P :=
    (hX j.castSucc).sub (hX j.succ)
  have hdiffint (j : Fin n) : Integrable (fun ω ↦ |X ω j.castSucc - X ω j.succ|) P :=
    ((hdiff j).integrable (by norm_num)).abs
  have hsum : Integrable (fun ω ↦ ∑ j : Fin n, |X ω j.castSucc - X ω j.succ|) P :=
    integrable_finsetSum Finset.univ (fun j _ ↦ hdiffint j)
  calc
    (∫ ω, ‖X ω‖ ∂P) ≤
        ∫ ω, |X ω (Fin.last n)| + ∑ j : Fin n, |X ω j.castSucc - X ω j.succ| ∂P :=
      integral_mono hint (hlast.add hsum) (fun ω ↦ norm_le_last_add_variation (X ω))
    _ = (∫ ω, |X ω (Fin.last n)| ∂P) +
        ∑ j : Fin n, ∫ ω, |X ω j.castSucc - X ω j.succ| ∂P := by
      rw [integral_add hlast hsum, integral_finsetSum _ (fun j _ ↦ hdiffint j)]
    _ ≤ _ := add_le_add (integral_abs_le_sqrt_second_moment (hX _))
      (Finset.sum_le_sum fun j _ ↦ integral_abs_le_sqrt_second_moment (hdiff j))

theorem integral_norm_le_budget {n : ℕ} {X : Ω → (Fin (n + 1) → ℝ)}
    (hX : ∀ i, MemLp (fun ω ↦ X ω i) 2 P)
    (a : ℝ) (b : Fin n → ℝ) (ha : 0 ≤ a) (hb : ∀ j, 0 ≤ b j)
    (hlast : (∫ ω, (X ω (Fin.last n)) ^ 2 ∂P) ≤ a ^ 2)
    (hdiff : ∀ j, (∫ ω, (X ω j.castSucc - X ω j.succ) ^ 2 ∂P) ≤ (b j) ^ 2) :
    (∫ ω, ‖X ω‖ ∂P) ≤ a + ∑ j, b j := by
  refine (integral_norm_le_l2_variation hX).trans (add_le_add ?_ ?_)
  · exact (Real.sqrt_le_sqrt hlast).trans_eq (Real.sqrt_sq ha)
  · exact Finset.sum_le_sum fun j _ ↦
      (Real.sqrt_le_sqrt (hdiff j)).trans_eq (Real.sqrt_sq (hb j))

/-- A decreasing endpoint/increment budget telescopes independently of the
number of requested evaluation points. -/
theorem integral_norm_le_decreasing_budget {n : ℕ} {X : Ω → (Fin (n + 1) → ℝ)}
    (hX : ∀ i, MemLp (fun ω ↦ X ω i) 2 P)
    (r : Fin (n + 1) → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hdecr : ∀ j : Fin n, r j.succ ≤ r j.castSucc)
    (hlast : (∫ ω, (X ω (Fin.last n)) ^ 2 ∂P) ≤ (r (Fin.last n)) ^ 2)
    (hdiff : ∀ j : Fin n, (∫ ω, (X ω j.castSucc - X ω j.succ) ^ 2 ∂P) ≤
      (r j.castSucc - r j.succ) ^ 2) :
    (∫ ω, ‖X ω‖ ∂P) ≤ r 0 := by
  have h := integral_norm_le_budget hX (r (Fin.last n))
    (fun j ↦ r j.castSucc - r j.succ) (hr _) (fun j ↦ sub_nonneg.mpr (hdecr j)) hlast hdiff
  have he : (∑ j : Fin n, (r j.castSucc - r j.succ)) = r 0 - r (Fin.last n) := by
    rw [Finset.sum_sub_distrib]
    linarith [Fin.sum_univ_castSucc r, Fin.sum_univ_succ r]
  rw [he] at h
  linarith

end Erdos524.FiniteChaining
