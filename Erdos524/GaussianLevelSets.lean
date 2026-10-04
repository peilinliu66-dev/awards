import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
Compact convex symmetric positive superlevels of the unnormalized standard
Gaussian density on a finite coordinate space. The norm used on the coordinate
space need not be the Euclidean norm: the energy is explicitly the sum of squares.
-/

namespace Erdos524.GaussianLevelSets

open Set
open scoped BigOperators

variable {n : ℕ}

noncomputable def energy (x : Fin (n + 1) → ℝ) : ℝ := ∑ i, (x i) ^ 2

noncomputable def rho (x : Fin (n + 1) → ℝ) : ℝ := Real.exp (-energy x / 2)

theorem energy_nonneg (x : Fin (n + 1) → ℝ) : 0 ≤ energy x :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg (x i)

theorem coordinate_sq_le_energy (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (x i) ^ 2 ≤ energy x :=
  Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)

@[simp] theorem energy_neg (x : Fin (n + 1) → ℝ) : energy (-x) = energy x := by
  simp [energy]

theorem continuous_energy : Continuous (energy (n := n)) := by
  unfold energy
  fun_prop

theorem continuous_rho : Continuous (rho (n := n)) := by
  exact Real.continuous_exp.comp (continuous_energy.neg.div_const 2)

theorem measurable_rho : Measurable (rho (n := n)) := continuous_rho.measurable

theorem rho_pos (x : Fin (n + 1) → ℝ) : 0 < rho x := Real.exp_pos _

theorem rho_nonneg (x : Fin (n + 1) → ℝ) : 0 ≤ rho x := (rho_pos x).le

@[simp] theorem rho_neg (x : Fin (n + 1) → ℝ) : rho (-x) = rho x := by
  simp [rho]

theorem energy_convex_le (x y : Fin (n + 1) → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    energy (a • x + b • y) ≤ a * energy x + b * energy y := by
  have hi (i : Fin (n + 1)) :
      (a * x i + b * y i) ^ 2 ≤ a * (x i) ^ 2 + b * (y i) ^ 2 := by
    have hn : 0 ≤ a * b * (x i - y i) ^ 2 :=
      mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
    have he : (a * x i + b * y i) ^ 2 + a * b * (x i - y i) ^ 2 =
        a * (x i) ^ 2 + b * (y i) ^ 2 := by
      calc
        _ = (a + b) * (a * (x i) ^ 2 + b * (y i) ^ 2) := by ring
        _ = _ := by rw [hab, one_mul]
    linarith
  calc
    energy (a • x + b • y) ≤ ∑ i, (a * (x i) ^ 2 + b * (y i) ^ 2) :=
      Finset.sum_le_sum fun i _ ↦ hi i
    _ = a * energy x + b * energy y := by
      simp [energy, Finset.sum_add_distrib, Finset.mul_sum]

def energySublevel (r : ℝ) : Set (Fin (n + 1) → ℝ) := {x | energy x ≤ r}

theorem convex_energySublevel (r : ℝ) : Convex ℝ (energySublevel (n := n) r) := by
  intro x hx y hy a b ha hb hab
  change energy (a • x + b • y) ≤ r
  calc
    energy (a • x + b • y) ≤ a * energy x + b * energy y :=
      energy_convex_le x y ha hb hab
    _ ≤ a * r + b * r := add_le_add
      (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = r := by rw [← add_mul, hab, one_mul]

theorem isClosed_energySublevel (r : ℝ) : IsClosed (energySublevel (n := n) r) :=
  isClosed_le continuous_energy continuous_const

theorem energySublevel_subset_closedBall (r : ℝ) :
    energySublevel (n := n) r ⊆ Metric.closedBall 0 (|r| + 1) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ |r| + 1)).2
  intro i
  rw [Real.norm_eq_abs]
  apply abs_le_of_sq_le_sq ?_ (by positivity)
  have hxi : (x i) ^ 2 ≤ r := (coordinate_sq_le_energy x i).trans hx
  nlinarith [le_abs_self r, sq_nonneg (|r|), abs_nonneg r]

theorem isCompact_energySublevel (r : ℝ) : IsCompact (energySublevel (n := n) r) :=
  (isCompact_closedBall (0 : Fin (n + 1) → ℝ) (|r| + 1)).of_isClosed_subset
    (isClosed_energySublevel r) (energySublevel_subset_closedBall r)

theorem superlevel_eq_energySublevel {s : ℝ} (hs : 0 < s) :
    {x : Fin (n + 1) → ℝ | s ≤ rho x} = energySublevel (-2 * Real.log s) := by
  ext x
  change (s ≤ Real.exp (-energy x / 2)) ↔ energy x ≤ -2 * Real.log s
  rw [← Real.log_le_iff_le_exp hs]
  constructor <;> intro h <;> linarith

theorem isCompact_superlevel {s : ℝ} (hs : 0 < s) :
    IsCompact {x : Fin (n + 1) → ℝ | s ≤ rho x} := by
  rw [superlevel_eq_energySublevel hs]
  exact isCompact_energySublevel _

theorem convex_superlevel {s : ℝ} (hs : 0 < s) :
    Convex ℝ {x : Fin (n + 1) → ℝ | s ≤ rho x} := by
  rw [superlevel_eq_energySublevel hs]
  exact convex_energySublevel _

theorem neg_mem_superlevel {s : ℝ} {x : Fin (n + 1) → ℝ}
    (hx : x ∈ {x : Fin (n + 1) → ℝ | s ≤ rho x}) :
    -x ∈ {x : Fin (n + 1) → ℝ | s ≤ rho x} := by
  simpa only [mem_setOf_eq, rho_neg] using hx

end Erdos524.GaussianLevelSets
