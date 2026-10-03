import Erdos1017.DenseCut
import Erdos1017.WeightedFoundation
import Erdos1017.PackingEdgeCount

/-! Numerical estimates for the uniform dense saving. UNCOMPILED.
Graph-existence steps are supplied by their separate constructive modules. -/

namespace Erdos1017

open scoped BigOperators

theorem balanced_part_bounds {n x d : ℝ} (hn : 0 ≤ n)
    (hbal : (x - n / 2)^2 ≤ 6 * d) (hsmall : 10000 * d ≤ n^2) :
    19 * n ≤ 40 * x ∧ 40 * x ≤ 21 * n := by
  constructor
  · by_contra h
    have h1 : 0 < 19 * n - 40 * x := by linarith
    have h2 : 0 < 21 * n - 40 * x := by linarith
    have hp := mul_pos h1 h2
    nlinarith [sq_nonneg n]
  · by_contra h
    have h1 : 0 < 40 * x - 21 * n := by linarith
    have h2 : 0 < 40 * x - 19 * n := by linarith
    have hp := mul_pos h1 h2
    nlinarith [sq_nonneg n]

theorem balanced_parts_positive {n x y d : ℝ} (hn : 0 < n)
    (hxy : x + y = n) (hbal : (x - n / 2)^2 ≤ 6 * d)
    (hsmall : 10000 * d ≤ n^2) : 0 < x ∧ 0 < y ∧ 9 * (x - y) ≤ x := by
  obtain ⟨hl, hu⟩ := balanced_part_bounds hn.le hbal hsmall
  constructor
  · linarith
  constructor <;> linarith

theorem discarded_le_ninth {x y ell m : ℝ} (hx : 0 < x) (hm : 0 ≤ m)
    (hell : 0 ≤ ell) (hbalance : 9 * (x - y) ≤ x)
    (hbudget : x * ell ≤ (x - min x y) * m) : 9 * ell ≤ m := by
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy] at hbudget
    nlinarith
  · have hyx : y ≤ x := le_of_lt (lt_of_not_ge hxy)
    rw [min_eq_right hyx] at hbudget
    have hmul := mul_le_mul_of_nonneg_right hbalance hm
    nlinarith

theorem near_dense_surplus {n e p d m ell mu q cross : ℝ}
    (hd : 0 ≤ d) (hdef : p = n^2 / 4 - d)
    (hpacking : p + m ≤ cross + 2 * ell + 2 * mu + q)
    (hcross : cross ≤ n^2 / 4) (hmiss : mu ≤ 6 * d)
    (hq : q ≤ 5 * d) (hell : 9 * ell ≤ m)
    (hedges : e ≤ cross + 2 * m) : e - n^2 / 4 ≤ 72 * d := by
  have hm : m ≤ 36 * d := by linarith
  linarith

theorem uniform_real_saving {n e p : ℝ} (hn : 0 ≤ n)
    (hp : p ≤ n^2 / 4) (he : e ≤ n^2 / 2)
    (hnear : 10000 * (n^2 / 4 - p) ≤ n^2 →
      e - n^2 / 4 ≤ 72 * (n^2 / 4 - p)) :
    e - n^2 / 4 ≤ 2500 * (n^2 / 4 - p) := by
  by_cases hsmall : 10000 * (n^2 / 4 - p) ≤ n^2
  · have h := hnear hsmall
    linarith
  · have hlarge : n^2 < 10000 * (n^2 / 4 - p) := lt_of_not_ge hsmall
    nlinarith

/-- Square residues give the exact quarter-floor error, without a parity premise. -/
theorem square_quarter_floor_bounds (n : ℕ) :
    (balancedThreshold n : ℝ) ≤ (n : ℝ)^2 / 4 ∧
      (n : ℝ)^2 / 4 ≤ balancedThreshold n + 1 / 4 := by
  have hhalf := floor_square_half_eq_twice_quarter n
  have hdiv := Nat.mod_add_div (n^2) 2
  have hmod := Nat.mod_lt (n^2) (by decide : 0 < 2)
  have hlow : 4 * balancedThreshold n ≤ n^2 := by
    unfold balancedThreshold
    omega
  have hhigh : n^2 ≤ 4 * balancedThreshold n + 1 := by
    unfold balancedThreshold at *
    omega
  have hlowR : 4 * (balancedThreshold n : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast hlow
  have hhighR : (n : ℝ)^2 ≤ 4 * (balancedThreshold n : ℝ) + 1 := by exact_mod_cast hhigh
  constructor <;> linarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At the balanced threshold, a minimum count forces every low-weight block
to be a single edge. Thus any positive edge surplus forces a positive deficit.
-/
theorem partitionNumber_lt_balanced_of_dense (G : SimpleGraph V)
    (hdense : balancedThreshold (Fintype.card V) < edgeCount G) :
    partitionNumber G < balancedThreshold (Fintype.card V) := by
  classical
  have hp := partitionNumber_le_balancedThreshold G
  by_contra h
  have heq : partitionNumber G = balancedThreshold (Fintype.card V) := by omega
  obtain ⟨P, hPw⟩ := exists_weighted_partition G
  have hmin := partitionNumber_le P
  have hlarge := P.two_count_add_large_le_weight
  have hcount : P.count = balancedThreshold (Fintype.card V) := by omega
  have hzero : P.largeBlocks.card = 0 := by omega
  have hempty : P.largeBlocks = ∅ := Finset.card_eq_zero.mp hzero
  have htwo : ∀ C ∈ P.blocks, C.card = 2 := by
    intro C hC
    have hlo := P.nontrivial C hC
    have hnot : ¬ 3 ≤ C.card := by
      intro hthree
      have hmem : C ∈ P.largeBlocks := Finset.mem_filter.mpr ⟨hC, hthree⟩
      rw [hempty] at hmem
      simp at hmem
    omega
  have hedge : edgeCount G = P.count := by
    rw [P.edgeCount_eq_sum_choose]
    calc
      ∑ C ∈ P.blocks, C.card.choose 2 = ∑ _C ∈ P.blocks, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro C hC
        rw [htwo C hC]
        norm_num
      _ = P.count := by simp [CliquePartition.count]
  omega

/-- Pure integer conversion after strictness and the uniform real saving. -/
theorem integer_saving_of_real {n e p : ℕ}
    (hp : p ≤ balancedThreshold n)
    (hstrict : balancedThreshold n < e → p < balancedThreshold n)
    (hsaving : (e : ℝ) - (n : ℝ)^2 / 4 ≤
      2500 * ((n : ℝ)^2 / 4 - p)) :
    5000 * p + e ≤ 5001 * balancedThreshold n := by
  by_cases he : e ≤ balancedThreshold n
  · omega
  · have he' : balancedThreshold n < e := lt_of_not_ge he
    have hp' := hstrict he'
    obtain ⟨hfloor, herror⟩ := square_quarter_floor_bounds n
    have hpR : (p : ℝ) + 1 ≤ balancedThreshold n := by
      exact_mod_cast (show p + 1 ≤ balancedThreshold n by omega)
    have hbound : (e : ℝ) - balancedThreshold n ≤
        5000 * ((balancedThreshold n : ℝ) - p) := by linarith
    have hfinal : (5000 : ℝ) * p + e ≤ 5001 * balancedThreshold n := by linarith
    exact_mod_cast hfinal

end Erdos1017
