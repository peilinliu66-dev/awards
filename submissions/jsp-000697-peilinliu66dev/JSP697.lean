/-
JSP-000697 / Erdos problem 841 -- the original density-zero question.

Target: Lean 4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

Mathematical attribution: the problem is due to Erdos, Graham, Granville
and Selfridge. Bui--Pratt--Zaharescu (arXiv:2211.12467; 2024 publication)
proved a substantially stronger distribution theorem. The proof below
only claims the complete ORIGINAL near-linear exceptional-set question;
it does not claim their Dickman distribution theorem or the later sharp
pointwise estimates. No mathematical priority is claimed.

Proof: the four corners of a multiplicative rectangle, a least divisor,
Chebyshev's theta upper bound, and the elementary harmonic-sum bound.

STATUS: locally compiled with the pinned toolchain, 2026-09-17.
Terminal axiom reports contain only propext, Classical.choice, Quot.sound.
There are no admitted lemmas and no additional mathematical hypotheses.
-/
import Mathlib

open Finset Filter
open scoped Classical Topology

namespace JSP697

noncomputable section

/-! ## The exact delay, with distinct following integers -/

/-- `t` is admissible when a subset of the distinct integers in `(n,n+t]`
completes `n` to a square. The empty set is permitted, as required for
square `n`, for which the least delay is zero. -/
def Admissible (n t : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Ioc n (n + t) ∧ IsSquare (n * ∏ a ∈ S, a)

lemma admissible_of_square {n : ℕ} (h : IsSquare n) (t : ℕ) :
    Admissible n t := by
  refine ⟨∅, Finset.empty_subset _, ?_⟩
  simpa using h

lemma exists_admissible (n : ℕ) : ∃ t : ℕ, Admissible n t := by
  by_cases hn : n = 0
  · subst n
    exact ⟨0, admissible_of_square (by exact ⟨0, by simp⟩) 0⟩
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    refine ⟨3 * n, {4 * n}, ?_, ?_⟩
    · intro a ha
      have ha' : a = 4 * n := Finset.mem_singleton.mp ha
      subst a
      apply Finset.mem_Ioc.mpr
      constructor <;> omega
    · refine ⟨2 * n, ?_⟩
      simp only [Finset.prod_singleton]
      ring

/-- The least delay, not an arbitrary upper-bound surrogate. -/
def delay (n : ℕ) : ℕ := Nat.find (exists_admissible n)

lemma delay_spec (n : ℕ) : Admissible n (delay n) :=
  Nat.find_spec (exists_admissible n)

lemma delay_le {n t : ℕ} (h : Admissible n t) : delay n ≤ t :=
  Nat.find_min' (exists_admissible n) h

lemma delay_eq_zero_of_square {n : ℕ} (h : IsSquare n) : delay n = 0 := by
  exact Nat.eq_zero_of_le_zero (delay_le (admissible_of_square h 0))

lemma delay_eq_zero_iff (n : ℕ) : delay n = 0 ↔ IsSquare n := by
  constructor
  · intro h
    obtain ⟨S, hS, hs⟩ := delay_spec n
    rw [h, Nat.add_zero] at hS
    have hS0 : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have hmem := Finset.mem_Ioc.mp (hS ha)
      omega
    simpa [hS0] using hs
  · exact delay_eq_zero_of_square

/-- A uniform constructive bound from the four corners of a rectangle. -/
theorem delay_mul_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    delay (a * b) ≤ a + b + 1 := by
  by_cases hab : a = b
  · subst b
    rw [delay_eq_zero_of_square (show IsSquare (a * a) from ⟨a, rfl⟩)]
    omega
  · let A := a * (b + 1)
    let B := (a + 1) * b
    let C := (a + 1) * (b + 1)
    have hAB : A ≠ B := by
      dsimp [A, B]
      intro h
      apply hab
      nlinarith
    have hAC : A ≠ C := by
      dsimp [A, C]
      nlinarith
    have hBC : B ≠ C := by
      dsimp [B, C]
      nlinarith
    apply delay_le
    refine ⟨{A, B, C}, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      all_goals
        apply Finset.mem_Ioc.mpr
        dsimp [A, B, C]
        constructor <;> nlinarith
    · refine ⟨a * b * (a + 1) * (b + 1), ?_⟩
      simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
        hAB, hAC, hBC, or_self, not_false_eq_true, Finset.prod_singleton]
      dsimp [A, B, C]
      ring

/-! ## A least-divisor alternative, with no smooth-number theorem -/

/-- If no balanced factorization can give a sufficiently short rectangle,
then `n` is a prime times a cofactor smaller than `Y^2`. -/
theorem small_cofactor_of_large_delay (n Y : ℕ)
    (hY : 2 ≤ Y) (hYn : Y ≤ n)
    (hlarge : 2 * n + Y < delay n * Y) :
    ∃ m p : ℕ, 0 < m ∧ m < Y ^ 2 ∧ p.Prime ∧ n = m * p := by
  have hn : 0 < n := by omega
  have hex : ∃ d : ℕ, Y ≤ d ∧ d ∣ n := ⟨n, hYn, dvd_rfl⟩
  let d := Nat.find hex
  have hd : Y ≤ d ∧ d ∣ n := Nat.find_spec hex
  have hdpos : 0 < d := by omega
  obtain ⟨b, hnb⟩ := hd.2
  have hbpos : 0 < b := by
    by_contra hb
    have hb0 : b = 0 := by omega
    simp [hb0] at hnb
    omega
  have hbY : b < Y := by
    by_contra hbY
    have hYb : Y ≤ b := by omega
    have ht : delay n ≤ d + b + 1 := by
      rw [hnb]
      exact delay_mul_le d b hdpos hbpos
    have hmul := Nat.mul_le_mul_right Y ht
    have hdb := Nat.mul_le_mul_left d hYb
    have hbd := Nat.mul_le_mul_left b hd.1
    nlinarith [hnb]
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
  obtain ⟨c, hdc⟩ := hpd
  have hcpos : 0 < c := by
    by_contra hc
    have hc0 : c = 0 := by omega
    simp [hc0] at hdc
    omega
  have hcd : c < d := by nlinarith [hp.two_le]
  have hcn : c ∣ n := by
    refine ⟨p * b, ?_⟩
    rw [hnb, hdc]
    ring
  have hcY : c < Y := by
    by_contra hcY
    have hYc : Y ≤ c := by omega
    exact (Nat.find_min hex hcd) ⟨hYc, hcn⟩
  refine ⟨b * c, p, Nat.mul_pos hbpos hcpos, ?_, hp, ?_⟩
  · calc
      b * c ≤ b * Y := Nat.mul_le_mul_left b hcY.le
      _ < Y * Y := Nat.mul_lt_mul_of_pos_right hbY (by omega)
      _ = Y ^ 2 := by ring
  · rw [hnb, hdc]
    ring

/-! ## Elementary natural-power helpers -/

lemma pow_mono_exponent {q i j : ℕ} (hq : 1 ≤ q) (hij : i ≤ j) :
    q ^ i ≤ q ^ j := by
  have hp : 1 ≤ q ^ (j - i) := by
    have := pow_pos (show 0 < q by omega) (j - i)
    omega
  calc
    q ^ i = q ^ i * 1 := by omega
    _ ≤ q ^ i * q ^ (j - i) := Nat.mul_le_mul_left _ hp
    _ = q ^ j := by
      rw [← pow_add]
      congr 1
      omega

lemma self_le_pow (q k : ℕ) (hq : 1 ≤ q) (hk : 1 ≤ k) : q ≤ q ^ k := by
  simpa only [pow_one] using (pow_mono_exponent hq hk : q ^ 1 ≤ q ^ k)

/-- An integer floor-root construction valid for every ambient cutoff. -/
lemma exists_power_bracket (m B N : ℕ) (hm : 0 < m) (hBN : B ^ m ≤ N) :
    ∃ q : ℕ, B ≤ q ∧ q ^ m ≤ N ∧ N < (q + 1) ^ m := by
  have hex : ∃ z : ℕ, N < (z + 1) ^ m := by
    refine ⟨N, ?_⟩
    exact (Nat.lt_succ_self N).trans_le (self_le_pow (N + 1) m (by omega) hm)
  let q := Nat.find hex
  have hq : N < (q + 1) ^ m := Nat.find_spec hex
  have hBq : B ≤ q := by
    by_contra h
    have h' : q + 1 ≤ B := by omega
    have hp : (q + 1) ^ m ≤ B ^ m := by gcongr
    omega
  have hqp : q ^ m ≤ N := by
    by_cases h0 : q = 0
    · simp [h0, Nat.ne_of_gt hm]
    · have hprev : q - 1 < q := by omega
      have hmin := Nat.find_min hex hprev
      have hsucc : q - 1 + 1 = q := by omega
      rw [hsucc] at hmin
      omega
  exact ⟨q, hBq, hqp, hq⟩

lemma grid_delay_large (k q n N : ℕ) (hk : 7 ≤ k)
    (hq : 2 ^ (k + 2) + 2 ≤ q)
    (hn : n ≤ N) (hN : N < (q + 1) ^ (k + 1))
    (ht : q ^ (k - 1) ≤ delay n) :
    2 * n + q ^ 3 < delay n * q ^ 3 := by
  have hq2 : 2 ≤ q := by
    have hpow : 0 ≤ (2 : ℕ) ^ (k + 2) := Nat.zero_le _
    omega
  have hqpos : 0 < q := by omega
  have hqone : 1 ≤ q := by omega
  have hN' : N ≤ 2 ^ (k + 1) * q ^ (k + 1) := by
    calc
      N ≤ (q + 1) ^ (k + 1) := hN.le
      _ ≤ (2 * q) ^ (k + 1) := by gcongr <;> omega
      _ = _ := by rw [mul_pow]
  have hq3 : q ^ 3 ≤ q ^ (k + 1) := pow_mono_exponent hqone (by omega)
  have htwo : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    ring
  have hu : 2 * n + q ^ 3 ≤ (2 ^ (k + 2) + 1) * q ^ (k + 1) := by
    rw [htwo]
    nlinarith
  have hl : (2 ^ (k + 2) + 1) * q ^ (k + 1) < q ^ (k + 2) := by
    calc
      (2 ^ (k + 2) + 1) * q ^ (k + 1) < q * q ^ (k + 1) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hqpos _)
      _ = q ^ (k + 2) := by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        ring
  have ht' : q ^ (k + 2) ≤ delay n * q ^ 3 := by
    calc
      q ^ (k + 2) = q ^ (k - 1) * q ^ 3 := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ delay n * q ^ 3 := Nat.mul_le_mul_right _ ht
  exact (hu.trans_lt hl).trans_le ht'

/-! ## Prime covers and their unconditional logarithmic counting bound -/

/-- Primes in `[L,N/m]`. -/
def primeSlice (N L m : ℕ) : Finset ℕ :=
  (N / m).primesLE.filter (fun p => L ≤ p)

/-- All integers at most `N` representable as a prime at least `L`
times a positive cofactor at most `M`. Duplicates are counted only once. -/
def primeCover (N L M : ℕ) : Finset ℕ :=
  (Icc 1 M).biUnion (fun m => (primeSlice N L m).image (fun p => m * p))

lemma mem_primeCover (N L M m p : ℕ)
    (hm : 0 < m) (hmM : m ≤ M) (hp : p.Prime)
    (hLp : L ≤ p) (hmp : m * p ≤ N) : m * p ∈ primeCover N L M := by
  apply Finset.mem_biUnion.mpr
  refine ⟨m, Finset.mem_Icc.mpr ⟨hm, hmM⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨p, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_, hp⟩, hLp⟩
  exact (Nat.le_div_iff_mul_le hm).mpr (by simpa [Nat.mul_comm] using hmp)

lemma primeSlice_weighted (N L m : ℕ) (hm : 0 < m) (hL : 0 < L) :
    ((primeSlice N L m).card : ℝ) * Real.log L ≤
      Real.log 4 * (N : ℝ) / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hL_R : (0 : ℝ) < L := by exact_mod_cast hL
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hdiv : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
    apply (le_div_iff₀ hmR).mpr
    exact_mod_cast (Nat.div_mul_le_self N m)
  calc
    ((primeSlice N L m).card : ℝ) * Real.log L =
        ∑ p ∈ primeSlice N L m, Real.log L := by simp
    _ ≤ ∑ p ∈ primeSlice N L m, Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      have hLp : L ≤ p := (Finset.mem_filter.mp hp).2
      exact Real.log_le_log hL_R (by exact_mod_cast hLp)
    _ ≤ ∑ p ∈ (N / m).primesLE, Real.log p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp _
      have hp1 : 1 ≤ p := (Nat.mem_primesLE.mp hp).2.one_le
      exact Real.log_nonneg (by exact_mod_cast hp1)
    _ = Chebyshev.theta (N / m : ℕ) :=
      (Chebyshev.theta_eq_sum_primesLE_log (N / m)).symm
    _ ≤ Real.log 4 * ((N / m : ℕ) : ℝ) :=
      Chebyshev.theta_le_log4_mul_x (by positivity)
    _ ≤ Real.log 4 * ((N : ℝ) / (m : ℝ)) := mul_le_mul_of_nonneg_left hdiv hlog4
    _ = Real.log 4 * (N : ℝ) / (m : ℝ) := by ring

lemma harmonic_sum_bound (M : ℕ) :
    (∑ m ∈ Icc 1 M, (m : ℝ)⁻¹) ≤ 1 + Real.log M := by
  simpa [harmonic_eq_sum_Icc] using (harmonic_le_one_add_log M)

lemma card_biUnion_bound (s : Finset ℕ) (f : ℕ → Finset ℕ) :
    (s.biUnion f).card ≤ ∑ a ∈ s, (f a).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)

/-- This is a finite inequality, derived from the actual Chebyshev theorem
in Mathlib, not supplied as an analytic hypothesis. -/
theorem primeCover_weighted (N L M : ℕ) (hL : 1 ≤ L) :
    ((primeCover N L M).card : ℝ) * Real.log L ≤
      Real.log 4 * (N : ℝ) * (1 + Real.log M) := by
  classical
  have hcard : (primeCover N L M).card ≤
      ∑ m ∈ Icc 1 M, (primeSlice N L m).card := by
    calc
      (primeCover N L M).card ≤
          ∑ m ∈ Icc 1 M, ((primeSlice N L m).image (fun p => m * p)).card :=
        card_biUnion_bound _ _
      _ ≤ ∑ m ∈ Icc 1 M, (primeSlice N L m).card := by
        apply Finset.sum_le_sum
        intro m hm
        exact Finset.card_image_le
  have hcardR : ((primeCover N L M).card : ℝ) ≤
      ∑ m ∈ Icc 1 M, ((primeSlice N L m).card : ℝ) := by
    exact_mod_cast hcard
  have hlogL : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hL)
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  calc
    ((primeCover N L M).card : ℝ) * Real.log L ≤
        (∑ m ∈ Icc 1 M, ((primeSlice N L m).card : ℝ)) * Real.log L :=
      mul_le_mul_of_nonneg_right hcardR hlogL
    _ = ∑ m ∈ Icc 1 M, ((primeSlice N L m).card : ℝ) * Real.log L :=
      by rw [Finset.sum_mul]
    _ ≤ ∑ m ∈ Icc 1 M, Real.log 4 * (N : ℝ) / (m : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      exact primeSlice_weighted N L m (Finset.mem_Icc.mp hm).1 (by omega)
    _ = (Real.log 4 * (N : ℝ)) * (∑ m ∈ Icc 1 M, (m : ℝ)⁻¹) := by
      simp only [div_eq_mul_inv, Finset.mul_sum]
    _ ≤ (Real.log 4 * (N : ℝ)) * (1 + Real.log M) :=
      mul_le_mul_of_nonneg_left (harmonic_sum_bound M) (mul_nonneg hlog4 (by positivity))

lemma one_le_log_of_four_le {q : ℕ} (hq : 4 ≤ q) : 1 ≤ Real.log (q : ℝ) := by
  have hhalf : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num)
      (show (2 : ℝ) ≠ 0 by norm_num)
    norm_num at h
    linarith
  have hmono : Real.log (4 : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  linarith

lemma primeCover_grid_bound (N k q : ℕ) (hk : 7 ≤ k) (hq : 4 ≤ q) :
    ((primeCover N (q ^ (k - 6)) (q ^ 6)).card : ℝ) * (k - 6 : ℕ) ≤
      21 * (N : ℝ) := by
  have hq2 : 2 ≤ q := by
    have hpow : 0 ≤ (2 : ℕ) ^ (k + 2) := Nat.zero_le _
    omega
  have hqpos : 0 < q := by omega
  have hL : 1 ≤ q ^ (k - 6) := by
    have := pow_pos hqpos (k - 6)
    omega
  have h := primeCover_weighted N (q ^ (k - 6)) (q ^ 6) hL
  have hlog : 1 ≤ Real.log (q : ℝ) := one_le_log_of_four_le hq
  have hlogpos : 0 < Real.log (q : ℝ) := by linarith
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    have h4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at h4
    exact h4
  have hlog4nonneg : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hpowL : Real.log ((q ^ (k - 6) : ℕ) : ℝ) =
      (k - 6 : ℕ) * Real.log (q : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  have hpowM : Real.log ((q ^ 6 : ℕ) : ℝ) = 6 * Real.log (q : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hpowL, hpowM] at h
  have h1 : Real.log 4 * (N : ℝ) * (1 + 6 * Real.log (q : ℝ)) ≤
      3 * (N : ℝ) * (1 + 6 * Real.log (q : ℝ)) := by gcongr
  have h2 : 3 * (N : ℝ) * (1 + 6 * Real.log (q : ℝ)) ≤
      21 * (N : ℝ) * Real.log (q : ℝ) := by
    have hl : 1 + 6 * Real.log (q : ℝ) ≤ 7 * Real.log (q : ℝ) := by linarith
    calc
      3 * (N : ℝ) * (1 + 6 * Real.log (q : ℝ)) ≤
          3 * (N : ℝ) * (7 * Real.log (q : ℝ)) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ = 21 * (N : ℝ) * Real.log (q : ℝ) := by ring
  have hc : Real.log (q : ℝ) *
      (((primeCover N (q ^ (k - 6)) (q ^ 6)).card : ℝ) * (k - 6 : ℕ)) ≤
      Real.log (q : ℝ) * (21 * (N : ℝ)) := by
    nlinarith [h.trans (h1.trans h2)]
  exact (mul_le_mul_iff_right₀ hlogpos).mp hc

/-! ## Full exceptional-set counting on every sufficiently large cutoff -/

def countPrefix (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => n ∈ A)

/-- Precise meaning of `t_n >= n^(1-o(1))` along an arbitrary set A. -/
def NearlyLinearOn (A : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → n ∈ A →
    (n : ℝ) ^ (1 - ε) ≤ (delay n : ℝ)

/-- Natural density zero, in the full epsilon/eventual-cutoff formulation. -/
def DensityZero (A : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ((countPrefix A N).card : ℝ) < ε * (N : ℝ)

lemma high_member_in_primeCover (A : Set ℕ) (N k q : ℕ)
    (hk : 7 ≤ k) (hq : 2 ^ (k + 2) + 2 ≤ q)
    (hN : N < (q + 1) ^ (k + 1))
    (ht : ∀ n : ℕ, n ∈ A → q ^ k ≤ n → q ^ (k - 1) ≤ delay n)
    {n : ℕ} (hn : n ∈ countPrefix A N) (hhigh : q ^ k ≤ n) :
    n ∈ primeCover N (q ^ (k - 6)) (q ^ 6) := by
  obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnI
  have hq2 : 2 ≤ q := by
    have hpow : 0 ≤ (2 : ℕ) ^ (k + 2) := Nat.zero_le _
    omega
  have hqpos : 0 < q := by omega
  have hqone : 1 ≤ q := by omega
  have hq3 : 2 ≤ q ^ 3 := by
    have hself := self_le_pow q 3 hqone (by omega)
    omega
  have hq3n : q ^ 3 ≤ n :=
    (pow_mono_exponent hqone (show 3 ≤ k by omega)).trans hhigh
  have hlarge := grid_delay_large k q n N hk hq hnN hN (ht n hnA hhigh)
  obtain ⟨m, p, hm, hm6, hp, hnmp⟩ :=
    small_cofactor_of_large_delay n (q ^ 3) hq3 hq3n hlarge
  have hm6' : m < q ^ 6 := by
    simpa only [← pow_mul] using hm6
  have hLp : q ^ (k - 6) ≤ p := by
    by_contra hLp
    have hpL : p < q ^ (k - 6) := by omega
    have hcontr : n < q ^ k := by
      calc
        n = m * p := hnmp
        _ ≤ q ^ 6 * p := Nat.mul_le_mul_right p hm6'.le
        _ < q ^ 6 * q ^ (k - 6) :=
          Nat.mul_lt_mul_of_pos_left hpL (pow_pos hqpos 6)
        _ = q ^ k := by
          rw [← pow_add]
          congr 1
          omega
    omega
  rw [hnmp]
  apply mem_primeCover N (q ^ (k - 6)) (q ^ 6) m p hm hm6'.le hp hLp
  omega

/-- A uniform bound tending to zero by first choosing k, then the cutoff:
`density <= 1/q + 21/(k-6)` whenever `q^(k+1) <= N < (q+1)^(k+1)`. -/
theorem grid_density_bound (A : Set ℕ) (N k q : ℕ)
    (hk : 7 ≤ k) (hq4 : 4 ≤ q) (hq : 2 ^ (k + 2) + 2 ≤ q)
    (hNlo : q ^ (k + 1) ≤ N) (hNhi : N < (q + 1) ^ (k + 1))
    (ht : ∀ n : ℕ, n ∈ A → q ^ k ≤ n → q ^ (k - 1) ≤ delay n) :
    ((countPrefix A N).card : ℝ) / (N : ℝ) ≤
      1 / (q : ℝ) + 21 / (k - 6 : ℕ) := by
  have hq2 : 2 ≤ q := by
    have hpow : 0 ≤ (2 : ℕ) ^ (k + 2) := Nat.zero_le _
    omega
  have hqpos : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hNpos : 0 < N := lt_of_lt_of_le (pow_pos hqpos _) hNlo
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hd : (0 : ℝ) < (k - 6 : ℕ) := by exact_mod_cast (show 0 < k - 6 by omega)
  have hsub : countPrefix A N ⊆ (range (q ^ k)) ∪ primeCover N (q ^ (k - 6)) (q ^ 6) := by
    intro n hn
    by_cases hsmall : n < q ^ k
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr hsmall))
    · exact Finset.mem_union.mpr (Or.inr
        (high_member_in_primeCover A N k q hk hq hNhi ht hn (by omega)))
  have hcard : (countPrefix A N).card ≤ q ^ k +
      (primeCover N (q ^ (k - 6)) (q ^ 6)).card := by
    calc
      (countPrefix A N).card ≤ ((range (q ^ k)) ∪ primeCover N (q ^ (k - 6)) (q ^ 6)).card :=
        Finset.card_le_card hsub
      _ ≤ q ^ k + (primeCover N (q ^ (k - 6)) (q ^ 6)).card := by
        simpa only [Finset.card_range] using
          (Finset.card_union_le (range (q ^ k)) (primeCover N (q ^ (k - 6)) (q ^ 6)))
  have hcardR : ((countPrefix A N).card : ℝ) ≤ (q : ℝ) ^ k +
      ((primeCover N (q ^ (k - 6)) (q ^ 6)).card : ℝ) := by exact_mod_cast hcard
  have hfirst : (q : ℝ) ^ k / (N : ℝ) ≤ 1 / (q : ℝ) := by
    apply (div_le_div_iff₀ hNR hqR).mpr
    have hpower : q ^ k * q ≤ N := by simpa only [pow_succ] using hNlo
    simp only [one_mul]
    exact_mod_cast hpower
  have hsecond : ((primeCover N (q ^ (k - 6)) (q ^ 6)).card : ℝ) / (N : ℝ) ≤
      21 / (k - 6 : ℕ) := by
    exact (div_le_div_iff₀ hNR hd).mpr (primeCover_grid_bound N k q hk hq4)
  calc
    ((countPrefix A N).card : ℝ) / (N : ℝ) ≤
        ((q : ℝ) ^ k + ((primeCover N (q ^ (k - 6)) (q ^ 6)).card : ℝ)) / (N : ℝ) :=
      div_le_div_of_nonneg_right hcardR hNR.le
    _ = (q : ℝ) ^ k / (N : ℝ) +
        ((primeCover N (q ^ (k - 6)) (q ^ 6)).card : ℝ) / (N : ℝ) := by ring
    _ ≤ 1 / (q : ℝ) + 21 / (k - 6 : ℕ) := add_le_add hfirst hsecond

lemma rpow_grid_lower (k q n : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q)
    (hn : q ^ k ≤ n) :
    ((q ^ (k - 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 - 1 / (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsub : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel hk)
  have he : 1 - 1 / (k : ℝ) = ((k - 1 : ℕ) : ℝ) / (k : ℝ) := by
    apply (eq_div_iff (ne_of_gt hkR)).mpr
    field_simp [ne_of_gt hkR] <;> nlinarith
  rw [he]
  have heval : (((q : ℝ) ^ k) ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ))) =
      (q : ℝ) ^ (k - 1) := by
    rw [← Real.rpow_natCast (q : ℝ) k, ← Real.rpow_mul (by positivity)]
    have he' : (k : ℝ) * (((k - 1 : ℕ) : ℝ) / (k : ℝ)) = (k - 1 : ℕ) := by
      field_simp [ne_of_gt hkR]
    rw [he', Real.rpow_natCast]
  have hnR : (q : ℝ) ^ k ≤ (n : ℝ) := by exact_mod_cast hn
  calc
    ((q ^ (k - 1) : ℕ) : ℝ) = (q : ℝ) ^ (k - 1) := by norm_cast
    _ = ((q : ℝ) ^ k) ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ)) := heval.symm
    _ ≤ (n : ℝ) ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ)) :=
      Real.rpow_le_rpow (by positivity) hnR (by positivity)

/-- COMPLETE ORIGINAL DENSITY-ZERO STATEMENT for an arbitrary exceptional
set, with all epsilon and eventual-cutoff quantifiers. -/
theorem density_zero_of_nearly_linear (A : Set ℕ) (hA : NearlyLinearOn A) :
    DensityZero A := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (42 / ε + 7)
  have h42 : (0 : ℝ) < 42 / ε := by positivity
  have hk7R : (7 : ℝ) < k := by linarith
  have hk7 : 7 ≤ k := by exact_mod_cast hk7R.le
  have hkposR : (0 : ℝ) < k := by linarith
  have hcastd : ((k - 6 : ℕ) : ℝ) + 6 = (k : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel (show 6 ≤ k by omega))
  have hdR : (0 : ℝ) < (k - 6 : ℕ) := by linarith
  have hkd : (42 : ℝ) / ε < (k - 6 : ℕ) := by linarith
  have hprod : (42 : ℝ) < ((k - 6 : ℕ) : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hkd
  have hterm2 : (21 : ℝ) / (k - 6 : ℕ) < ε / 2 := by
    apply (div_lt_iff₀ hdR).mpr
    nlinarith
  obtain ⟨N₀, hN₀⟩ := hA (1 / (k : ℝ)) (by positivity)
  obtain ⟨R, hR⟩ := exists_nat_gt (2 / ε)
  let B := max (max N₀ (2 ^ (k + 2) + 2)) (max 4 R)
  refine ⟨B ^ (k + 1), ?_⟩
  intro N hN
  obtain ⟨q, hBq, hNlo, hNhi⟩ := exists_power_bracket (k + 1) B N (by omega) hN
  have hN₀q : N₀ ≤ q :=
    (le_max_left N₀ (2 ^ (k + 2) + 2)).trans ((le_max_left _ _).trans hBq)
  have hq : 2 ^ (k + 2) + 2 ≤ q :=
    (le_max_right N₀ (2 ^ (k + 2) + 2)).trans ((le_max_left _ _).trans hBq)
  have hq4 : 4 ≤ q :=
    (le_max_left 4 R).trans ((le_max_right _ _).trans hBq)
  have hRq : R ≤ q :=
    (le_max_right 4 R).trans ((le_max_right _ _).trans hBq)
  have hq2 : 2 ≤ q := by
    have hpow : 0 ≤ (2 : ℕ) ^ (k + 2) := Nat.zero_le _
    omega
  have hqpos : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hReq : (R : ℝ) ≤ q := by exact_mod_cast hRq
  have hqeps : (2 : ℝ) / ε < q := hR.trans_le hReq
  have hprodq : (2 : ℝ) < (q : ℝ) * ε := (div_lt_iff₀ hε).mp hqeps
  have hterm1 : (1 : ℝ) / q < ε / 2 := by
    apply (div_lt_iff₀ hqR).mpr
    nlinarith
  have ht : ∀ n : ℕ, n ∈ A → q ^ k ≤ n → q ^ (k - 1) ≤ delay n := by
    intro n hnA hn
    have hqn : q ≤ n := (self_le_pow q k (by omega) (by omega)).trans hn
    have hnear := hN₀ n (hN₀q.trans hqn) hnA
    have hgrid := rpow_grid_lower k q n (by omega) (by omega) hn
    have hreal := hgrid.trans hnear
    exact_mod_cast hreal
  have hbound := grid_density_bound A N k q hk7 hq4 hq hNlo hNhi ht
  have hNpos : 0 < N := lt_of_lt_of_le (pow_pos hqpos _) hNlo
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  apply (div_lt_iff₀ hNR).mp
  linarith

/-- The arbitrary-function formulation of the original `n^(1-o(1))`
question. No nonnegativity or monotonicity assumption on eta is needed. -/
theorem erdos_841 (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0)) :
    DensityZero {n : ℕ | 2 ≤ n ∧ (n : ℝ) ^ (1 - η n) ≤ (delay n : ℝ)} := by
  apply density_zero_of_nearly_linear
  intro ε hε
  have hevent : ∀ᶠ n : ℕ in atTop, η n < ε := hη.eventually (gt_mem_nhds hε)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨N₀, ?_⟩
  intro n hn hnA
  have hn2 : 2 ≤ n := hnA.1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  calc
    (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (1 - η n) :=
      Real.rpow_le_rpow_of_exponent_le hnR (by linarith [hN₀ n hn])
    _ ≤ (delay n : ℝ) := hnA.2

/-- The epsilon formulation is the ordinary natural-density limit. -/
theorem densityZero_tendsto {A : Set ℕ} (hA : DensityZero A) :
    Tendsto (fun N : ℕ => ((countPrefix A N).card : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hA ε hε
  refine ⟨max N₀ 1, ?_⟩
  intro N hN
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnonneg : 0 ≤ ((countPrefix A N).card : ℝ) / (N : ℝ) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact (div_lt_iff₀ hNR).mpr (hN₀ N hN0)

/-- The original arbitrary-o(1) question as an actual limit, with the
least delay defined above and no auxiliary analytic assumptions. -/
theorem erdos_841_limit (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (((Icc (1 : ℕ) N).filter (fun n : ℕ =>
        2 ≤ n ∧ (n : ℝ) ^ (1 - η n) ≤ (delay n : ℝ))).card : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  simpa only [countPrefix, Set.mem_ofPred_eq] using densityZero_tendsto (erdos_841 η hη)

/-- Explicit terminal quantifiers, without a wrapper around the statement. -/
theorem erdos_841_full_original :
    ∀ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) →
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((Icc (1 : ℕ) N).filter (fun n : ℕ =>
          2 ≤ n ∧ (n : ℝ) ^ (1 - η n) ≤ (delay n : ℝ))).card : ℝ) <
          ε * (N : ℝ) := by
  intro η hη
  simpa only [DensityZero, countPrefix, Set.mem_ofPred_eq] using erdos_841 η hη

end

#print axioms JSP697.delay_mul_le
#print axioms JSP697.density_zero_of_nearly_linear
#print axioms JSP697.erdos_841_full_original
#print axioms JSP697.erdos_841_limit

end JSP697
