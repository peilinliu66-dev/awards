/-
JSP-000356 / Erdos 437: proof of the full lower endpoint.

Requires JSP356Finite.lean in the same Lean project.
Target: Lean 4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

The complete project is locally checked with the pinned Lean toolchain.
The accompanying density-zero upper theorem is formalized in
Erdos437Upper.lean and JSP356UpperBridge.lean; Proof.lean combines both.

Known mathematical solution: Bui--Pratt--Zaharescu (2024), as explained
by Tao on 9 August 2024.  No new-solution priority is claimed.
-/
import JSP356Finite

open Finset Filter
open scoped Classical Topology

namespace JSP356

noncomputable section

/-- Every fixed power of log is eventually at most c times n. -/
lemma eventually_nat_log_pow (k : ℕ) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ)) ^ k ≤ c * (n : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ)
    (show (0 : ℝ) < 1 by norm_num)).bound hc
  have hn := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually h
  filter_upwards [hn, eventually_ge_atTop (1 : ℕ)] with n h hn
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  simpa only [Real.rpow_natCast, Real.rpow_one,
    Real.norm_of_nonneg (pow_nonneg hlog k),
    Real.norm_of_nonneg (Nat.cast_nonneg n)] using h

/-- A deliberately weak integer-power form of the Chebyshev lower bound.
It is strong enough for every epsilon in the original question. -/
theorem eventually_prime_count_pow (k : ℕ) :
    ∀ᶠ y : ℕ in atTop, y ^ k ≤ (Nat.primeCounting y) ^ (k + 1) := by
  let c : ℝ := Real.log 2 / 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (eventually_nat_log_pow 1 (Real.log 2 / 4) (by positivity))
  have hp := eventually_nat_log_pow (k + 1) (c ^ (k + 1)) (by positivity)
  filter_upwards [hp, eventually_ge_atTop Y,
    eventually_ge_atTop (2 : ℕ)] with y hpower hYy hy
  have hyR : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hy1R : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos hy1R
  have herr0 := hY (y + 1) (by omega)
  simp only [pow_one, Nat.cast_add, Nat.cast_one] at herr0
  have herr : Real.log ((y : ℝ) + 1) ≤ c * y := by
    dsimp [c]
    nlinarith
  have hcheb := (div_le_iff₀ hlog).mp (chebyshev_input y)
  have hlinear : c * y ≤ (Nat.primeCounting y : ℝ) * Real.log (y : ℝ) := by
    dsimp [c] at herr ⊢
    nlinarith
  have hpow : (c * y) ^ (k + 1) ≤
      ((Nat.primeCounting y : ℝ) * Real.log (y : ℝ)) ^ (k + 1) := by
    gcongr
  rw [mul_pow, mul_pow] at hpow
  have hright := mul_le_mul_of_nonneg_left hpower
    (show (0 : ℝ) ≤ (Nat.primeCounting y : ℝ) ^ (k + 1) by positivity)
  have hcross : c ^ (k + 1) * (y : ℝ) ^ (k + 1) ≤
      c ^ (k + 1) * ((Nat.primeCounting y : ℝ) ^ (k + 1) * y) := by
    calc
      _ ≤ (Nat.primeCounting y : ℝ) ^ (k + 1) *
          Real.log (y : ℝ) ^ (k + 1) := hpow
      _ ≤ (Nat.primeCounting y : ℝ) ^ (k + 1) * (c ^ (k + 1) * y) := hright
      _ = _ := by ring
  have hcancel : (y : ℝ) ^ (k + 1) ≤
      (Nat.primeCounting y : ℝ) ^ (k + 1) * y := by
    by_contra h
    exact (not_lt_of_ge hcross)
      (mul_lt_mul_of_pos_left (lt_of_not_ge h) (pow_pos hc (k + 1)))
  rw [pow_succ] at hcancel
  have hfinal : (y : ℝ) ^ k ≤ (Nat.primeCounting y : ℝ) ^ (k + 1) :=
    (mul_le_mul_iff_left₀ hyR).mp hcancel
  exact_mod_cast hfinal

lemma prime_count_le_self (y : ℕ) : Nat.primeCounting y ≤ y := by
  calc
    Nat.primeCounting y = (Nat.primesLE y).card :=
      by simp only [Nat.primesLE_card_eq_primeCounting]
    _ ≤ (Icc 1 y).card := by
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_Icc.mpr
        ⟨(Nat.prime_of_mem_primesLE hp).one_le, Nat.le_of_mem_primesLE hp⟩
    _ = y := by simp

lemma nat_power_le_factorial_mul_choose (r m : ℕ) :
    (r + 1 - m) ^ m ≤ m.factorial * r.choose m := by
  have h : (((r + 1 - m : ℕ) : ℝ) ^ m) / (m.factorial : ℝ) ≤
      (r.choose m : ℝ) := Nat.pow_le_choose m r
  have h' := (div_le_iff₀ (show (0 : ℝ) < m.factorial by positivity)).mp h
  have h'' : (((r + 1 - m : ℕ) : ℝ) ^ m) ≤
      (m.factorial : ℝ) * (r.choose m : ℝ) := by
    simpa only [mul_comm] using h'
  exact_mod_cast h''

lemma one_le_nat_pow (y k : ℕ) (hy : 1 ≤ y) : 1 ≤ y ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      nlinarith

/-- Integer grid bound.  The four-unit exponent slack makes interpolation
and all epsilon-quantifiers independent of delicate real asymptotics. -/
theorem eventually_grid_lower (k : ℕ) :
    ∀ᶠ y : ℕ in atTop,
      ∃ A : Finset ℕ, A ⊆ Icc 1 (y ^ (k + 4)) ∧
        y ^ (k + 1) < (squareCuts A).card := by
  let m := k + 4
  let C := 2 ^ m * m.factorial
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [eventually_prime_count_pow (k + 3),
    eventually_prime_count_pow 1,
    eventually_ge_atTop ((2 * m) ^ 2),
    eventually_ge_atTop (4 * C), eventually_ge_atTop (2 : ℕ)]
    with y hgrow hgrow1 hbig hCy hy
  let r := Nat.primeCounting y
  have hrle : r ≤ y := prime_count_le_self y
  have hrbig : 2 * m ≤ r := by
    have hgrow1' : y ≤ r ^ 2 := by
      simpa only [pow_one] using hgrow1
    nlinarith
  have htwice : r ≤ 2 * (r + 1 - m) := by omega
  have hrpow : r ^ m ≤ 2 ^ m * (r + 1 - m) ^ m := by
    calc
      r ^ m ≤ (2 * (r + 1 - m)) ^ m := by gcongr
      _ = _ := by rw [mul_pow]
  have hchoose := nat_power_le_factorial_mul_choose r m
  have hmajor : y ^ (k + 3) ≤ C * r.choose m := by
    calc
      y ^ (k + 3) ≤ r ^ m := hgrow
      _ ≤ 2 ^ m * (r + 1 - m) ^ m := hrpow
      _ ≤ 2 ^ m * (m.factorial * r.choose m) := Nat.mul_le_mul_left _ hchoose
      _ = _ := by dsimp [C]; ring
  have hyp : 1 ≤ y ^ (k + 1) := one_le_nat_pow y (k + 1) (by omega)
  have hmul : C * ((y ^ (k + 1) + 1) * (r + 1)) ≤ y ^ (k + 3) := by
    calc
      C * ((y ^ (k + 1) + 1) * (r + 1)) ≤
          C * ((2 * y ^ (k + 1)) * (2 * y)) := by
            gcongr <;> omega
      _ = (4 * C) * y ^ (k + 2) := by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        ring
      _ ≤ y * y ^ (k + 2) := Nat.mul_le_mul_right _ hCy
      _ = y ^ (k + 3) := by
        rw [show k + 3 = (k + 2) + 1 by omega, pow_succ]
        ring
  have hqmul : (y ^ (k + 1) + 1) * (r + 1) ≤ r.choose m := by
    by_contra h
    exact (not_lt_of_ge (hmul.trans hmajor))
      (mul_lt_mul_of_pos_left (lt_of_not_ge h) hC)
  have hquot : y ^ (k + 1) + 1 ≤ r.choose m / (r + 1) :=
    (Nat.le_div_iff_mul_le (Nat.succ_pos r)).mpr hqmul
  obtain ⟨A, hA, hcount⟩ := finite_lower_bound (y ^ m) y m le_rfl
  refine ⟨A, hA, ?_⟩
  change r.choose m / (r + 1) ≤ (squareCuts A).card at hcount
  omega

lemma self_le_nat_pow (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) : n ≤ n ^ k := by
  revert hk
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro hk
      cases k with
      | zero => simp
      | succ k =>
          have hprev : n ≤ n ^ (k + 1) := ih (by omega)
          rw [pow_succ]
          nlinarith

/-- A purely natural-number floor-root construction; no floating-point roots. -/
lemma exists_power_bracket (m B N : ℕ) (hm : 0 < m)
    (hBN : B ^ m ≤ N) :
    ∃ y : ℕ, B ≤ y ∧ y ^ m ≤ N ∧ N < (y + 1) ^ m := by
  have hex : ∃ z : ℕ, N < (z + 1) ^ m := by
    refine ⟨N, ?_⟩
    exact (Nat.lt_succ_self N).trans_le
      (self_le_nat_pow (N + 1) m (by omega) hm)
  let y := Nat.find hex
  have hy : N < (y + 1) ^ m := Nat.find_spec hex
  have hBy : B ≤ y := by
    by_contra h
    have h' : y + 1 ≤ B := by omega
    have hp : (y + 1) ^ m ≤ B ^ m := by gcongr
    omega
  have hyp : y ^ m ≤ N := by
    by_cases h0 : y = 0
    · simp [h0, Nat.ne_of_gt hm]
    · have hprev : y - 1 < y := by omega
      have hmin := Nat.find_min hex hprev
      have hsucc : y - 1 + 1 = y := by omega
      rw [hsucc] at hmin
      omega
  exact ⟨y, hBy, hyp, hy⟩

/-- FULL original Erdos 437 lower question, including every epsilon and
all sufficiently large bounds, not merely a subsequence of bounds.
Uncompiled candidate: see the header before treating this as verified. -/
theorem original_lower_question : OriginalLowerQuestion := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (4 / ε)
  let m := k + 4
  have hm : 0 < m := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hεk : (4 : ℝ) < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
  have hexp : 1 - ε ≤ (k : ℝ) / (m : ℝ) := by
    apply (le_div_iff₀ hmR).mpr
    have hmcast : (m : ℝ) = (k : ℝ) + 4 := by dsimp [m]; norm_cast
    rw [hmcast]
    nlinarith
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (eventually_grid_lower k)
  let B := max Y (2 ^ k + 1)
  refine ⟨B ^ m, ?_⟩
  intro N hN
  obtain ⟨y, hBy, hyp, hupper⟩ := exists_power_bracket m B N hm hN
  have hyY : Y ≤ y := (le_max_left _ _).trans hBy
  have hy2k : 2 ^ k < y := by
    have h := (le_max_right Y (2 ^ k + 1)).trans hBy
    omega
  have hypos : 1 ≤ y :=
    Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le (2 ^ k)) hy2k)
  have hNpos : 1 ≤ N := (one_le_nat_pow y m hypos).trans hyp
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hbase : (N : ℝ) ≤ ((y + 1 : ℕ) : ℝ) ^ m := by
    exact_mod_cast hupper.le
  have hrpow : (((y + 1 : ℕ) : ℝ) ^ m) ^ ((k : ℝ) / (m : ℝ)) =
      ((y + 1 : ℕ) : ℝ) ^ k := by
    rw [← Real.rpow_natCast ((y + 1 : ℕ) : ℝ) m,
      ← Real.rpow_mul (by positivity)]
    have he : (m : ℝ) * ((k : ℝ) / (m : ℝ)) = (k : ℝ) := by
      field_simp [ne_of_gt hmR]
    rw [he, Real.rpow_natCast]
  have hnat : (y + 1) ^ k ≤ y ^ (k + 1) := by
    calc
      (y + 1) ^ k ≤ (2 * y) ^ k := by gcongr <;> omega
      _ = 2 ^ k * y ^ k := by rw [mul_pow]
      _ ≤ y * y ^ k := Nat.mul_le_mul_right _ hy2k.le
      _ = y ^ (k + 1) := by rw [pow_succ]; ring
  have hcomparison : (N : ℝ) ^ (1 - ε) ≤ ((y ^ (k + 1) : ℕ) : ℝ) := by
    calc
      (N : ℝ) ^ (1 - ε) ≤ (N : ℝ) ^ ((k : ℝ) / (m : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hNR hexp
      _ ≤ (((y + 1 : ℕ) : ℝ) ^ m) ^ ((k : ℝ) / (m : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hbase (by positivity)
      _ = ((y + 1 : ℕ) : ℝ) ^ k := hrpow
      _ ≤ ((y ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
  obtain ⟨A, hA, hcount⟩ := hY y hyY
  refine ⟨A, ?_, hcomparison.trans_lt (by exact_mod_cast hcount)⟩
  intro a ha
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp (hA ha)
  exact Finset.mem_Icc.mpr ⟨ha1, ha2.trans hyp⟩

/-- The same full endpoint stated with actual strictly increasing sequences. -/
theorem erdos_437_sequence :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ m : ℕ, ∃ a : Fin m → ℕ,
        StrictMono a ∧ (∀ i, 1 ≤ a i ∧ a i ≤ N) ∧
        (N : ℝ) ^ (1 - ε) < ((sequenceSquareCuts a).card : ℝ) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := original_lower_question ε hε
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨A, hA, hcount⟩ := hN₀ N hN
  refine ⟨A.card, A.orderEmbOfFin rfl, (A.orderEmbOfFin rfl).strictMono, ?_, ?_⟩
  · intro i
    exact Finset.mem_Icc.mp (hA (A.orderEmbOfFin_mem rfl i))
  · simpa only [card_sequenceSquareCuts_orderEmb] using hcount


/-- The literal real-cutoff version of the original question.
The floor step is explicit: N < (y+1)^m implies x < (y+1)^m for N=floor x. -/
theorem erdos_437_real :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x →
      ∃ l : ℕ, ∃ a : Fin l → ℕ,
        StrictMono a ∧ (∀ i, 1 ≤ a i ∧ (a i : ℝ) ≤ x) ∧
        x ^ (1 - ε) < ((sequenceSquareCuts a).card : ℝ) := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (4 / ε)
  let m := k + 4
  have hm : 0 < m := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hεk : (4 : ℝ) < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
  have hexp : 1 - ε ≤ (k : ℝ) / (m : ℝ) := by
    apply (le_div_iff₀ hmR).mpr
    have hmcast : (m : ℝ) = (k : ℝ) + 4 := by dsimp [m]; norm_cast
    rw [hmcast]
    nlinarith
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (eventually_grid_lower k)
  let B := max Y (2 ^ k + 1)
  refine ⟨((B ^ m : ℕ) : ℝ), ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := (Nat.cast_nonneg _).trans hx
  let N := Nat.floor x
  have hN : B ^ m ≤ N := Nat.le_floor hx
  have hNle : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  obtain ⟨y, hBy, hyp, hupper⟩ := exists_power_bracket m B N hm hN
  have hyY : Y ≤ y := (le_max_left _ _).trans hBy
  have hy2k : 2 ^ k < y := by
    have h := (le_max_right Y (2 ^ k + 1)).trans hBy
    omega
  have hypos : 1 ≤ y :=
    Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le (2 ^ k)) hy2k)
  have hNpos : 1 ≤ N := (one_le_nat_pow y m hypos).trans hyp
  have hx1 : 1 ≤ x := (by exact_mod_cast hNpos : (1 : ℝ) ≤ N).trans hNle
  have hbase : x ≤ ((y + 1 : ℕ) : ℝ) ^ m := by
    apply hxN.le.trans
    exact_mod_cast (show N + 1 ≤ (y + 1) ^ m by omega)
  have hrpow : (((y + 1 : ℕ) : ℝ) ^ m) ^ ((k : ℝ) / (m : ℝ)) =
      ((y + 1 : ℕ) : ℝ) ^ k := by
    rw [← Real.rpow_natCast ((y + 1 : ℕ) : ℝ) m,
      ← Real.rpow_mul (by positivity)]
    have he : (m : ℝ) * ((k : ℝ) / (m : ℝ)) = (k : ℝ) := by
      field_simp [ne_of_gt hmR]
    rw [he, Real.rpow_natCast]
  have hnat : (y + 1) ^ k ≤ y ^ (k + 1) := by
    calc
      (y + 1) ^ k ≤ (2 * y) ^ k := by gcongr <;> omega
      _ = 2 ^ k * y ^ k := by rw [mul_pow]
      _ ≤ y * y ^ k := Nat.mul_le_mul_right _ hy2k.le
      _ = y ^ (k + 1) := by rw [pow_succ]; ring
  have hcomparison : x ^ (1 - ε) ≤ ((y ^ (k + 1) : ℕ) : ℝ) := by
    calc
      x ^ (1 - ε) ≤ x ^ ((k : ℝ) / (m : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hx1 hexp
      _ ≤ (((y + 1 : ℕ) : ℝ) ^ m) ^ ((k : ℝ) / (m : ℝ)) :=
        Real.rpow_le_rpow hx0 hbase (by positivity)
      _ = ((y + 1 : ℕ) : ℝ) ^ k := hrpow
      _ ≤ ((y ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
  obtain ⟨A, hA, hcount⟩ := hY y hyY
  have hcountR : x ^ (1 - ε) < ((squareCuts A).card : ℝ) :=
    hcomparison.trans_lt (by exact_mod_cast hcount)
  refine ⟨A.card, A.orderEmbOfFin rfl, (A.orderEmbOfFin rfl).strictMono, ?_, ?_⟩
  · intro i
    obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp (hA (A.orderEmbOfFin_mem rfl i))
    refine ⟨ha1, ?_⟩
    have hai : A.orderEmbOfFin rfl i ≤ N := ha2.trans hyp
    exact (by exact_mod_cast hai : (A.orderEmbOfFin rfl i : ℝ) ≤ N).trans hNle
  · simpa only [card_sequenceSquareCuts_orderEmb] using hcountR

end
end JSP356
