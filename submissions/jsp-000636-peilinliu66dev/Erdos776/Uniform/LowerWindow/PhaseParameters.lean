import Erdos776.Uniform.LowerWindow.Parameters

/-!
# Parameters of the doubling-phase segment

This file formalizes the integer `K` selected in Section 5 and the resulting
lower bounds on the tower stones.  In particular, `phaseCount` is selected by
least-number search; it is not an externally computed parameter.
-/

namespace Erdos776.Uniform

/-- The elementary exponential estimate used to show that a phase count exists. -/
theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      omega

/-- Some power of two, after scaling by the positive phase width, exceeds `r/4`. -/
theorem exists_phaseCount_exponent (r t : ℕ) :
    ∃ K, r / 4 < phaseWidth t * 2 ^ K := by
  let x := r / 4
  refine ⟨x + 1, ?_⟩
  have hpow := succ_le_two_pow (x + 1)
  have hwidth : 1 ≤ phaseWidth t := by simp [phaseWidth]
  have hmul := Nat.mul_le_mul_right (2 ^ (x + 1)) hwidth
  dsimp [x] at hpow ⊢
  have hscaled : 2 ^ (r / 4 + 1) ≤
      phaseWidth t * 2 ^ (r / 4 + 1) := by
    simpa [Nat.mul_comm] using hmul
  omega

/-- The least `K` for which `r/4 < c 2^K`. -/
noncomputable def phaseCount (r t : ℕ) : ℕ :=
  Nat.find (exists_phaseCount_exponent r t)

theorem phaseCount_upper (r t : ℕ) :
    r / 4 < phaseWidth t * 2 ^ phaseCount r t := by
  exact Nat.find_spec (exists_phaseCount_exponent r t)

/-- The two inequalities selecting `K` in (5.1), together with positivity. -/
def IsPhaseCount (r t K : ℕ) : Prop :=
  1 ≤ K ∧
    phaseWidth t * 2 ^ (K - 1) ≤ r / 4 ∧
    r / 4 < phaseWidth t * 2 ^ K

theorem phaseCount_spec_of_width_le
    {r t : ℕ} (hwidth : phaseWidth t ≤ r / 4) :
    IsPhaseCount r t (phaseCount r t) := by
  have hupper := phaseCount_upper r t
  have hpos : 1 ≤ phaseCount r t := by
    by_contra hnot
    have hzero : phaseCount r t = 0 := by omega
    rw [hzero] at hupper
    simp only [pow_zero, Nat.mul_one] at hupper
    omega
  have hminimal : ¬ r / 4 <
      phaseWidth t * 2 ^ (phaseCount r t - 1) := by
    have hlt : phaseCount r t - 1 < phaseCount r t := by omega
    simpa only [phaseCount] using
      (Nat.find_min (exists_phaseCount_exponent r t) hlt)
  exact ⟨hpos, Nat.le_of_not_gt hminimal, hupper⟩

theorem phaseWidth_le_quarter
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    phaseWidth t ≤ r / 4 := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
  have h64 := sixtyFour_mul_phaseWidth_le ht
  omega

/-- Under the maximal-anchor hypotheses, the least exponent satisfies `K ≥ 5`. -/
theorem five_le_phaseCount
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    5 ≤ phaseCount r t := by
  have hspec := phaseCount_spec_of_width_le (phaseWidth_le_quarter ht)
  by_contra hnot
  have hK4 : phaseCount r t ≤ 4 := by omega
  have hpow : 2 ^ phaseCount r t ≤ 2 ^ 4 :=
    pow_le_pow_right' (by omega) hK4
  have hscaled : phaseWidth t * 2 ^ phaseCount r t ≤
      phaseWidth t * 2 ^ 4 := Nat.mul_le_mul_left _ hpow
  have hquarter : 16 * phaseWidth t ≤ r / 4 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
    have h64 := sixtyFour_mul_phaseWidth_le ht
    omega
  have hscaled' : phaseWidth t * 2 ^ phaseCount r t ≤
      16 * phaseWidth t := by
    norm_num at hscaled ⊢
    simpa [Nat.mul_comm] using hscaled
  have := hscaled'.trans hquarter
  have hupper := hspec.2.2
  omega

theorem phaseCount_spec
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    IsPhaseCount r t (phaseCount r t) :=
  phaseCount_spec_of_width_le (phaseWidth_le_quarter ht)

/-- For every ordinary phase, the tower stone remains above `3r/4`. -/
theorem towerStone_phase_lower
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    3 * r / 4 + 1 ≤ towerStone r t j := by
  have hspec := phaseCount_spec ht
  have hexp : j - 1 ≤ phaseCount r t - 1 := by omega
  have hpow : 2 ^ (j - 1) ≤ 2 ^ (phaseCount r t - 1) :=
    pow_le_pow_right' (by omega) hexp
  have hdist : phaseWidth t * 2 ^ (j - 1) ≤ r / 4 :=
    (Nat.mul_le_mul_left _ hpow).trans hspec.2.1
  unfold towerStone
  omega

/-- The first stone after the ordinary phases is still above `r/2`. -/
theorem towerStone_after_phases_lower
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    r / 2 + 1 ≤ towerStone r t (phaseCount r t + 1) := by
  have hspec := phaseCount_spec ht
  have hK : 1 ≤ phaseCount r t := hspec.1
  have hpow : 2 ^ phaseCount r t =
      2 * 2 ^ (phaseCount r t - 1) := by
    conv_lhs => rw [show phaseCount r t = phaseCount r t - 1 + 1 by omega,
      pow_succ]
    omega
  have hdist : phaseWidth t * 2 ^ phaseCount r t ≤ r / 2 := by
    have hlower := hspec.2.1
    calc
      phaseWidth t * 2 ^ phaseCount r t =
          2 * (phaseWidth t * 2 ^ (phaseCount r t - 1)) := by
        rw [hpow]
        ac_rfl
      _ ≤ 2 * (r / 4) := Nat.mul_le_mul_left 2 hlower
      _ ≤ r / 2 := by omega
  simp only [towerStone, show phaseCount r t + 1 - 1 = phaseCount r t by omega]
  omega

end Erdos776.Uniform
