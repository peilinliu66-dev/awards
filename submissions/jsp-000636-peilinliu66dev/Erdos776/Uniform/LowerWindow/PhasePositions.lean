import Erdos776.Uniform.LowerWindow.PhaseParameters

/-!
# Positions and birth levels of the ordinary phases

This file formalizes (5.4)--(5.8).  Phase numbers are one-based.  The value
at index zero is defined to agree with phase one only so that the recursive
definition is total; all mathematical statements below use `1 ≤ j`.
-/

namespace Erdos776.Uniform

/-- The active top position `u_j`. -/
def phaseTop (r t : ℕ) : ℕ → ℕ
  | 0 => anchorN r t - 4
  | 1 => anchorN r t - 4
  | 2 =>
      let u := anchorN r t - 4
      u - (u - 5) / 2 - 2
  | j + 3 => (phaseTop r t (j + 2) + 1) / 2

@[simp] theorem phaseTop_zero (r t : ℕ) :
    phaseTop r t 0 = anchorN r t - 4 := rfl

@[simp] theorem phaseTop_one (r t : ℕ) :
    phaseTop r t 1 = anchorN r t - 4 := rfl

@[simp] theorem phaseTop_two (r t : ℕ) :
    phaseTop r t 2 =
      (anchorN r t - 4) - ((anchorN r t - 4) - 5) / 2 - 2 := rfl

/-- The number `ell_j` of in-phase extensions. -/
def phaseExtensionCount (r t j : ℕ) : ℕ :=
  if j = 1 then (phaseTop r t j - 5) / 2
  else (phaseTop r t j - 4) / 2

theorem phaseTop_one_eq_width
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    phaseTop r t 1 = r - phaseWidth t - 1 := by
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp [phaseTop, anchorN, phaseWidth] at h64 ⊢
  omega

theorem five_le_phaseTop_one
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    5 ≤ phaseTop r t 1 := by
  rw [phaseTop_one_eq_width ht]
  have h64 := sixtyFour_mul_phaseWidth_le ht
  have hc : 3 ≤ phaseWidth t := by simp [phaseWidth]
  omega

/-- Apart from the exceptional first transition, `u_{j+1}=ceil(u_j/2)`. -/
theorem phaseTop_succ_eq_ceil
    {r t j : ℕ} (hj : 2 ≤ j) :
    phaseTop r t (j + 1) = (phaseTop r t j + 1) / 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 2 + j + 1 = j + 3 by omega,
    show 2 + j = j + 2 by omega]
  rfl

/-- The recurrence in (5.6), including the exceptional definition of `ell_1`. -/
theorem phaseTop_succ_eq_sub
    {r t j : ℕ} (hj : 1 ≤ j) (hu : 4 ≤ phaseTop r t j) :
    phaseTop r t (j + 1) =
      phaseTop r t j - phaseExtensionCount r t j - 2 := by
  by_cases hj1 : j = 1
  · subst j
    rw [show 1 + 1 = 2 by omega, phaseTop_two, phaseTop_one]
    simp [phaseExtensionCount]
  · have hj2 : 2 ≤ j := by omega
    rw [phaseTop_succ_eq_ceil hj2]
    simp only [phaseExtensionCount, if_neg hj1]
    omega

/-- Every phase transition is at least a halving. -/
theorem phaseTop_le_two_mul_succ
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t) (hj : 1 ≤ j) :
    phaseTop r t j ≤ 2 * phaseTop r t (j + 1) := by
  by_cases hj1 : j = 1
  · subst j
    have hu := five_le_phaseTop_one ht
    rw [show 1 + 1 = 2 by omega, phaseTop_two, phaseTop_one]
    rw [phaseTop_one] at hu
    omega
  · have hj2 : 2 ≤ j := by omega
    rw [phaseTop_succ_eq_ceil hj2]
    omega

/-- The rounding error in a phase transition is at most two. -/
theorem two_mul_phaseTop_succ_le
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t) (hj : 1 ≤ j) :
    2 * phaseTop r t (j + 1) ≤ phaseTop r t j + 2 := by
  by_cases hj1 : j = 1
  · subst j
    have hu := five_le_phaseTop_one ht
    rw [show 1 + 1 = 2 by omega, phaseTop_two, phaseTop_one]
    rw [phaseTop_one] at hu
    omega
  · have hj2 : 2 ≤ j := by omega
    rw [phaseTop_succ_eq_ceil hj2]
    omega

theorem phaseTop_succ_le (r t j : ℕ) :
    phaseTop r t (j + 1) ≤ phaseTop r t j := by
  by_cases hj0 : j = 0
  · subst j
    simp
  by_cases hj1 : j = 1
  · subst j
    rw [show 1 + 1 = 2 by omega, phaseTop_two, phaseTop_one]
    omega
  · rw [phaseTop_succ_eq_ceil (j := j) (by omega)]
    omega

theorem antitone_phaseTop (r t : ℕ) : Antitone (phaseTop r t) :=
  antitone_nat_of_succ_le (phaseTop_succ_le r t)

/-- Multiplicative form of the lower half of (5.7). -/
theorem phaseTop_scaled_lower
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) (n : ℕ) :
    phaseTop r t 1 ≤ 2 ^ n * phaseTop r t (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hhalf := phaseTop_le_two_mul_succ ht
        (j := n + 1) (by omega)
      have hhalf' : phaseTop r t (n + 1) ≤
          2 * phaseTop r t (n + 2) := by
        simpa only [show n + 1 + 1 = n + 2 by omega] using hhalf
      calc
        phaseTop r t 1 ≤ 2 ^ n * phaseTop r t (n + 1) := ih
        _ ≤ 2 ^ n * (2 * phaseTop r t (n + 2)) :=
          Nat.mul_le_mul_left _ hhalf'
        _ = 2 ^ (n + 1) * phaseTop r t (n + 1 + 1) := by
          simp only [pow_succ, show n + 1 + 1 = n + 2 by omega,
            Nat.mul_assoc]

/-- Multiplicative form of the upper half of (5.7). -/
theorem phaseTop_scaled_upper
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) (n : ℕ) :
    2 ^ n * phaseTop r t (n + 1) ≤
      phaseTop r t 1 + 2 * 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hround := two_mul_phaseTop_succ_le ht
        (j := n + 1) (by omega)
      have hround' : 2 * phaseTop r t (n + 2) ≤
          phaseTop r t (n + 1) + 2 := by
        simpa only [show n + 1 + 1 = n + 2 by omega] using hround
      calc
        2 ^ (n + 1) * phaseTop r t (n + 1 + 1) =
            2 ^ n * (2 * phaseTop r t (n + 2)) := by
          simp only [pow_succ, show n + 1 + 1 = n + 2 by omega,
            Nat.mul_assoc]
        _ ≤ 2 ^ n * (phaseTop r t (n + 1) + 2) :=
          Nat.mul_le_mul_left _ hround'
        _ = 2 ^ n * phaseTop r t (n + 1) + 2 * 2 ^ n := by
          simp [Nat.mul_add, Nat.mul_comm]
        _ ≤ (phaseTop r t 1 + 2 * 2 ^ n) + 2 * 2 ^ n :=
          Nat.add_le_add_right ih _
        _ = phaseTop r t 1 + 2 * 2 ^ (n + 1) := by
          rw [pow_succ]
          omega

/-- The lower quantitative endpoint in (5.8). -/
theorem three_mul_phaseWidth_le_finalTop
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    3 * phaseWidth t ≤ phaseTop r t (phaseCount r t) := by
  let K := phaseCount r t
  let p := 2 ^ (K - 1)
  have hK : 1 ≤ K := (phaseCount_spec ht).1
  have hscaled : phaseTop r t 1 ≤ p * phaseTop r t K := by
    have h := phaseTop_scaled_lower ht (K - 1)
    simpa [K, p, show K - 1 + 1 = K by omega] using h
  have hphase : phaseWidth t * p ≤ r / 4 := by
    simpa [K, p] using (phaseCount_spec ht).2.1
  have hleft : (3 * phaseWidth t) * p ≤ 3 * (r / 4) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 3 hphase
  have hquarter : 3 * (r / 4) ≤ phaseTop r t 1 := by
    rw [phaseTop_one_eq_width ht]
    have h64 := sixtyFour_mul_phaseWidth_le ht
    have hc : 3 ≤ phaseWidth t := by simp [phaseWidth]
    omega
  have hprod : p * (3 * phaseWidth t) ≤
      p * phaseTop r t K := by
    rw [Nat.mul_comm p (3 * phaseWidth t)]
    exact hleft.trans (hquarter.trans hscaled)
  simpa only [K] using Nat.le_of_mul_le_mul_left hprod (by simp [p])

/-- The upper quantitative endpoint in (5.8). -/
theorem finalTop_le_eight_mul_phaseWidth_add_two
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    phaseTop r t (phaseCount r t) ≤ 8 * phaseWidth t + 2 := by
  let K := phaseCount r t
  let p := 2 ^ (K - 1)
  have hK : 1 ≤ K := (phaseCount_spec ht).1
  have hscaled : p * phaseTop r t K ≤ phaseTop r t 1 + 2 * p := by
    have h := phaseTop_scaled_upper ht (K - 1)
    simpa [K, p, show K - 1 + 1 = K by omega] using h
  have hpow : 2 ^ K = 2 * p := by
    dsimp [p]
    conv_lhs => rw [show K = K - 1 + 1 by omega, pow_succ]
    omega
  have hupper : r / 4 < 2 * (phaseWidth t * p) := by
    have h := (phaseCount_spec ht).2.2
    rw [hpow] at h
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hr : r < 8 * (phaseWidth t * p) := by omega
  have hu1 : phaseTop r t 1 ≤ r := by
    rw [phaseTop_one]
    exact (Nat.sub_le (anchorN r t) 4).trans (Nat.sub_le r (2 * t))
  have hprod : p * phaseTop r t K < p * (8 * phaseWidth t + 2) := by
    calc
      p * phaseTop r t K ≤ phaseTop r t 1 + 2 * p := hscaled
      _ ≤ r + 2 * p := Nat.add_le_add_right hu1 _
      _ < 8 * (phaseWidth t * p) + 2 * p := Nat.add_lt_add_right hr _
      _ = p * (8 * phaseWidth t + 2) := by
        simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
  simpa only [K] using (Nat.lt_of_mul_lt_mul_left hprod).le

theorem phaseTop_between_at_phase
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    3 * phaseWidth t ≤ phaseTop r t j ∧
      phaseTop r t j ≤ phaseTop r t 1 := by
  constructor
  · exact (three_mul_phaseWidth_le_finalTop ht).trans
      (antitone_phaseTop r t hjK)
  · exact antitone_phaseTop r t hj

theorem phaseTop_two_le_half_add_one
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    phaseTop r t 2 ≤ r / 2 + 1 := by
  have hround := two_mul_phaseTop_succ_le ht (j := 1) (by omega)
  have hu1 : phaseTop r t 1 ≤ r := by
    rw [phaseTop_one]
    exact (Nat.sub_le (anchorN r t) 4).trans (Nat.sub_le r (2 * t))
  have hround' : 2 * phaseTop r t 2 ≤ phaseTop r t 1 + 2 := by
    simpa only [show 1 + 1 = 2 by omega] using hround
  omega

theorem phaseTop_le_half_add_one_of_two_le
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t) (hj : 2 ≤ j) :
    phaseTop r t j ≤ r / 2 + 1 :=
  (antitone_phaseTop r t hj).trans (phaseTop_two_le_half_add_one ht)

theorem four_le_phaseTop_at_phase
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    4 ≤ phaseTop r t j := by
  have h := (phaseTop_between_at_phase ht hj hjK).1
  simp only [phaseWidth] at h
  omega

/-- `b_j`, defined so that the slot identity (5.6b) is visible by construction. -/
def phaseBirth (r t j : ℕ) : ℕ :=
  phaseTop r t j + t + j + 1

theorem phaseBirth_sub_phaseTop (r t j : ℕ) :
    phaseBirth r t j - phaseTop r t j = t + j + 1 := by
  unfold phaseBirth
  omega

theorem phaseBirth_one
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    phaseBirth r t 1 = r - t - 2 := by
  unfold phaseBirth
  rw [phaseTop_one_eq_width ht]
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp only [phaseWidth] at h64 ⊢
  omega

/-- A harvest lands exactly one level above the next phase birth. -/
theorem phaseBirth_succ
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseBirth r t (j + 1) =
      phaseBirth r t j - phaseExtensionCount r t j - 1 := by
  have hu := four_le_phaseTop_at_phase ht hj hjK
  unfold phaseBirth
  rw [phaseTop_succ_eq_sub hj hu]
  have hell : phaseExtensionCount r t j + 2 ≤ phaseTop r t j := by
    by_cases hj1 : j = 1
    · subst j
      have hu5 := five_le_phaseTop_one ht
      simp only [phaseExtensionCount, if_pos]
      omega
    · simp only [phaseExtensionCount, if_neg hj1]
      omega
  omega

theorem phaseBirth_succ_add_one
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseBirth r t (j + 1) + 1 =
      phaseBirth r t j - phaseExtensionCount r t j := by
  rw [phaseBirth_succ ht hj hjK]
  have hu := four_le_phaseTop_at_phase ht hj hjK
  have hell : phaseExtensionCount r t j + 1 ≤ phaseBirth r t j := by
    unfold phaseBirth
    by_cases hj1 : j = 1
    · subst j
      have hu5 := five_le_phaseTop_one ht
      simp only [phaseExtensionCount, if_pos]
      omega
    · simp only [phaseExtensionCount, if_neg hj1]
      omega
  omega

end Erdos776.Uniform
