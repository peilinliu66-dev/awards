import Erdos776.Combinatorics.BoundedShadow
import Erdos776.Uniform.FreeCore

/-!
# Verified finite constant-profile checks

This file provides one ground-bounded executable recurrence for constant
profiles.  Its soundness theorem relates every successful checked state to
the original `profileChain`, whose definition uses `canonicalShadow`.

The two specializations below certify exactly the finite data needed for the
range `11 ≤ r < 29`: upper-core fit/carry and overflow of the full profile at
level two.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- The checked state after descending `d` levels from the occupied top `hi`. -/
def checkedConstantProfileState (n load hi : ℕ) : ℕ → Option ℕ
  | 0 =>
      if load ≤ fastBinom n hi then some load else none
  | d + 1 =>
      match checkedConstantProfileState n load hi d with
      | none => none
      | some m =>
          let i := hi - (d + 1)
          let next := load + boundedShadow n (i + 1) m
          if next ≤ fastBinom n i then some next else none

theorem checkedConstantProfileState_pred_some
    {n load hi d m : ℕ}
    (h : checkedConstantProfileState n load hi (d + 1) = some m) :
    ∃ prev, checkedConstantProfileState n load hi d = some prev := by
  simp only [checkedConstantProfileState] at h
  split at h
  · contradiction
  · rename_i prev hprev
    split at h
    · exact ⟨prev, hprev⟩
    · contradiction

theorem checkedConstantProfileState_some_of_le
    {n load hi d D m : ℕ} (hdD : d ≤ D)
    (hD : checkedConstantProfileState n load hi D = some m) :
    ∃ value, checkedConstantProfileState n load hi d = some value := by
  refine Nat.decreasingInduction'
      (P := fun k => ∃ value,
        checkedConstantProfileState n load hi k = some value)
      (m := d) (n := D) ?_ hdD ⟨m, hD⟩
  intro k _ _ hk
  obtain ⟨value, hvalue⟩ := hk
  exact checkedConstantProfileState_pred_some hvalue

/-- A successful state is the exact canonical recurrence state and fits. -/
theorem checkedConstantProfileState_sound
    {n load hi d m : ℕ} (hd : d ≤ hi)
    (h : checkedConstantProfileState n load hi d = some m) :
    m = profileChain (fun _ => load) hi (hi - d) ∧
      m ≤ n.choose (hi - d) := by
  induction d generalizing m with
  | zero =>
      simp only [checkedConstantProfileState] at h
      split at h
      · rename_i hcap
        simp only [Option.some.injEq] at h
        subst m
        constructor
        · simp only [Nat.sub_zero]
          rw [profileChain_step (fun _ => load) (show hi ≤ hi by omega)]
          simp
        · simpa using hcap
      · contradiction
  | succ d ih =>
      have hdPrev : d ≤ hi := by omega
      simp only [checkedConstantProfileState] at h
      split at h
      · contradiction
      · rename_i prev hprev
        split at h
        · rename_i hcap
          simp only [Option.some.injEq] at h
          subst m
          have hsound := ih hdPrev hprev
          let i := hi - (d + 1)
          have hlevelPrev : hi - d = i + 1 := by dsimp [i]; omega
          have hshadow : boundedShadow n (i + 1) prev =
              canonicalShadow (i + 1) prev := by
            apply boundedShadow_eq_canonicalShadow (by omega)
            rw [← hlevelPrev]
            exact hsound.2
          have hlevel : hi - (d + 1) = i := by rfl
          have hprevEq : prev =
              profileChain (fun _ => load) hi (i + 1) := by
            rw [← hlevelPrev]
            exact hsound.1
          constructor
          · rw [hlevel, hshadow,
              profileChain_step (fun _ => load) (show i ≤ hi by omega),
              ← hprevEq]
          · simpa [hlevel] using hcap
        · contradiction

/-- Check all capacities of a constant profile on the interval `lo,...,hi`. -/
def constantProfileCheck (n load lo hi : ℕ) : Bool :=
  (checkedConstantProfileState n load hi (hi - lo)).isSome

/-- A successful interval check proves the original canonical recurrence feasible. -/
theorem constantProfileCheck_sound
    {n load lo hi : ℕ} (hlohi : lo ≤ hi)
    (hcheck : constantProfileCheck n load lo hi = true) :
    IsProfileRecurrence n lo hi (fun _ => load)
      (profileChain (fun _ => load) hi) := by
  have hfull : ∃ m,
      checkedConstantProfileState n load hi (hi - lo) = some m := by
    unfold constantProfileCheck at hcheck
    cases hstate : checkedConstantProfileState n load hi (hi - lo) with
    | none => simp [hstate] at hcheck
    | some m => exact ⟨m, rfl⟩
  refine ⟨profileChain_top (fun _ => load) hi,
    (fun i _ hii => profileChain_step (fun _ => load) hii), ?_⟩
  intro i hloi hihi
  by_cases htop : i = hi + 1
  · subst i
    simp
  have hii : i ≤ hi := by omega
  let d := hi - i
  have hd : d ≤ hi - lo := by dsimp [d]; omega
  obtain ⟨lastValue, hlastValue⟩ := hfull
  obtain ⟨value, hvalue⟩ := checkedConstantProfileState_some_of_le
    hd hlastValue
  have hsound := checkedConstantProfileState_sound
    (n := n) (load := load) (hi := hi) (d := d) (m := value)
    (by dsimp [d]; omega) hvalue
  have hlevel : hi - d = i := by dsimp [d]; omega
  rw [← hlevel, ← hsound.1]
  exact hsound.2

/-- A feasible checked constant profile produces an actual antichain profile. -/
theorem fullMiddleProfileExists_of_constantProfileCheck
    {n r : ℕ} (hn : 4 ≤ n)
    (hcheck : constantProfileCheck n r 2 (n - 2) = true) :
    FullMiddleProfileExists n r := by
  have hrec := constantProfileCheck_sound (show 2 ≤ n - 2 by omega) hcheck
  obtain ⟨F, hanti, hlevels, -⟩ :=
    profile_sufficiency (n := n) (lo := 2) (hi := n - 2)
      (f := fun _ => r) (m := profileChain (fun _ => r) (n - 2))
      (by omega) hrec
  refine ⟨F, hanti, ?_⟩
  intro i hi2 hin
  unfold Erdos776.Antichain.HasMultiplicityAt
  rw [hlevels i hi2 hin]

/-- Check upper-core capacity down to level four and the bounded carry at level three. -/
def upperCoreCheck (r : ℕ) : Bool :=
  match checkedConstantProfileState (r + 4) r (r + 2) (r - 2) with
  | none => false
  | some m4 =>
      let m3 := r + boundedShadow (r + 4) 4 m4
      let e := m3 - fastBinom (r + 4) 3
      decide (fastBinom (r + 4) 3 + e = m3 ∧ 1 ≤ e ∧ e ≤ 6)

/-- A successful upper-core check supplies the semantic assembly interface. -/
theorem upperCoreCheck_sound
    {r : ℕ} (hr : 2 ≤ r) (hcheck : upperCoreCheck r = true) :
    HasUpperCoreData r := by
  unfold upperCoreCheck at hcheck
  split at hcheck
  · contradiction
  · rename_i m4 hm4
    simp only [decide_eq_true_eq] at hcheck
    let m3 := r + boundedShadow (r + 4) 4 m4
    let e := m3 - fastBinom (r + 4) 3
    have hconditions :
        fastBinom (r + 4) 3 + e = m3 ∧ 1 ≤ e ∧ e ≤ 6 := by
      simpa only [m3, e] using hcheck
    have hsound4 := checkedConstantProfileState_sound
      (n := r + 4) (load := r) (hi := r + 2)
      (d := r - 2) (m := m4) (by omega) hm4
    have hlevel4 : r + 2 - (r - 2) = 4 := by omega
    have hm4Eq : m4 = upperCoreChain r 4 := by
      simpa only [upperCoreChain, hlevel4] using hsound4.1
    have hm4Cap : m4 ≤ (r + 4).choose 4 := by
      simpa only [hlevel4] using hsound4.2
    have hshadow : boundedShadow (r + 4) 4 m4 =
        canonicalShadow 4 m4 :=
      boundedShadow_eq_canonicalShadow (by omega) hm4Cap
    have hm3Eq : m3 = upperCoreChain r 3 := by
      dsimp only [m3]
      rw [hshadow, upperCoreChain_step r 3 (by omega), ← hm4Eq]
    refine ⟨e, ?_, ?_, hconditions.2.1, hconditions.2.2⟩
    · intro b hb4 hbr
      let d := r + 2 - b
      have hd : d ≤ r - 2 := by dsimp [d]; omega
      obtain ⟨value, hvalue⟩ := checkedConstantProfileState_some_of_le
        (n := r + 4) (load := r) (hi := r + 2) hd hm4
      have hsound := checkedConstantProfileState_sound
        (n := r + 4) (load := r) (hi := r + 2)
        (d := d) (m := value) (by dsimp [d]; omega) hvalue
      have hlevel : r + 2 - d = b := by dsimp [d]; omega
      change profileChain (fun _ => r) (r + 2) b ≤ (r + 4).choose b
      rw [← hlevel, ← hsound.1]
      exact hsound.2
    · calc
        upperCoreChain r 3 = m3 := hm3Eq.symm
        _ = fastBinom (r + 4) 3 + e := hconditions.1.symm
        _ = (r + 4).choose 3 + e := by simp

/-- Check that a constant profile fits through level three and overflows at level two. -/
def constantProfileLevelTwoOverflowCheck (n load : ℕ) : Bool :=
  let hi := n - 2
  match checkedConstantProfileState n load hi (hi - 3) with
  | none => false
  | some m3 =>
      decide (fastBinom n 2 < load + boundedShadow n 3 m3)

/-- A successful level-two check rules out the corresponding actual profile. -/
theorem constantProfileLevelTwoOverflowCheck_sound
    {n load : ℕ} (hn : 5 ≤ n)
    (hcheck : constantProfileLevelTwoOverflowCheck n load = true) :
    ¬ FullMiddleProfileExists n load := by
  unfold constantProfileLevelTwoOverflowCheck at hcheck
  dsimp only at hcheck
  split at hcheck
  · contradiction
  · rename_i m3 hm3
    simp only [decide_eq_true_eq] at hcheck
    let hi := n - 2
    let d := hi - 3
    have hd : d ≤ hi := by dsimp [d]; omega
    have hsound3 := checkedConstantProfileState_sound
      (n := n) (load := load) (hi := hi) (d := d) (m := m3) hd (by
        simpa only [hi, d] using hm3)
    have hlevel3 : hi - d = 3 := by dsimp [hi, d]; omega
    have hm3Eq : m3 = profileChain (fun _ => load) hi 3 := by
      simpa only [hlevel3] using hsound3.1
    have hm3Cap : m3 ≤ n.choose 3 := by
      simpa only [hlevel3] using hsound3.2
    have hshadow : boundedShadow n 3 m3 = canonicalShadow 3 m3 :=
      boundedShadow_eq_canonicalShadow (by omega) hm3Cap
    have hstate2 : load + boundedShadow n 3 m3 =
        profileChain (fun _ => load) hi 2 := by
      rw [hshadow, profileChain_step (fun _ => load) (show 2 ≤ hi by
        dsimp [hi]
        omega), ← hm3Eq]
    apply not_fullMiddleProfileExists_of_chain_overflow
      (n := n) (r := load) (i := 2) (by omega) (by omega)
    simpa only [hi, fastBinom_eq_choose, hstate2] using hcheck

/-- Check the bad full profile at `n = 2r+5`. -/
def fullProfileOverflowCheck (r : ℕ) : Bool :=
  constantProfileLevelTwoOverflowCheck (2 * r + 5) r

/-- A successful finite overflow check rules out the full middle profile. -/
theorem fullProfileOverflowCheck_sound
    {r : ℕ} (hcheck : fullProfileOverflowCheck r = true) :
    ¬ FullMiddleProfileExists (2 * r + 5) r := by
  exact constantProfileLevelTwoOverflowCheck_sound (by omega) hcheck

end Erdos776.Uniform
