import Erdos776.Combinatorics.BoundedShadow
import Erdos776.Uniform.LowerWindow.Supersolution

/-!
# Executable finite checker for the lower window

The checker runs the exact lower-window recurrence from the top down.  It
checks capacity before every call to `boundedShadow`, so the proof that the
bounded evaluator equals `canonicalShadow` applies at each step.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- The checked state after descending `d` levels from level `r+1`. -/
def checkedLowerWindowState (r : ℕ) : ℕ → Option ℕ
  | 0 =>
      let m := r - 6
      if m ≤ fastBinom (r + 4) (r + 1) then some m else none
  | d + 1 =>
      match checkedLowerWindowState r d with
      | none => none
      | some m =>
          let i := r - d
          let next := r + boundedShadow (r + 4) (i + 1) m
          if next ≤ fastBinom (r + 4) i then some next else none

/-- The complete finite check, ending at level two. -/
def lowerWindowCheck (r : ℕ) : Bool :=
  (checkedLowerWindowState r (r - 1)).isSome

theorem checkedLowerWindowState_pred_some
    {r d m : ℕ} (h : checkedLowerWindowState r (d + 1) = some m) :
    ∃ prev, checkedLowerWindowState r d = some prev := by
  simp only [checkedLowerWindowState] at h
  split at h
  · contradiction
  · rename_i prev hprev
    split at h
    · exact ⟨prev, hprev⟩
    · contradiction

theorem checkedLowerWindowState_some_of_le
    {r d D m : ℕ} (hdD : d ≤ D)
    (hD : checkedLowerWindowState r D = some m) :
    ∃ value, checkedLowerWindowState r d = some value := by
  refine Nat.decreasingInduction'
      (P := fun k => ∃ value, checkedLowerWindowState r k = some value)
      (m := d) (n := D) ?_ hdD ⟨m, hD⟩
  intro k _ _ hk
  obtain ⟨value, hvalue⟩ := hk
  exact checkedLowerWindowState_pred_some hvalue

theorem checkedLowerWindowState_sound
    {r d m : ℕ} (hr : 2 ≤ r) (hd : d ≤ r - 1)
    (h : checkedLowerWindowState r d = some m) :
    m = lowerWindowChain r (r + 1 - d) ∧
      m ≤ (r + 4).choose (r + 1 - d) := by
  induction d generalizing m with
  | zero =>
      simp only [checkedLowerWindowState] at h
      split at h
      · rename_i hcap
        simp only [Option.some.injEq] at h
        subst m
        constructor
        · exact (lowerWindowChain_top_value r).symm
        · simpa using hcap
      · contradiction
  | succ d ih =>
      have hdPrev : d ≤ r - 1 := by omega
      simp only [checkedLowerWindowState] at h
      split at h
      · contradiction
      · rename_i prev hprev
        split at h
        · rename_i hcap
          simp only [Option.some.injEq] at h
          subst m
          have hsound := ih hdPrev hprev
          let i := r - d
          have hi : 2 ≤ i := by dsimp [i]; omega
          have hlevelPrev : r + 1 - d = i + 1 := by dsimp [i]; omega
          have hshadow : boundedShadow (r + 4) (i + 1) prev =
              canonicalShadow (i + 1) prev := by
            apply boundedShadow_eq_canonicalShadow (by omega)
            rw [← hlevelPrev]
            exact hsound.2
          have hlevel : r + 1 - (d + 1) = i := by dsimp [i]; omega
          have hprevEq : prev = lowerWindowChain r (i + 1) := by
            rw [← hlevelPrev]
            exact hsound.1
          constructor
          · rw [hlevel, hshadow, lowerWindowChain_step r i (by omega),
              lowerWindowProfile_eq_of_le (by omega), ← hprevEq]
          · simpa [hlevel] using hcap
        · contradiction

/-- A successful executable check proves the mathematical capacity predicate. -/
theorem lowerWindowCheck_sound
    {r : ℕ} (hr : 2 ≤ r) (hcheck : lowerWindowCheck r = true) :
    LowerWindowFits r := by
  have hfull : ∃ m, checkedLowerWindowState r (r - 1) = some m := by
    unfold lowerWindowCheck at hcheck
    cases hstate : checkedLowerWindowState r (r - 1) with
    | none => simp [hstate] at hcheck
    | some m => exact ⟨m, rfl⟩
  intro i hi2 hir
  by_cases htop : i = r + 2
  · subst i
    simp
  have hir' : i ≤ r + 1 := by omega
  let d := r + 1 - i
  have hd : d ≤ r - 1 := by dsimp [d]; omega
  obtain ⟨topValue, htopValue⟩ := hfull
  obtain ⟨value, hvalue⟩ := checkedLowerWindowState_some_of_le
    hd htopValue
  have hsound := checkedLowerWindowState_sound hr hd hvalue
  have hlevel : r + 1 - d = i := by dsimp [d]; omega
  rw [← hlevel, ← hsound.1]
  exact hsound.2

end Erdos776.Uniform
