import Erdos776.Combinatorics.ProfileNecessity
import Erdos776.L4.ReverseSteps

/-!
# The semantic L4 theorem

This file turns the numerical recurrence contradiction into a theorem about
actual antichains.  `HasL4MultiplicityProfile r F` says that `F` is an
antichain with at least `r` members on every level `2, ..., r+1`.
-/

namespace Erdos776.L4

open Finset
open Erdos776.KruskalKatona

/-- An antichain carrying the level multiplicities ruled out by L4. -/
def HasL4MultiplicityProfile {n : ℕ} (r : ℕ)
    (F : Finset (Finset (Fin n))) : Prop :=
  IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n))) ∧
    ∀ i, 2 ≤ i → i ≤ r + 1 → r ≤ (levelFamily F i).card

/-- Build the exact top-down numerical recurrence, indexed by distance from the top. -/
def l4DescendingChain (shadow : ℕ → ℕ → ℕ) (r : ℕ) : ℕ → ℕ
  | 0 => r
  | d + 1 => r + shadow (r + 1 - d) (l4DescendingChain shadow r d)

/-- The recurrence indexed by its set-size level. -/
def l4ProfileChain (shadow : ℕ → ℕ → ℕ) (r i : ℕ) : ℕ :=
  l4DescendingChain shadow r (r + 1 - i)

theorem isL4Chain_l4ProfileChain (shadow : ℕ → ℕ → ℕ) (r : ℕ) :
    IsL4Chain shadow r (l4ProfileChain shadow r) := by
  constructor
  · simp [l4ProfileChain, l4DescendingChain]
  · intro i hi hir
    have hdist : r + 1 - i = (r - i) + 1 := by omega
    have hlevel : r + 1 - (r - i) = i + 1 := by omega
    have hnext : r + 1 - (i + 1) = r - i := by omega
    rw [l4ProfileChain, hdist, l4DescendingChain, hlevel]
    rw [l4ProfileChain, hnext]

/--
The necessary half of the profile criterion, specialized to the constant L4
profile but valid on an arbitrary finite ground set.
-/
theorem l4_profile_forces_recurrence
    {n r : ℕ} {F : Finset (Finset (Fin n))}
    (hr : 2 ≤ r) (hF : HasL4MultiplicityProfile r F) :
    ∃ c : ℕ → ℕ,
      IsL4Chain (kkShadow n) r c ∧ c 2 ≤ n.choose 2 := by
  let c : ℕ → ℕ := l4ProfileChain (kkShadow n) r
  have hchain : IsL4Chain (kkShadow n) r c := by
    exact isL4Chain_l4ProfileChain (kkShadow n) r
  have hcumulative :
      ∀ i, 2 ≤ i → i ≤ r + 1 →
        c i ≤ (cumulativeLevel F i).card := by
    intro i hi hir
    apply Nat.decreasingInduction'
        (P := fun k => c k ≤ (cumulativeLevel F k).card)
        (m := i) (n := r + 1) ?_ hir
    · calc
        c (r + 1) = r := hchain.1
        _ ≤ (levelFamily F (r + 1)).card := hF.2 (r + 1) (by omega) (by omega)
        _ ≤ (cumulativeLevel F (r + 1)).card :=
          card_le_card levelFamily_subset_cumulativeLevel
    · intro k hkr hik ih
      have hk2 : 2 ≤ k := hi.trans hik
      have hkle : k ≤ r := by omega
      rw [hchain.2 k hk2 hkle]
      calc
        r + kkShadow n (k + 1) (c (k + 1)) ≤
            r + kkShadow n (k + 1) (cumulativeLevel F (k + 1)).card :=
          Nat.add_le_add_left (kkShadow_mono n (k + 1) ih) r
        _ ≤ (cumulativeLevel F k).card :=
          profile_step_le_cumulativeLevel hF.1 (hF.2 k hk2 (by omega))
  refine ⟨c, hchain, ?_⟩
  exact (hcumulative 2 le_rfl (by omega)).trans card_cumulativeLevel_le_choose

/--
**Theorem L4.** On `r+4` points there is no antichain containing at least
`r` sets of every size from `2` through `r+1`, for any `r ≥ 29`.
-/
theorem l4_multiplicity_profile_infeasible (r : ℕ) (hr : 29 ≤ r) :
    ¬ ∃ F : Finset (Finset (Fin (r + 4))),
      HasL4MultiplicityProfile r F := by
  rintro ⟨F, hF⟩
  obtain ⟨c, hchain, hcapacity⟩ :=
    l4_profile_forces_recurrence (F := F) (by omega) hF
  apply l4_no_recurrence r hr
  exact ⟨c, by simpa [l4Shadow] using hchain, hcapacity⟩

end Erdos776.L4
