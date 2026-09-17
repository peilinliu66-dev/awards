import Erdos776.Combinatorics.ProfileNecessity
import Erdos776.Combinatorics.ProfileSufficiency

/-!
# The prescribed-profile criterion

This file packages the generic necessity and sufficiency arguments into the
exact iff statement used in the manuscripts.  It concerns profiles supported
on a nonempty interval `lo..hi` with `lo ≥ 1`.
-/

namespace Erdos776.KruskalKatona

open Finset
open Erdos776.Antichain

/-- The exact top-down recurrence associated with a profile. -/
def profileDescending (f : ℕ → ℕ) (hi : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 =>
      f (hi - d) +
        canonicalShadow (hi - d + 1) (profileDescending f hi d)

/-- Reindex the descending recurrence by the actual set-size level. -/
def profileChain (f : ℕ → ℕ) (hi i : ℕ) : ℕ :=
  profileDescending f hi (hi + 1 - i)

@[simp] theorem profileChain_top (f : ℕ → ℕ) (hi : ℕ) :
    profileChain f hi (hi + 1) = 0 := by
  simp [profileChain, profileDescending]

theorem profileChain_step (f : ℕ → ℕ) {hi i : ℕ} (hi_le : i ≤ hi) :
    profileChain f hi i =
      f i + canonicalShadow (i + 1) (profileChain f hi (i + 1)) := by
  have hdist : hi + 1 - i = (hi - i) + 1 := by omega
  have hlevel : hi - (hi - i) = i := by omega
  have hnext : hi + 1 - (i + 1) = hi - i := by omega
  rw [profileChain, hdist, profileDescending, hlevel]
  rw [profileChain, hnext]

theorem levelFamily_eq_level {n i : ℕ}
    (F : Finset (Finset (Fin n))) :
    levelFamily F i = Erdos776.Antichain.level F i := by
  rfl

/--
Generic necessity: every antichain carrying at least the proposed profile
forces every state of its canonical recurrence to fit inside the corresponding
level of `Fin n`.
-/
theorem profile_necessity
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (htop : m (hi + 1) = 0)
    (hstep : ∀ i, lo ≤ i → i ≤ hi →
      m i = f i + canonicalShadow (i + 1) (m (i + 1)))
    {F : Family (Fin n)}
    (hanti : IsSperner F)
    (hprofile : ∀ i, lo ≤ i → i ≤ hi → f i ≤ (level F i).card) :
    IsProfileRecurrence n lo hi f m := by
  have hcumulative :
      ∀ i, lo ≤ i → i ≤ hi + 1 →
        m i ≤ (cumulativeLevel F i).card := by
    intro i hloi hihi
    apply Nat.decreasingInduction'
        (P := fun k => m k ≤ (cumulativeLevel F k).card)
        (m := i) (n := hi + 1) ?_ hihi
    · rw [htop]
      omega
    · intro k hkhi hik ih
      have hlok : lo ≤ k := hloi.trans hik
      have hkhi' : k ≤ hi := by omega
      rw [hstep k hlok hkhi']
      have hmono := canonicalShadow_mono (k + 1) (by omega) ih
      have hcap : (cumulativeLevel F (k + 1)).card ≤
          n.choose (k + 1) := card_cumulativeLevel_le_choose
      have hshadowEq := kkShadow_eq_canonicalShadow (by omega) hcap
      have hlevel : f k ≤ (levelFamily F k).card := by
        rw [levelFamily_eq_level]
        exact hprofile k hlok hkhi'
      have hprofileStep := profile_step_le_cumulativeLevel hanti hlevel
      rw [hshadowEq] at hprofileStep
      exact (Nat.add_le_add_left hmono (f k)).trans hprofileStep
  refine ⟨htop, hstep, ?_⟩
  intro i hloi hihi
  exact (hcumulative i hloi hihi).trans card_cumulativeLevel_le_choose

/-- The canonical recurrence is feasible whenever the requested antichain exists. -/
theorem profileChain_isProfileRecurrence_of_antichain
    {n lo hi : ℕ} {f : ℕ → ℕ}
    {F : Family (Fin n)}
    (hanti : IsSperner F)
    (hprofile : ∀ i, lo ≤ i → i ≤ hi → f i ≤ (level F i).card) :
    IsProfileRecurrence n lo hi f (profileChain f hi) := by
  apply profile_necessity (profileChain_top f hi)
      (fun i _ hi_i => profileChain_step f hi_i) hanti hprofile

/--
The classical prescribed-profile criterion: an exact finite antichain profile
exists iff its top-down canonical recurrence fits in every level.
-/
theorem profile_criterion
    {n lo hi : ℕ} {f : ℕ → ℕ} (hlo : 1 ≤ lo) :
    (∃ F : Family (Fin n),
      IsSperner F ∧
        (∀ i, lo ≤ i → i ≤ hi → (level F i).card = f i) ∧
        ∀ s ∈ F, s.card ∈ Finset.Icc lo hi) ↔
      ∃ m : ℕ → ℕ, IsProfileRecurrence n lo hi f m := by
  constructor
  · rintro ⟨F, hanti, hprofile, hsupport⟩
    refine ⟨profileChain f hi,
      profileChain_isProfileRecurrence_of_antichain hanti ?_⟩
    intro i hloi hihi
    rw [hprofile i hloi hihi]
  · rintro ⟨m, hrec⟩
    exact profile_sufficiency hlo hrec

end Erdos776.KruskalKatona
