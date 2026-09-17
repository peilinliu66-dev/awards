import Erdos776.Uniform.FreeCore

/-!
# Reflection and the core carry

This file formalizes Sections 13--14.  The lower-window theorem is exposed as
one semantic feasibility proposition.  Complementing its witness produces the
reflected upper profile; comparison of the two canonical recurrences gives the
upper-core fit and the bound `e ≤ 6`, while semantic L4 forces `e ≥ 1`.
-/

namespace Erdos776.Uniform

open Finset
open Erdos776.Antichain
open Erdos776.KruskalKatona
open Erdos776.L4

/-- The lower-window profile defining the lower bound on `alpha_r`. -/
def lowerWindowProfile (r i : ℕ) : ℕ :=
  if i = r + 1 then r - 6 else r

/-- Semantic form of the sole remaining lower-window input. -/
def LowerWindowFeasible (r : ℕ) : Prop :=
  ∃ F : Family (Fin (r + 4)),
    IsSperner F ∧
      ∀ i, 2 ≤ i → i ≤ r + 1 →
        (level F i).card = lowerWindowProfile r i

/-- The canonical lower-window recurrence used by the finite checker and supersolution. -/
def lowerWindowChain (r : ℕ) : ℕ → ℕ :=
  profileChain (lowerWindowProfile r) (r + 1)

/-- Certificate-facing form of the lower-window theorem: every state fits. -/
def LowerWindowFits (r : ℕ) : Prop :=
  ∀ i, 2 ≤ i → i ≤ r + 2 →
    lowerWindowChain r i ≤ (r + 4).choose i

@[simp] theorem lowerWindowChain_above_top (r : ℕ) :
    lowerWindowChain r (r + 2) = 0 := by
  exact profileChain_top (lowerWindowProfile r) (r + 1)

theorem lowerWindowChain_step (r i : ℕ) (hi : i ≤ r + 1) :
    lowerWindowChain r i = lowerWindowProfile r i +
      canonicalShadow (i + 1) (lowerWindowChain r (i + 1)) := by
  exact profileChain_step (lowerWindowProfile r) hi

/-- Fitting numerical states construct an actual lower-window antichain. -/
theorem lowerWindowFeasible_of_fits
    (r : ℕ) (hfit : LowerWindowFits r) :
    LowerWindowFeasible r := by
  have hrec : IsProfileRecurrence (r + 4) 2 (r + 1)
      (lowerWindowProfile r) (lowerWindowChain r) :=
    ⟨lowerWindowChain_above_top r,
      (fun i _ hi => lowerWindowChain_step r i hi), hfit⟩
  obtain ⟨F, hanti, hprofile, -⟩ :=
    profile_sufficiency (n := r + 4) (lo := 2) (hi := r + 1)
      (f := lowerWindowProfile r) (m := lowerWindowChain r)
      (by omega) hrec
  exact ⟨F, hanti, hprofile⟩

/-- The complemented lower-window profile, supported on levels `3,...,r+2`. -/
def reflectedWindowProfile (r i : ℕ) : ℕ :=
  if i = 3 then r - 6 else r

/-- Its canonical top-down recurrence. -/
def reflectedWindowChain (r : ℕ) : ℕ → ℕ :=
  profileChain (reflectedWindowProfile r) (r + 2)

@[simp] theorem reflectedWindowChain_above_top (r : ℕ) :
    reflectedWindowChain r (r + 3) = 0 := by
  exact profileChain_top (reflectedWindowProfile r) (r + 2)

theorem reflectedWindowChain_step (r i : ℕ) (hi : i ≤ r + 2) :
    reflectedWindowChain r i = reflectedWindowProfile r i +
      canonicalShadow (i + 1) (reflectedWindowChain r (i + 1)) := by
  exact profileChain_step (reflectedWindowProfile r) hi

/-- Above level three, reflection has exactly the upper-core recurrence. -/
theorem reflectedWindowChain_eq_upperCoreChain (r : ℕ) :
    ∀ i, 4 ≤ i → i ≤ r + 3 →
      reflectedWindowChain r i = upperCoreChain r i := by
  intro i hi4 hir
  apply Nat.decreasingInduction'
      (P := fun k => reflectedWindowChain r k = upperCoreChain r k)
      (m := i) (n := r + 3) ?_ hir
  · rw [reflectedWindowChain_above_top, upperCoreChain_above_top]
  · intro k hkr hik ih
    have hk4 : 4 ≤ k := hi4.trans hik
    have hkupper : k ≤ r + 2 := by omega
    rw [reflectedWindowChain_step r k hkupper,
      upperCoreChain_step r k hkupper, ih, reflectedWindowProfile]
    simp [show k ≠ 3 by omega]

/-- The reflected level-three state differs from the core state only in load. -/
theorem reflectedWindowChain_three (r : ℕ) (hr : 2 ≤ r) :
    reflectedWindowChain r 3 =
      (r - 6) + canonicalShadow 4 (upperCoreChain r 4) := by
  rw [reflectedWindowChain_step r 3 (by omega), reflectedWindowProfile,
    if_pos rfl, reflectedWindowChain_eq_upperCoreChain r 4 (by omega) (by omega)]

/-- Complementing a lower-window witness realizes the reflected recurrence. -/
theorem reflectedWindowChain_isProfileRecurrence_of_lowerWindow
    (r : ℕ) (hr : 6 ≤ r) (hwindow : LowerWindowFeasible r) :
    IsProfileRecurrence (r + 4) 3 (r + 2)
      (reflectedWindowProfile r) (reflectedWindowChain r) := by
  obtain ⟨F, hanti, hprofile⟩ := hwindow
  let G : Family (Fin (r + 4)) := Finset.compls F
  have hantiG : IsSperner G := by
    exact isSperner_compls hanti
  apply profileChain_isProfileRecurrence_of_antichain hantiG
  intro i hi3 hir
  have hj2 : 2 ≤ r + 4 - i := by omega
  have hjtop : r + 4 - i ≤ r + 1 := by omega
  have hlevels := hprofile (r + 4 - i) hj2 hjtop
  have hprofiles : reflectedWindowProfile r i =
      lowerWindowProfile r (r + 4 - i) := by
    simp only [reflectedWindowProfile, lowerWindowProfile]
    split_ifs <;> omega
  have hiCard : i ≤ Fintype.card (Fin (r + 4)) := by
    simp
    omega
  have hcompl := card_level_compls (i := i) F hiCard
  have hcompl' : (level G i).card = (level F (r + 4 - i)).card := by
    simpa [G] using hcompl
  rw [hprofiles, ← hlevels, ← hcompl']

/-- Lower-window feasibility supplies every upper-core capacity above level three. -/
theorem upperCoreChain_fit_of_lowerWindow
    (r : ℕ) (hr : 6 ≤ r) (hwindow : LowerWindowFeasible r) :
    ∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b ≤ (r + 4).choose b := by
  have hrec := reflectedWindowChain_isProfileRecurrence_of_lowerWindow
    r hr hwindow
  intro b hb4 hbr
  rw [← reflectedWindowChain_eq_upperCoreChain r b hb4 (by omega)]
  exact hrec.2.2 b (by omega) (by omega)

/-- The reflected level-three capacity says that the core carry is at most six. -/
theorem upperCoreChain_three_le_of_lowerWindow
    (r : ℕ) (hr : 6 ≤ r) (hwindow : LowerWindowFeasible r) :
    upperCoreChain r 3 ≤ (r + 4).choose 3 + 6 := by
  have hrec := reflectedWindowChain_isProfileRecurrence_of_lowerWindow
    r hr hwindow
  have hcap := hrec.2.2 3 le_rfl (by omega)
  rw [reflectedWindowChain_three r (by omega)] at hcap
  have hstep := upperCoreChain_step r 3 (by omega)
  simp only [show 3 + 1 = 4 by omega] at hstep
  omega

/-- If level three also fitted, complementation would produce the forbidden L4 profile. -/
theorem upperCoreChain_three_gt_of_fit
    (r : ℕ) (hr : 29 ≤ r)
    (hfit : ∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b ≤ (r + 4).choose b) :
    (r + 4).choose 3 < upperCoreChain r 3 := by
  by_contra hnot
  have hthree : upperCoreChain r 3 ≤ (r + 4).choose 3 := by omega
  have hrec : IsProfileRecurrence (r + 4) 3 (r + 2)
      (fun _ => r) (upperCoreChain r) := by
    refine ⟨upperCoreChain_above_top r,
      (fun i _ hi => upperCoreChain_step r i hi), ?_⟩
    intro i hi3 hii
    by_cases htop : i = r + 3
    · subst i
      simp
    have hiCore : i ≤ r + 2 := by omega
    by_cases hi : i = 3
    · simpa [hi] using hthree
    · exact hfit i (by omega) hiCore
  obtain ⟨G, hantiG, hprofileG, -⟩ :=
    profile_sufficiency (n := r + 4) (lo := 3) (hi := r + 2)
      (f := fun _ => r) (m := upperCoreChain r) (by omega) hrec
  apply l4_multiplicity_profile_infeasible r hr
  refine ⟨Finset.compls G, ?_⟩
  constructor
  · exact isSperner_compls hantiG
  · intro i hi2 hir
    have hj3 : 3 ≤ r + 4 - i := by omega
    have hjtop : r + 4 - i ≤ r + 2 := by omega
    have hiCard : i ≤ Fintype.card (Fin (r + 4)) := by
      simp
      omega
    have hcompl := card_level_compls (i := i) G hiCard
    have hcompl' : (level (Finset.compls G) i).card =
        (level G (r + 4 - i)).card := by
      simpa using hcompl
    rw [levelFamily_eq_level, hcompl',
      hprofileG (r + 4 - i) hj3 hjtop]

/-- Lower-window feasibility implies the complete upper-core data package. -/
theorem hasUpperCoreData_of_lowerWindowFeasible
    (r : ℕ) (hr : 29 ≤ r) (hwindow : LowerWindowFeasible r) :
    HasUpperCoreData r := by
  have hfit := upperCoreChain_fit_of_lowerWindow r (by omega) hwindow
  have hlower := upperCoreChain_three_gt_of_fit r hr hfit
  have hupper := upperCoreChain_three_le_of_lowerWindow r (by omega) hwindow
  let e := upperCoreChain r 3 - (r + 4).choose 3
  refine ⟨e, hfit, ?_, ?_, ?_⟩
  · dsimp [e]
    omega
  · dsimp [e]
    omega
  · dsimp [e]
    omega

/-- The entire symbolic middle-profile threshold now follows from the lower window. -/
theorem fullMiddleProfileThreshold_of_lowerWindowFeasible
    (r : ℕ) (hr : 29 ≤ r) (hwindow : LowerWindowFeasible r) :
    FullMiddleProfileThreshold r := by
  exact fullMiddleProfileThreshold_of_upperCoreData r hr
    (hasUpperCoreData_of_lowerWindowFeasible r hr hwindow)

/-- Certificate-facing final endpoint: only the lower-window capacities remain. -/
theorem fullMiddleProfileThreshold_of_lowerWindowFits
    (r : ℕ) (hr : 29 ≤ r) (hfit : LowerWindowFits r) :
    FullMiddleProfileThreshold r := by
  exact fullMiddleProfileThreshold_of_lowerWindowFeasible r hr
    (lowerWindowFeasible_of_fits r hfit)

end Erdos776.Uniform
