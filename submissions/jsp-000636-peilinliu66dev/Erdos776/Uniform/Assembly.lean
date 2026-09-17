import Erdos776.Uniform.DiagonalObstruction
import Erdos776.Combinatorics.Padding
import Erdos776.Combinatorics.CoreToFull

/-!
# Conditional assembly of the uniform threshold profile

This file connects the symbolic obstruction and construction layers.  The
remaining mathematical inputs are represented as ordinary propositions, not
axioms: upper-core recurrence data for the obstruction and one suitable free
core for the construction.
-/

namespace Erdos776.Uniform

open Erdos776.Antichain
open Erdos776.KruskalKatona

/-- An antichain with multiplicity at least `r` on every middle level. -/
def FullMiddleProfileExists (n r : ℕ) : Prop :=
  ∃ F : Family (Fin n),
    IsSperner F ∧ HasMultiplicities F r 2 (n - 2)

/--
The exact core interface needed by persistent padding and `coreToFull`.
The core lives on `r+5` points, reaches level `r+2`, and carries at least `r`
free sets of size `r+1`.
-/
def HasSuitableFreeCore (r : ℕ) : Prop :=
  ∃ C D : Family (Fin (r + 5)),
    IsSperner C ∧
      HasMultiplicities C r 2 (r + 2) ∧
      (D : Set (Finset (Fin (r + 5)))).Sized (r + 1) ∧
      r ≤ D.card ∧
      IsFreeFamily C D

/-- The two upper-core facts supplied by Sections 13--14. -/
def HasUpperCoreData (r : ℕ) : Prop :=
  ∃ e : ℕ,
    (∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b ≤ (r + 4).choose b) ∧
    upperCoreChain r 3 = (r + 4).choose 3 + e ∧
    1 ≤ e ∧ e ≤ 6

/-- The obstruction/construction threshold statement for full middle profiles. -/
def FullMiddleProfileThreshold (r : ℕ) : Prop :=
  (¬ FullMiddleProfileExists (2 * r + 5) r) ∧
    ∀ n, 2 * r + 6 ≤ n → FullMiddleProfileExists n r

/-- Generic full-profile threshold event, with an arbitrary last failing size. -/
def FullMiddleProfileThresholdAt (r N : ℕ) : Prop :=
  (¬ FullMiddleProfileExists N r) ∧
    ∀ n, N < n → FullMiddleProfileExists n r

theorem fullMiddleProfileThreshold_iff_at (r : ℕ) :
    FullMiddleProfileThreshold r ↔
      FullMiddleProfileThresholdAt r (2 * r + 5) := by
  simp only [FullMiddleProfileThreshold, FullMiddleProfileThresholdAt]
  constructor <;> rintro ⟨hfail, hsuccess⟩ <;>
    exact ⟨hfail, fun n hn => hsuccess n (by omega)⟩

/-- Any exact overflow of the prescribed-profile recurrence is an obstruction. -/
theorem not_fullMiddleProfileExists_of_chain_overflow
    {n r i : ℕ} (hi2 : 2 ≤ i) (hin : i ≤ n - 2)
    (hoverflow : n.choose i < profileChain (fun _ => r) (n - 2) i) :
    ¬ FullMiddleProfileExists n r := by
  rintro ⟨F, hanti, hprofile⟩
  have hrec := profileChain_isProfileRecurrence_of_antichain
    (n := n) (lo := 2) (hi := n - 2) (f := fun _ => r)
    (F := F) hanti hprofile
  have hcap := hrec.2.2 i hi2 (by omega)
  exact (Nat.not_lt_of_ge hcap) hoverflow

/-- Every natural offset is an even number plus a zero-or-one remainder. -/
theorem exists_two_step_decomposition {base n : ℕ} (hbase : base ≤ n) :
    ∃ t ε : ℕ, ε < 2 ∧ n = base + 2 * t + ε := by
  let d := n - base
  refine ⟨d / 2, d % 2, Nat.mod_lt d (by omega), ?_⟩
  have hsub : base + d = n := by
    dsimp [d]
    omega
  have hdiv := Nat.mod_add_div d 2
  omega

/-- A suitable free core produces the full middle profile at every later size. -/
theorem fullMiddleProfileExists_of_suitableFreeCore
    {r n : ℕ} (hcore : HasSuitableFreeCore r)
    (hn : 2 * r + 6 ≤ n) :
    FullMiddleProfileExists n r := by
  obtain ⟨C, D, hC, hlevels, hDsize, hDcard, hfree⟩ := hcore
  obtain ⟨t, ε, hε, hnform⟩ :=
    exists_two_step_decomposition (base := 2 * r + 6) hn
  have hspec := iteratedPaddingState_spec
    (r := r) (s := r + 2) (by omega) hC hlevels
    (by simpa only [show r + 2 - 1 = r + 1 by omega] using hDsize)
    hDcard hfree t
  let state := iteratedPaddingState C D t
  have hstateAnti : IsSperner state.family := by
    exact hspec.1
  have hstateLevels :
      HasMultiplicities state.family r 2 (r + 2 + t) := by
    exact hspec.2.1
  let G := CoreGround (IteratedGround (Fin (r + 5)) t) r (Fin ε)
  have hcard : Fintype.card G = n := by
    dsimp [G, CoreGround]
    simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
      card_iteratedGround]
    omega
  have hneeded : HasMultiplicities state.family r 2
      (Fintype.card G / 2 - 1) := by
    intro i hi2 hii
    apply hstateLevels i hi2
    rw [hcard] at hii
    have hhalf : n / 2 - 1 ≤ r + 2 + t := by
      omega
    exact hii.trans hhalf
  have hfull := coreToFull_fin
    (α := IteratedGround (Fin (r + 5)) t) (γ := Fin ε) (r := r)
    (C := state.family) (by rw [hcard]; omega) hstateAnti hneeded
  have hcard' : Fintype.card
      (CoreGround (IteratedGround (Fin (r + 5)) t) r (Fin ε)) = n :=
    hcard
  let eFin : Fin (Fintype.card
      (CoreGround (IteratedGround (Fin (r + 5)) t) r (Fin ε))) ↪ Fin n :=
    Fin.castLEEmb hcard'.le
  let F : Family (Fin n) := mapFamily eFin (coreToFullFinFamily
      (α := IteratedGround (Fin (r + 5)) t) (γ := Fin ε) (r := r)
      state.family)
  refine ⟨F, isSperner_mapFamily hfull.1, ?_⟩
  intro i hi2 hin
  unfold HasMultiplicityAt
  simp only [F, card_level_mapFamily]
  exact hfull.2 i hi2 (by simpa only [hcard'] using hin)

/-- The Section 16 theorem expressed through `FullMiddleProfileExists`. -/
theorem not_fullMiddleProfileExists_of_upperCoreData
    (r : ℕ) (hr : 29 ≤ r) (hupper : HasUpperCoreData r) :
    ¬ FullMiddleProfileExists (2 * r + 5) r := by
  obtain ⟨e, hfit, hexcess, heLower, heUpper⟩ := hupper
  intro hfull
  apply upperCore_fit_full_multiplicity_profile_infeasible
    r hr hfit hexcess heLower heUpper
  obtain ⟨F, hanti, hlevels⟩ := hfull
  refine ⟨F, hanti, ?_⟩
  intro i hi2 hii
  exact hlevels i hi2 (by omega)

/--
Pure assembly: once obstruction and a suitable free core are available, all
indices, parity cases, padding stages, and ground-set transports compose.
-/
theorem fullMiddleProfileThreshold_of_components
    {r : ℕ}
    (hobstruction : ¬ FullMiddleProfileExists (2 * r + 5) r)
    (hcore : HasSuitableFreeCore r) :
    FullMiddleProfileThreshold r := by
  exact ⟨hobstruction,
    fun n hn => fullMiddleProfileExists_of_suitableFreeCore hcore hn⟩

/--
Conditional uniform assembly with exactly the two remaining major inputs:
upper-core data and a suitable free core.
-/
theorem uniform_profile_threshold_from_components
    (r : ℕ) (hr : 29 ≤ r)
    (hupper : HasUpperCoreData r)
    (hcore : HasSuitableFreeCore r) :
    FullMiddleProfileThreshold r := by
  exact fullMiddleProfileThreshold_of_components
    (not_fullMiddleProfileExists_of_upperCoreData r hr hupper) hcore

end Erdos776.Uniform
