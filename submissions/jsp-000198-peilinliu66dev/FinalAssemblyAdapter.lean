/-
Released under the MIT license.
JSP198 / Erdos 216 final integration adapter.

CONDITIONAL ON ONLY THE REMAINING CASE I.A CORE.
This file is not an unconditional solution of the original problem.
It reuses the credited small-k and Horton developments and the verified
local Nicolas geometry, ES25, Case II, I.C, scope bridge, and I.B modules.
No new geometric premise is added to the remaining Case I.A interface.
-/
import HexagonNormalization
import HortonBranch
import EmptyPentagon.SmallHoles
import JSP198NicolasCaseIScopeBridge
import JSP198NicolasCaseIB

noncomputable section
open Classical Horton

namespace JSP198.FinalAssembly
open Nicolas

/-- The single outstanding mathematical obligation. The singleton-fiber
condition concerns only vertices on the actual run; the remaining vertices
are unrestricted. This is a proposition to be proved, not an axiom. -/
def RemainingCaseIACore : Prop :=
  ∀ (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (R : ActualCaseIRun P hgp o ho),
    RunHasSingletonSectors R →
    R.length + 3 ≤ (ChainSecond P).card → HasEmptySix P

/-- Conditional only on I.A: the other actual-run branches are already proved. -/
theorem four_layer_finish_conditional (hIA : RemainingCaseIACore)
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) : HasEmptySix P := by
  rcases emptySix_or_short_actual_singleton_run P hgp hmin o ho with hSix | hRun
  · exact hSix
  · obtain ⟨R, hsize, hsingle⟩ := hRun
    have hs : RunHasSingletonSectors R := by
      intro j hj s he
      exact hsingle ⟨j, by omega⟩ s he
    rcases hsize with hA | hB
    · exact hIA P hgp hmin o ho R hs hA
    · exact hasEmptySix_of_caseIB_run P hgp hmin o ho R hs hB

/-- ES25, safe ambient restriction, the proved three-layer branch, and the
conditional four-layer finish imply the finite empty-hexagon upper bound. -/
theorem hasEmptySix_at_bound_conditional (hIA : RemainingCaseIACore)
    (P : Finset Point) (hcard : es25Bound ≤ P.card)
    (hgp : GeneralPosition P) : HasEmptySix P := by
  by_contra hno
  obtain ⟨Q, _, hgpQ, hmin, houter, hnoQ⟩ :=
    hexagon_free_minimal25_reduction P hcard hgp hno
  apply hnoQ
  by_cases hthree : inner (inner (inner Q)) = ∅
  · exact hasEmptySix_of_three_layers Q hgpQ (by omega) hthree
  · obtain ⟨o, ho⟩ := Finset.nonempty_iff_ne_empty.mpr hthree
    exact four_layer_finish_conditional hIA Q hgpQ hmin o ho

/-- The same six-gon bound in the original at-least-N model. -/
theorem original_six_bound_conditional (hIA : RemainingCaseIACore) :
    Prize.Geometry.ForcesEmptyKGon es25Bound 6 := by
  intro P hcard hgp
  apply (ModelBridge.hasEmptyKGon_iff 6 P).mp
  exact hasEmptySix_at_bound_conditional hIA P hcard
    ((ModelBridge.generalPosition_iff P).mpr hgp)

/-- The existing exact small values, transported without a core assumption. -/
theorem original_small_exact :
    (∀ N, Prize.Geometry.ForcesEmptyKGon N 3 ↔ 3 ≤ N) ∧
    (∀ N, Prize.Geometry.ForcesEmptyKGon N 4 ↔ 5 ≤ N) ∧
    (∀ N, Prize.Geometry.ForcesEmptyKGon N 5 ↔ 10 ≤ N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N
    exact (ModelBridge.forcesEmptyKGon_iff 3 N).symm.trans
      (forces_empty_triangle_iff N)
  · intro N
    exact (ModelBridge.forcesEmptyKGon_iff 4 N).symm.trans
      (forces_empty_quadrilateral_iff N)
  · intro N
    exact (ModelBridge.forcesEmptyKGon_iff 5 N).symm.trans
      (forces_empty_pentagon_iff N)

/-- Arbitrarily large counterexamples for every k >= 7, including integer
coordinates. This branch is unconditional and inherited from Horton. -/
theorem original_large_counterexamples (k : ℕ) (hk : 7 ≤ k) (N : ℕ) :
    ∃ P : Finset Point, P.card = N ∧
      Prize.Geometry.GeneralPosition (P : Set Point) ∧
      ¬ Prize.Geometry.HasEmptyKGon k P ∧
      (∀ q ∈ P, ∃ x y : ℤ, q = ((x : ℝ), (y : ℝ))) := by
  obtain ⟨P, hcard, hgp, hno, hinteger⟩ := horton_counterexamples N k hk
  refine ⟨P, hcard, (ModelBridge.generalPosition_iff P).mp hgp, ?_, hinteger⟩
  intro h
  exact hno ((ModelBridge.hasEmptyKGon_iff k P).mpr h)

/-- A true least hexagon threshold exists below the explicit finite bound,
conditional only on I.A. No numerical claim g(6)=30 is made. -/
theorem original_six_threshold_conditional (hIA : RemainingCaseIACore) :
    ∃ g6 : ℕ, g6 ≤ es25Bound ∧
      ∀ N, Prize.Geometry.ForcesEmptyKGon N 6 ↔ g6 ≤ N := by
  have hbound := original_six_bound_conditional hIA
  have hex : ∃ N, Prize.Geometry.ForcesEmptyKGon N 6 := ⟨es25Bound, hbound⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hbound, ?_⟩
  intro N
  constructor
  · exact Nat.find_min' hex
  · intro hN P hcard hgp
    exact Nat.find_spec hex P (hN.trans hcard) hgp

/-- Complete finite-versus-infinite classification for the original range k>=3.
The sole unproved input is explicitly visible as `hIA`. -/
theorem finite_threshold_iff_conditional (hIA : RemainingCaseIACore)
    (k : ℕ) (hk : 3 ≤ k) :
    (∃ N, Prize.Geometry.ForcesEmptyKGon N k) ↔ k ≤ 6 := by
  constructor
  · rintro ⟨N, hN⟩
    by_contra hn
    have hk7 : 7 ≤ k := by omega
    exact no_horton_threshold hk7 N ((ModelBridge.forcesEmptyKGon_iff k N).mpr hN)
  · intro hk6
    have hcases : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact ⟨3, (original_small_exact.1 3).mpr (le_refl _)⟩
    · exact ⟨5, (original_small_exact.2.1 5).mpr (le_refl _)⟩
    · exact ⟨10, (original_small_exact.2.2 10).mpr (le_refl _)⟩
    · exact ⟨es25Bound, original_six_bound_conditional hIA⟩

/-- All requested branches in a single original-model statement.
CONDITIONAL: instantiate `hIA` with the future complete I.A proof before any
unconditional solution or award-submission claim. -/
theorem erdos216_classification_conditional (hIA : RemainingCaseIACore) :
    (∀ N, Prize.Geometry.ForcesEmptyKGon N 3 ↔ 3 ≤ N) ∧
    (∀ N, Prize.Geometry.ForcesEmptyKGon N 4 ↔ 5 ≤ N) ∧
    (∀ N, Prize.Geometry.ForcesEmptyKGon N 5 ↔ 10 ≤ N) ∧
    (∃ g6 : ℕ, g6 ≤ es25Bound ∧
      ∀ N, Prize.Geometry.ForcesEmptyKGon N 6 ↔ g6 ≤ N) ∧
    (∀ k, 7 ≤ k → ∀ N, ∃ P : Finset Point, P.card = N ∧
      Prize.Geometry.GeneralPosition (P : Set Point) ∧
      ¬ Prize.Geometry.HasEmptyKGon k P ∧
      (∀ q ∈ P, ∃ x y : ℤ, q = ((x : ℝ), (y : ℝ)))) := by
  exact ⟨original_small_exact.1, original_small_exact.2.1,
    original_small_exact.2.2, original_six_threshold_conditional hIA,
    original_large_counterexamples⟩

end JSP198.FinalAssembly

-- Standard axiom output here does not discharge the explicit hIA parameter.
#print axioms JSP198.FinalAssembly.original_small_exact
#print axioms JSP198.FinalAssembly.original_large_counterexamples
#print axioms JSP198.FinalAssembly.four_layer_finish_conditional
#print axioms JSP198.FinalAssembly.original_six_threshold_conditional
#print axioms JSP198.FinalAssembly.finite_threshold_iff_conditional
#print axioms JSP198.FinalAssembly.erdos216_classification_conditional
