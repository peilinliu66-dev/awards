/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Monotone.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Forces
import EmptyPentagon.HullVertex

noncomputable section
namespace Horton

/-- Removing a hull vertex preserves emptiness of every polygon of the remaining points. -/
theorem forcesEmptyKGon_succ (k n : ℕ) (h : ForcesEmptyKGon k n) :
    ForcesEmptyKGon k (n + 1) := by
  intro S hcard hgp
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hpS, hp⟩ := exists_hull_vertex S hne
  have hcard' : (S.erase p).card = n := by
    rw [Finset.card_erase_of_mem hpS, hcard]; rfl
  have hgp' : GeneralPosition (S.erase p) := fun a ha b hb c hc =>
    hgp a (Finset.erase_subset p S ha) b (Finset.erase_subset p S hb) c
      (Finset.erase_subset p S hc)
  obtain ⟨V, hVcard, hVsub, hVconv, hVempty⟩ := h (S.erase p) hcard' hgp'
  have hVS : V ⊆ S := hVsub.trans (Finset.erase_subset p S)
  refine ⟨V, hVcard, hVS, hVconv, fun q hqS hqV => ?_⟩
  by_cases hqp : q = p
  · subst hqp
    exact hp V hVS
  · exact hVempty q (Finset.mem_erase.mpr ⟨hqp, hqS⟩) hqV

/-- Upward closure of the forcing property. -/
theorem forcesEmptyKGon_of_le {k m n : ℕ} (h : ForcesEmptyKGon k m) (hmn : m ≤ n) :
    ForcesEmptyKGon k n := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact forcesEmptyKGon_succ k n ih

/-- Downward closure of the non-forcing property. -/
theorem not_forcesEmptyKGon_of_le {k m n : ℕ} (h : ¬ ForcesEmptyKGon k m) (hnm : n ≤ m) :
    ¬ ForcesEmptyKGon k n :=
  fun h' => h (forcesEmptyKGon_of_le h' hnm)

end Horton
