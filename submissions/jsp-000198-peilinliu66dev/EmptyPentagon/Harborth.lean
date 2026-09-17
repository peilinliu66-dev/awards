/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Harborth.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Forces
import EmptyPentagon.ES5
import EmptyPentagon.Descent
import EmptyPentagon.CyclicLabel
import EmptyPentagon.Core

noncomputable section
namespace Horton

/-- Harborth (1978): every ten points in general position contain an empty convex pentagon. -/
theorem forcesEmptyKGon_five_ten : ForcesEmptyKGon 5 10 := by
  intro S hcard hgp
  have hex := exists_convex_pentagon S (by omega) hgp
  obtain ⟨V, hVS, hV5, hVci, hfew⟩ := exists_convex_pentagon_few_interior S hgp hex
  have hgpV : GeneralPosition V := fun a ha b hb c hc hab hac hbc =>
    hgp a (hVS ha) b (hVS hb) c (hVS hc) hab hac hbc
  obtain ⟨P, hinj, hPV, hccw⟩ := exists_cyclic_labeling V hV5 hgpV hVci
  have himg : Finset.univ.image P = V := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact hPV i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hV5]
  rw [← himg] at hfew
  exact exists_empty_pentagon_of_few_interior S hcard hgp P hinj (fun i => hVS (hPV i)) hccw hfew

end Horton
