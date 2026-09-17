import ModelBridge
import Prize.Horton

/-!
# The full k ≥ 7 branch in the common Horton model

The construction is the credited MIT-licensed upstream Horton formalization.
ModelBridge transports its geometric predicates exactly; no new construction
or mathematical discovery is claimed.
-/

noncomputable section
namespace JSP198

theorem horton_counterexamples (N k : ℕ) (hk : 7 ≤ k) :
    ∃ P : Finset Horton.Point, P.card = N ∧ Horton.GeneralPosition P ∧
      ¬ (∃ V : Finset Horton.Point,
        V.card = k ∧ Horton.EmptyConvexPolygon P V) ∧
      (∀ q ∈ P, ∃ x y : ℤ, q = ((x : ℝ), (y : ℝ))) := by
  obtain ⟨P, hcard, hgp, hno, hinteger⟩ :=
    Prize.Horton.horton_no_empty_k_gon N k hk
  refine ⟨P, hcard, (ModelBridge.generalPosition_iff P).mpr hgp, ?_, hinteger⟩
  intro h
  exact hno ((ModelBridge.hasEmptyKGon_iff k P).mp h)

theorem no_horton_threshold {k : ℕ} (hk : 7 ≤ k) :
    ∀ N, ¬ Horton.ForcesEmptyKGon k N := by
  intro N h
  exact Prize.Horton.no_finite_threshold hk N
    ((ModelBridge.forcesEmptyKGon_iff k N).mp h)

end JSP198

#print axioms JSP198.horton_counterexamples
#print axioms JSP198.no_horton_threshold
