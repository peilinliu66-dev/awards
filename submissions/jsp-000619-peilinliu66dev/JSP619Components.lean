import JSP619Basic

/-!
# Explicit nonempty connected-component restriction

Minimum degree is preserved, and all cycles map injectively
back to the original graph. No connectedness assumption is added to the problem.
-/
noncomputable section
open Finset Function
namespace JSP619
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The vertex set of the component of r. -/
def componentVertices (G : SimpleGraph V) (r : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Reachable r)

@[simp] lemma mem_componentVertices {G : SimpleGraph V} {r v : V} :
    v ∈ componentVertices G r ↔ G.Reachable r v := by
  classical
  simp [componentVertices]

lemma root_mem_component (G : SimpleGraph V) (r : V) :
    r ∈ componentVertices G r := mem_componentVertices.mpr .rfl

lemma component_closed (G : SimpleGraph V) (r : V) {v w : V}
    (hv : v ∈ componentVertices G r) (hvw : G.Adj v w) :
    w ∈ componentVertices G r :=
  mem_componentVertices.mpr ((mem_componentVertices.mp hv).trans hvw.reachable)

/-- Lift a walk to an explicitly neighbor-closed finite vertex set. -/
def liftClosedWalk (G : SimpleGraph V) (A : Finset V)
    (hclosed : ∀ v ∈ A, ∀ w, G.Adj v w → w ∈ A) :
    {a b : V} → (p : G.Walk a b) → (ha : a ∈ A) → (hb : b ∈ A) →
      (induced G A).Walk ⟨a, ha⟩ ⟨b, hb⟩
  | _, _, .nil, _, _ => .nil
  | a, b, .cons (v := w) h p, ha, hb =>
      SimpleGraph.Walk.cons
        (show (induced G A).Adj ⟨a, ha⟩ ⟨w, hclosed a ha w h⟩ from h)
        (liftClosedWalk G A hclosed p (hclosed a ha w h) hb)

lemma component_connected (G : SimpleGraph V) (r : V) :
    (induced G (componentVertices G r)).Connected := by
  let A := componentVertices G r
  letI : Nonempty ↥A := ⟨⟨r, root_mem_component G r⟩⟩
  refine ⟨?_⟩
  intro a b
  have hr : G.Reachable a.1 b.1 :=
    (mem_componentVertices.mp a.2).symm.trans (mem_componentVertices.mp b.2)
  obtain ⟨p⟩ := hr
  exact ⟨liftClosedWalk G A (fun _ hv _ h => component_closed G r hv h) p a.2 b.2⟩

lemma component_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (v : ↥(componentVertices G r)) :
    (induced G (componentVertices G r)).degree v = G.degree v.1 := by
  classical
  rw [induced_degree, ← degIn_univ G v.1]
  apply congrArg Finset.card
  ext w
  simp only [mem_neighborsIn, Finset.mem_univ, true_and]
  exact ⟨And.right, fun h => ⟨component_closed G r v.2 h, h⟩⟩

end JSP619
end
