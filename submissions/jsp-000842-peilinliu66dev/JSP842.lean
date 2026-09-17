import JSP842Assembly
import JSP842Ore

/-! A uniform explicit estimate for the original Erdős 1012 threshold question.
This is not a claim of Woodall's sharper threshold or pancyclic conclusion.
The mathematical context predates this AI-assisted formalization. -/
namespace JSP842

def threshold (k : ℕ) : ℕ := 5 * k + 5

theorem erdos_1012_explicit_threshold
    (k n : ℕ) (hn : 5 * k + 5 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (he : (n - k - 1).choose 2 + (k + 2).choose 2 + 1 ≤ G.edgeFinset.card) :
    ∃ v : Fin n, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = n - k := by
  apply threshold_of_ore_closure (fun V _ _ => ?_) k n hn G he
  exact ore_edge_closure

def OriginalStatement : Prop :=
  ∃ f : ℕ → ℕ, ∀ k n : ℕ, f k ≤ n →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (n - k - 1).choose 2 + (k + 2).choose 2 + 1 ≤ G.edgeFinset.card →
      ∃ v : Fin n, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = n - k

theorem erdos_1012 : OriginalStatement := by
  refine ⟨threshold, ?_⟩
  intro k n hn G _ he
  exact erdos_1012_explicit_threshold k n hn G he

#print axioms erdos_1012_explicit_threshold
#print axioms erdos_1012
end JSP842
