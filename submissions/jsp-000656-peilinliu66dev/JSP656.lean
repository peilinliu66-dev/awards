import JSP656Random
import JSP656ChoiceNumber

/-!
# Erdős 799: the list chromatic number of G(n,1/2) is o(n)

The sample space consists of all labelled simple graphs on `Fin n`, each
with equal probability. The invariant is the actual least list-colouring
threshold. `KChoosable.color_lists` shows that quantifying natural-number
lists is equivalent to allowing arbitrary colour types for finite graphs.

Mathematical attribution: Noga Alon (1992), who proved a stronger bound.
This file formalizes the original o(n) conclusion, not a new discovery.
-/

open Filter
open scoped Topology

namespace JSP656

/-- The complete original asymptotic assertion, for every positive epsilon
and every sufficiently large integer size, not just a subsequence. -/
def OriginalStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n : ℕ => fraction (fun G : SimpleGraph (Fin n) =>
      ε * (n : ℝ) < (choiceNumber G : ℝ))) atTop (𝓝 0)

theorem erdos_799 : OriginalStatement := by
  intro ε hε
  apply assembly_from_localHall (fun _ G => choiceNumber G) _ ε hε
  intro m s k n G hm hs hn hRich
  exact choiceNumber_le_of_independent_subsets G m s k hm hs
    (by simpa using hn) hRich

/-- The same statement with the exact number 2^(n choose 2) of labelled
graphs made explicit in the denominator. -/
theorem erdos_799_counting (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      (Nat.card {G : SimpleGraph (Fin n) //
        ε * (n : ℝ) < (choiceNumber G : ℝ)} : ℝ) /
        (2 : ℝ)^(n.choose 2)) atTop (𝓝 0) := by
  classical
  simpa only [OriginalStatement, fraction, Nat.card_eq_fintype_card,
    card_simpleGraphs, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using
    erdos_799 ε hε

#print axioms erdos_799
#print axioms erdos_799_counting

end JSP656
