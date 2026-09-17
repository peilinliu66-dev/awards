import JSP619Basic
import JSP619LocalExpansion

/-! Interfaces for the assembly, discharged by independently compiled Moore,
small-set expansion, and finite DFS proofs. -/

noncomputable section
open Finset Function
namespace JSP619
universe u

def MooreBound : Prop :=
  ∀ (V : Type u) [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d s : ℕ),
    0 < d → 0 < s → (∀ v, d + 1 ≤ G.degree v) → HighGirth G s →
    d ^ s < Fintype.card V

theorem mooreBound_proved : MooreBound.{u} := by
  intro V _ _ G _ d s hd hs hdeg hgirth
  classical
  exact moore_card_gt_pow G d s hd hs hdeg hgirth

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem boundary_eq_externalNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : boundary G S = externalNeighbors G S := by
  classical
  ext v
  simp [boundary, externalNeighbors]

theorem boundary_gt_twice_of_moore (_hMoore : MooreBound.{u})
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d s : ℕ) (hd : 0 < d) (hs : 0 < s)
    (hdeg : ∀ v, 6 * (d + 1) ≤ G.degree v) (hgirth : HighGirth G s)
    (X : Finset V) (hX : X.Nonempty) (hsize : 3 * X.card ≤ d ^ s) :
    2 * X.card < (boundary G X).card := by
  rw [boundary_eq_externalNeighbors]
  exact small_set_expansion G d s hd hs hdeg hgirth X hX.card_pos hsize

theorem long_path_of_minDegree (hMoore : MooreBound.{u})
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (d s m : ℕ) (hd : 0 < d) (hs : 0 < s) (hm : 0 < m)
    (hdeg : ∀ v, 6 * (d + 1) ≤ G.degree v) (hgirth : HighGirth G s)
    (hmsize : 3 * m ≤ d ^ s) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ 2 * m ≤ p.length := by
  have hcard := hMoore V G d s hd hs (fun v => by have := hdeg v; omega) hgirth
  apply exists_long_path_of_expansion G m hm (by omega)
  intro S hS
  simpa [hS] using
    small_set_expansion G d s hd hs hdeg hgirth S (by omega) (by omega)

#print axioms mooreBound_proved
#print axioms long_path_of_minDegree
end JSP619
