import Mathlib

/-!
An elementary depth-first search certificate: expansion of every set of `m`
vertices gives a simple path with at least `2*m` edges.  The search is proved
terminating by the rank `2 * unseen.card + stack.length`.
-/

namespace JSP619

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Neighbors outside a given finite vertex set. -/
def externalNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset V :=
  (univ \ S).filter fun v => ∃ u ∈ S, G.Adj u v

namespace DFS

def Chain (G : SimpleGraph V) : List V → Prop
  | [] => True
  | [_] => True
  | u :: v :: tail => G.Adj u v ∧ Chain G (v :: tail)

theorem chain_tail {G : SimpleGraph V} {u : V} {l : List V}
    (h : Chain G (u :: l)) : Chain G l := by
  cases l with
  | nil => trivial
  | cons v tail => exact h.2

/-- Turn a list of distinct consecutive adjacent vertices into a genuine walk. -/
theorem chain_walk {G : SimpleGraph V} {u : V} {l : List V}
    (hnodup : (u :: l).Nodup) (hchain : Chain G (u :: l)) :
    ∃ v : V, ∃ p : G.Walk u v, p.support = u :: l ∧ p.IsPath := by
  induction l generalizing u with
  | nil =>
    exact ⟨u, .nil, rfl, SimpleGraph.Walk.IsPath.nil⟩
  | cons v tail ih =>
    have hnd := List.nodup_cons.mp hnodup
    obtain ⟨w, p, hp, hpath⟩ := ih hnd.2 hchain.2
    refine ⟨w, .cons hchain.1 p, ?_, ?_⟩
    · simp [SimpleGraph.Walk.support_cons, hp]
    · apply SimpleGraph.Walk.IsPath.mk'
      simpa [SimpleGraph.Walk.support_cons, hp] using hnodup

structure State (V : Type*) where
  S : Finset V
  T : Finset V
  U : List V

/-- Finished vertices, unseen vertices, and the search stack form a partition.
There is no edge from a finished vertex to an unseen vertex. -/
structure Valid (G : SimpleGraph V) (z : State V) : Prop where
  nodup : z.U.Nodup
  st : ∀ v ∈ z.S, v ∉ z.T
  su : ∀ v ∈ z.S, v ∉ z.U
  tu : ∀ v ∈ z.T, v ∉ z.U
  size : z.S.card + z.T.card + z.U.length = Fintype.card V
  cover : ∀ v, v ∈ z.S ∨ v ∈ z.T ∨ v ∈ z.U
  chain : Chain G z.U
  cut : ∀ v ∈ z.S, ∀ w ∈ z.T, ¬ G.Adj v w

def initial : State V := ⟨∅, univ, []⟩

theorem initial_valid (G : SimpleGraph V) : Valid G (initial : State V) := by
  constructor <;> simp [initial, Chain]

def root (z : State V) (v : V) : State V :=
  { z with T := z.T.erase v, U := [v] }

def pop (z : State V) (v : V) (tail : List V) : State V :=
  { z with S := insert v z.S, U := tail }

def push (z : State V) (w : V) : State V :=
  { z with T := z.T.erase w, U := w :: z.U }

theorem root_valid {G : SimpleGraph V} {z : State V} (h : Valid G z)
    (hU : z.U = []) {v : V} (hv : v ∈ z.T) : Valid G (root z v) := by
  have ht : (z.T.erase v).card + 1 = z.T.card := by
    rw [Finset.card_erase_of_mem hv]
    have := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  constructor
  · simp [root]
  · intro w hw hwt
    exact h.st w hw (Finset.mem_erase.mp hwt).2
  · intro w hw hwU
    have : w = v := by simpa [root] using hwU
    subst w
    exact h.st v hw hv
  · intro w hw hwU
    have : w = v := by simpa [root] using hwU
    subst w
    exact (Finset.mem_erase.mp hw).1 rfl
  · have hs := h.size
    simp only [hU, List.length_nil] at hs
    simp only [root, List.length_singleton]
    omega
  · intro w
    rcases h.cover w with hw | hw | hw
    · exact Or.inl hw
    · by_cases heq : w = v
      · exact Or.inr (Or.inr (by simp [root, heq]))
      · exact Or.inr (Or.inl (Finset.mem_erase.mpr ⟨heq, hw⟩))
    · simpa [hU] using hw
  · trivial
  · intro w hw x hx
    exact h.cut w hw x (Finset.mem_erase.mp hx).2

theorem pop_valid {G : SimpleGraph V} {z : State V} (h : Valid G z)
    {v : V} {tail : List V} (hU : z.U = v :: tail)
    (hall : ∀ w ∈ z.T, ¬ G.Adj v w) : Valid G (pop z v tail) := by
  have hvS : v ∉ z.S := by
    intro hv
    exact h.su v hv (by simp [hU])
  have hvT : v ∉ z.T := by
    intro hv
    exact h.tu v hv (by simp [hU])
  have hnd : v ∉ tail ∧ tail.Nodup := by
    simpa [hU] using h.nodup
  have hSc : (insert v z.S).card = z.S.card + 1 := Finset.card_insert_of_notMem hvS
  constructor
  · exact hnd.2
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hvT
    · exact h.st w hw
  · intro w hw hwt
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hnd.1 hwt
    · exact h.su w hw (by simpa only [hU, List.mem_cons] using (Or.inr (show w ∈ tail from hwt)))
  · intro w hw hwt
    exact h.tu w hw (by simpa only [hU, List.mem_cons] using (Or.inr (show w ∈ tail from hwt)))
  · have hs := h.size
    simp only [hU, List.length_cons] at hs
    simp only [pop, hSc]
    omega
  · intro w
    rcases h.cover w with hw | hw | hw
    · exact Or.inl (Finset.mem_insert_of_mem hw)
    · exact Or.inr (Or.inl hw)
    · rw [hU, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact Or.inl (Finset.mem_insert_self _ _)
      · exact Or.inr (Or.inr hw)
  · change Chain G tail
    apply chain_tail
    simpa [hU] using h.chain
  · intro w hw x hx
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hall x hx
    · exact h.cut w hw x hx

theorem push_valid {G : SimpleGraph V} {z : State V} (h : Valid G z)
    {v w : V} {tail : List V} (hU : z.U = v :: tail)
    (hw : w ∈ z.T) (hadj : G.Adj v w) : Valid G (push z w) := by
  have hwU : w ∉ z.U := h.tu w hw
  have hwS : w ∉ z.S := by intro hs; exact h.st w hs hw
  have hTc : (z.T.erase w).card + 1 = z.T.card := by
    rw [Finset.card_erase_of_mem hw]
    have := Finset.card_pos.mpr ⟨w, hw⟩
    omega
  constructor
  · simpa [push] using List.nodup_cons.mpr ⟨hwU, h.nodup⟩
  · intro x hx hxt
    exact h.st x hx (Finset.mem_erase.mp hxt).2
  · intro x hx hxU
    rcases List.mem_cons.mp hxU with rfl | hxU
    · exact hwS hx
    · exact h.su x hx hxU
  · intro x hx hxU
    rcases List.mem_cons.mp hxU with rfl | hxU
    · exact (Finset.mem_erase.mp hx).1 rfl
    · exact h.tu x (Finset.mem_erase.mp hx).2 hxU
  · have hs := h.size
    simp only [push, List.length_cons]
    omega
  · intro x
    rcases h.cover x with hx | hx | hx
    · exact Or.inl hx
    · by_cases heq : x = w
      · exact Or.inr (Or.inr (by simp [push, heq]))
      · exact Or.inr (Or.inl (Finset.mem_erase.mpr ⟨heq, hx⟩))
    · exact Or.inr (Or.inr (List.mem_cons_of_mem w hx))
  · change Chain G (w :: z.U)
    rw [hU]
    exact ⟨hadj.symm, by simpa [hU] using h.chain⟩
  · intro x hx y hy
    exact h.cut x hx y (Finset.mem_erase.mp hy).2

/-- DFS can be stopped after exactly `m` vertices have been finished. -/
theorem reach_finished (G : SimpleGraph V) (m : ℕ) (hm : m ≤ Fintype.card V)
    (z : State V) (hz : Valid G z) (hsz : z.S.card ≤ m) :
    ∃ z' : State V, Valid G z' ∧ z'.S.card = m := by
  classical
  generalize hmeasure : 2 * z.T.card + z.U.length = r
  induction r using Nat.strong_induction_on generalizing z with
  | h r ih =>
    by_cases hsm : z.S.card = m
    · exact ⟨z, hz, hsm⟩
    have hslt : z.S.card < m := by omega
    cases hU : z.U with
    | nil =>
      have hT : z.T.Nonempty := by
        apply Finset.card_pos.mp
        have hsize := hz.size
        simp only [hU, List.length_nil] at hsize
        omega
      obtain ⟨v, hv⟩ := hT
      have hTc : (z.T.erase v).card + 1 = z.T.card := by
        rw [Finset.card_erase_of_mem hv]
        have := Finset.card_pos.mpr ⟨v, hv⟩
        omega
      have hdec : 2 * (root z v).T.card + (root z v).U.length < r := by
        simp only [root, List.length_singleton]
        simp only [hU, List.length_nil] at hmeasure
        omega
      exact ih _ hdec (root z v) (root_valid hz hU hv) hsz rfl
    | cons v tail =>
      by_cases hnext : ∃ w ∈ z.T, G.Adj v w
      · obtain ⟨w, hw, hadj⟩ := hnext
        have hTc : (z.T.erase w).card + 1 = z.T.card := by
          rw [Finset.card_erase_of_mem hw]
          have := Finset.card_pos.mpr ⟨w, hw⟩
          omega
        have hdec : 2 * (push z w).T.card + (push z w).U.length < r := by
          simp only [push, List.length_cons]
          omega
        exact ih _ hdec (push z w) (push_valid hz hU hw hadj) hsz rfl
      · have hall : ∀ w ∈ z.T, ¬ G.Adj v w := by
          intro w hw hadj
          exact hnext ⟨w, hw, hadj⟩
        have hvS : v ∉ z.S := by
          intro hv
          exact hz.su v hv (by simp [hU])
        have hSc : (insert v z.S).card = z.S.card + 1 :=
          Finset.card_insert_of_notMem hvS
        have hdec : 2 * (pop z v tail).T.card + (pop z v tail).U.length < r := by
          simp only [pop]
          simp only [hU, List.length_cons] at hmeasure
          omega
        have hsnew : (pop z v tail).S.card ≤ m := by
          simp only [pop, hSc]
          omega
        exact ih _ hdec (pop z v tail) (pop_valid hz hU hall) hsnew rfl

end DFS

/-- Small-set vertex expansion produces a path with at least `2*m` edges.
The strict bound on external neighbors is the only expansion assumption. -/
theorem exists_long_path_of_expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 0 < m) (hmn : m ≤ Fintype.card V)
    (hex : ∀ S : Finset V, S.card = m → 2 * m < (externalNeighbors G S).card) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsPath ∧ 2 * m ≤ p.length := by
  obtain ⟨z, hz, hsm⟩ := DFS.reach_finished G m hmn DFS.initial
    (DFS.initial_valid G) (by simp [DFS.initial])
  have hsub : externalNeighbors G z.S ⊆ z.U.toFinset := by
    intro v hv
    obtain ⟨hvout, u, hu, hadj⟩ := Finset.mem_filter.mp hv
    have hvS : v ∉ z.S := (Finset.mem_sdiff.mp hvout).2
    rcases hz.cover v with hv | hv | hv
    · exact (hvS hv).elim
    · exact (hz.cut u hu v hv hadj).elim
    · exact List.mem_toFinset.mpr hv
  have hcard : (externalNeighbors G z.S).card ≤ z.U.length := by
    calc
      _ ≤ z.U.toFinset.card := Finset.card_le_card hsub
      _ = z.U.length := List.toFinset_card_of_nodup hz.nodup
  have hlarge : 2 * m < z.U.length := lt_of_lt_of_le (hex z.S hsm) hcard
  cases hU : z.U with
  | nil => simp [hU] at hlarge
  | cons u tail =>
    obtain ⟨v, p, hp, hpath⟩ := DFS.chain_walk
      (by simpa [hU] using hz.nodup) (by simpa [hU] using hz.chain)
    have hlen : p.length + 1 = (u :: tail).length := by
      simpa [hp] using p.length_support.symm
    refine ⟨u, v, p, hpath, ?_⟩
    rw [hU] at hlarge
    omega

#print axioms exists_long_path_of_expansion

end JSP619
