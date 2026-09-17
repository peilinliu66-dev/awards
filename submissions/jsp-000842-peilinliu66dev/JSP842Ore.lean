import Mathlib

set_option maxHeartbeats 1200000

namespace JSP842
open SimpleGraph Finset

namespace Ore
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}

theorem crossing_of_degree_sum (p : G.Walk u v) (hp : p.IsHamiltonian)
    (hdeg : Fintype.card V ≤ G.degree u + G.degree v) :
    ∃ i < p.length, G.Adj u (p.getVert (i + 1)) ∧ G.Adj v (p.getVert i) := by
  classical
  let A := (range p.length).filter (fun i => G.Adj u (p.getVert (i + 1)))
  let B := (range p.length).filter (fun i => G.Adj v (p.getVert i))
  have hA : A.card = G.degree u := by
    rw [← G.card_neighborFinset_eq_degree u]
    apply card_bij (fun i _ => p.getVert (i + 1))
    · intro i hi
      exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hi).2
    · intro i hi j hj hij
      have hi' := mem_range.mp (mem_filter.mp hi).1
      have hj' := mem_range.mp (mem_filter.mp hj).1
      have := hp.isPath.getVert_injOn (by simp; omega) (by simp; omega) hij
      omega
    · intro w hw
      have hadj := (G.mem_neighborFinset _ _).mp hw
      obtain ⟨j, hj, hjle⟩ := p.mem_support_iff_exists_getVert.mp (hp.mem_support w)
      have hjpos : 0 < j := by
        by_contra hn
        have : j = 0 := by omega
        subst j
        simp only [Walk.getVert_zero] at hj
        exact hadj.ne hj
      refine ⟨j - 1, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, ?_⟩
      · simpa [Nat.sub_add_cancel (by omega : 1 ≤ j), hj] using hadj
      · simpa [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hj
  have hB : B.card = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree v]
    apply card_bij (fun i _ => p.getVert i)
    · intro i hi
      exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hi).2
    · intro i hi j hj hij
      have hi' := mem_range.mp (mem_filter.mp hi).1
      have hj' := mem_range.mp (mem_filter.mp hj).1
      exact hp.isPath.getVert_injOn (by simp; omega) (by simp; omega) hij
    · intro w hw
      have hadj := (G.mem_neighborFinset _ _).mp hw
      obtain ⟨j, hj, hjle⟩ := p.mem_support_iff_exists_getVert.mp (hp.mem_support w)
      have hjlt : j < p.length := by
        by_contra hn
        have : j = p.length := by omega
        subst j
        simp only [Walk.getVert_length] at hj
        exact hadj.ne hj
      exact ⟨j, mem_filter.mpr ⟨mem_range.mpr hjlt, hj ▸ hadj⟩, hj⟩
  have hU : (A ∪ B).card ≤ p.length := by
    calc
      (A ∪ B).card ≤ (range p.length).card := card_le_card (union_subset
        (filter_subset _ _) (filter_subset _ _))
      _ = p.length := card_range _
  have hlen := hp.length_support
  rw [Walk.length_support] at hlen
  have hI : (A ∩ B).Nonempty := by
    rw [← card_pos]
    have := card_union_add_card_inter A B
    omega
  obtain ⟨i, hi⟩ := hI
  have ha := mem_filter.mp (mem_inter.mp hi).1
  have hb := mem_filter.mp (mem_inter.mp hi).2
  exact ⟨i, mem_range.mp ha.1, ha.2, hb.2⟩

theorem hamiltonian_of_hamiltonian_path (p : G.Walk u v) (hp : p.IsHamiltonian)
    (hn : 3 ≤ Fintype.card V)
    (hdeg : Fintype.card V ≤ G.degree u + G.degree v) : G.IsHamiltonian := by
  classical
  obtain ⟨i, hi, hui, hvi⟩ := crossing_of_degree_sum p hp hdeg
  let a := p.take i
  let b := p.drop (i + 1)
  let q := b.reverse.append (Walk.cons hui.symm a)
  have hsplit : a.support ++ b.support = p.support := by
    simp only [a, b, Walk.support_take, Walk.drop_support_eq_support_drop_min,
      inf_eq_left.mpr (by omega : i + 1 ≤ p.length)]
    exact List.take_append_drop (i + 1) p.support
  have hq : q.IsHamiltonian := by
    intro w
    have heq : q.support.count w = p.support.count w := by
      dsimp [q]
      rw [Walk.support_append, Walk.support_reverse, Walk.support_cons, List.tail_cons]
      rw [List.count_append, List.count_reverse, add_comm, ← List.count_append, hsplit]
    exact heq.trans (hp w)
  let c := Walk.cons hvi.symm q
  have hclen : c.length = Fintype.card V := by
    have := hq.length_support
    rw [Walk.length_support] at this
    simpa only [c, Walk.length_cons] using this
  have hc : c.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simpa [c] using hq.isPath
    · omega
  intro _
  exact ⟨p.getVert i, c, Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hc, hclen⟩⟩

theorem edge_mem_of_ne_added {a b : V}
    (p : (G ⊔ SimpleGraph.edge u v).Walk a b)
    (hnot : s(u, v) ∉ p.edges) : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
  intro e he
  have := p.edges_subset_edgeSet he
  rw [SimpleGraph.edgeSet_sup] at this
  rcases this with hg | hadd
  · exact hg
  · have : e = s(u, v) := by
      exact Set.mem_singleton_iff.mp (SimpleGraph.edgeSet_edge_subset hadd)
    exact (hnot (this ▸ he)).elim

theorem path_of_cycle_snd (c : (G ⊔ SimpleGraph.edge u v).Walk u u)
    (hc : c.IsHamiltonianCycle) (hsnd : c.snd = v) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  cases c with
  | nil => exact (hc.not_nil Walk.nil_nil).elim
  | @cons _ a _ h p =>
    have hav : a = v := by simpa using hsnd
    subst a
    have hnot := (Walk.cons_isCycle_iff p h).mp hc.isCycle |>.2
    have htransfer := edge_mem_of_ne_added p hnot
    let q := p.transfer G htransfer
    refine ⟨q.reverse, ?_⟩
    intro w
    have hw := hc.isHamiltonian_tail w
    simpa [q, Walk.IsHamiltonian] using hw

theorem hamiltonian_or_path_of_add_edge
    (hn : 3 ≤ Fintype.card V) (huv : u ≠ v)
    (hham : (G ⊔ SimpleGraph.edge u v).IsHamiltonian) :
    G.IsHamiltonian ∨ ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  obtain ⟨x, c, hc⟩ := hham (by omega)
  by_cases hmem : s(u, v) ∈ c.edges
  · right
    generalize hddef : c.rotate u (hc.mem_support u) = d
    have hd : d.IsHamiltonianCycle := hddef ▸ hc.rotate _
    have hmemd : s(u, v) ∈ d.edges :=
      hddef ▸ (c.rotate_edges u (hc.mem_support u)).mem_iff.mpr hmem
    by_cases hsnd : d.snd = v
    · exact path_of_cycle_snd d hd hsnd
    · have hrev : d.reverse.IsHamiltonianCycle :=
        Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
          ⟨hd.isCycle.reverse, by simpa using hd.length_eq⟩
      apply path_of_cycle_snd d.reverse hrev
      rw [Walk.snd_reverse]
      cases d with
      | nil => exact (hd.not_nil Walk.nil_nil).elim
      | @cons _ a _ h p =>
        have hav : a ≠ v := by simpa using hsnd
        have htail : s(u, v) ∈ p.edges := by
          simp only [Walk.edges_cons, List.mem_cons] at hmemd
          rcases hmemd with he | he
          · have : v = a := by simpa [Ne.symm huv] using he
            exact (hav this.symm).elim
          · exact he
        have hp : p.IsPath := (Walk.cons_isCycle_iff p h).mp hd.isCycle |>.1
        have heq := hp.eq_penultimate_of_mem_edges htail
        rw [Walk.penultimate_cons_of_not_nil h p (Walk.not_nil_of_isCycle_cons hd.isCycle)]
        exact heq.symm
  · left
    have htransfer := edge_mem_of_ne_added c hmem
    intro _
    refine ⟨x, c.transfer G htransfer, ?_⟩
    apply Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
    exact ⟨hc.isCycle.transfer htransfer, by simpa using hc.length_eq⟩

end Ore

theorem ore_edge_closure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
    (hn : 3 ≤ Fintype.card V) (huv : u ≠ v) (_hnadj : ¬ G.Adj u v)
    (hdeg : Fintype.card V ≤ G.degree u + G.degree v)
    (hham : (G ⊔ SimpleGraph.edge u v).IsHamiltonian) : G.IsHamiltonian := by
  rcases Ore.hamiltonian_or_path_of_add_edge hn huv hham with h | ⟨p, hp⟩
  · exact h
  · exact Ore.hamiltonian_of_hamiltonian_path p hp hn hdeg

#print axioms ore_edge_closure
end JSP842
