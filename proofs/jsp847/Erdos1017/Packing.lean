import Erdos1017.PartitionExistence

/-! Finite exact clique packings, edge deletion, and partition assembly.
Original source implementation. UNCOMPILED. -/

open scoped BigOperators

namespace Erdos1017

variable {V : Type*} [DecidableEq V]

structure CliquePacking (G : SimpleGraph V) where
  blocks : Finset (Finset V)
  nontrivial : ∀ C ∈ blocks, 2 ≤ C.card
  clique : ∀ C ∈ blocks, IsClique G C
  unique : ∀ C ∈ blocks, ∀ D ∈ blocks,
    ∀ u ∈ C, ∀ v ∈ C, u ∈ D → v ∈ D → u ≠ v → C = D

namespace CliquePacking

variable {G : SimpleGraph V}

def count (P : CliquePacking G) : ℕ := P.blocks.card
def weight (P : CliquePacking G) : ℕ := ∑ C ∈ P.blocks, C.card

def OwnsEdge (P : CliquePacking G) (u v : V) : Prop :=
  ∃ C ∈ P.blocks, u ∈ C ∧ v ∈ C

theorem ownsEdge_symm (P : CliquePacking G) {u v : V}
    (h : P.OwnsEdge u v) : P.OwnsEdge v u := by
  obtain ⟨C, hC, hu, hv⟩ := h
  exact ⟨C, hC, hv, hu⟩

def remainder (P : CliquePacking G) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ¬ P.OwnsEdge u v
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, fun huv => h.2 (P.ownsEdge_symm huv)⟩
    ⟩
  loopless := ⟨by
    intro u h
    exact G.loopless.irrefl u h.1
    ⟩

@[simp] theorem remainder_adj (P : CliquePacking G) (u v : V) :
    P.remainder.Adj u v ↔ G.Adj u v ∧ ¬ P.OwnsEdge u v := Iff.rfl

theorem blocks_disjoint_next (P : CliquePacking G)
    (Q : CliquePacking P.remainder) : Disjoint P.blocks Q.blocks := by
  classical
  apply Finset.disjoint_left.mpr
  intro C hCP hCQ
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < C.card by
    have := P.nontrivial C hCP
    omega)
  exact (Q.clique C hCQ u hu v hv huv).2 ⟨C, hCP, hu, hv⟩

/-- Sequentially chosen edge-disjoint packings can be concatenated. -/
def append (P : CliquePacking G) (Q : CliquePacking P.remainder) : CliquePacking G where
  blocks := P.blocks ∪ Q.blocks
  nontrivial := by
    intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact P.nontrivial C hC
    · exact Q.nontrivial C hC
  clique := by
    intro C hC u hu v hv huv
    rcases Finset.mem_union.mp hC with hC | hC
    · exact P.clique C hC u hu v hv huv
    · exact (Q.clique C hC u hu v hv huv).1
  unique := by
    intro C hC D hD u huC v hvC huD hvD huv
    rcases Finset.mem_union.mp hC with hCP | hCQ <;>
      rcases Finset.mem_union.mp hD with hDP | hDQ
    · exact P.unique C hCP D hDP u huC v hvC huD hvD huv
    · exact False.elim ((Q.clique D hDQ u huD v hvD huv).2 ⟨C, hCP, huC, hvC⟩)
    · exact False.elim ((Q.clique C hCQ u huC v hvC huv).2 ⟨D, hDP, huD, hvD⟩)
    · exact Q.unique C hCQ D hDQ u huC v hvC huD hvD huv

@[simp] theorem append_weight (P : CliquePacking G) (Q : CliquePacking P.remainder) :
    (P.append Q).weight = P.weight + Q.weight := by
  classical
  exact Finset.sum_union (P.blocks_disjoint_next Q)

@[simp] theorem append_count (P : CliquePacking G) (Q : CliquePacking P.remainder) :
    (P.append Q).count = P.count + Q.count := by
  classical
  exact Finset.card_union_of_disjoint (P.blocks_disjoint_next Q)

theorem append_remainder (P : CliquePacking G) (Q : CliquePacking P.remainder) :
    (P.append Q).remainder = Q.remainder := by
  ext u v
  simp only [remainder, OwnsEdge, append, Finset.mem_union]
  constructor
  · rintro ⟨hG, h⟩
    refine ⟨⟨hG, ?_⟩, ?_⟩
    · rintro ⟨C, hC, hu, hv⟩
      exact h ⟨C, Or.inl hC, hu, hv⟩
    · rintro ⟨C, hC, hu, hv⟩
      exact h ⟨C, Or.inr hC, hu, hv⟩
  · rintro ⟨⟨hG, hp⟩, hq⟩
    refine ⟨hG, ?_⟩
    rintro ⟨C, hC | hC, hu, hv⟩
    · exact hp ⟨C, hC, hu, hv⟩
    · exact hq ⟨C, hC, hu, hv⟩

theorem blocks_disjoint_remainder (P : CliquePacking G)
    (Q : CliquePartition P.remainder) : Disjoint P.blocks Q.blocks := by
  classical
  apply Finset.disjoint_left.mpr
  intro C hCP hCQ
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < C.card by
    have := P.nontrivial C hCP
    omega)
  exact (Q.clique C hCQ u hu v hv huv).2 ⟨C, hCP, hu, hv⟩

/-- Fill all still-unowned edges with an exact partition of the remainder. -/
def complete (P : CliquePacking G) (Q : CliquePartition P.remainder) :
    CliquePartition G where
  blocks := P.blocks ∪ Q.blocks
  nontrivial := by
    intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact P.nontrivial C hC
    · exact Q.nontrivial C hC
  clique := by
    intro C hC u hu v hv huv
    rcases Finset.mem_union.mp hC with hC | hC
    · exact P.clique C hC u hu v hv huv
    · exact (Q.clique C hC u hu v hv huv).1
  owns := by
    classical
    intro u v huv
    by_cases hp : P.OwnsEdge u v
    · obtain ⟨C, hC, huC, hvC⟩ := hp
      refine ⟨C, ⟨Finset.mem_union_left _ hC, huC, hvC⟩, ?_⟩
      intro D hD
      rcases Finset.mem_union.mp hD.1 with hDP | hDQ
      · exact P.unique D hDP C hC u hD.2.1 v hD.2.2 huC hvC huv.ne
      · exact False.elim ((Q.clique D hDQ u hD.2.1 v hD.2.2 huv.ne).2
          ⟨C, hC, huC, hvC⟩)
    · obtain ⟨C, hC, huniq⟩ := Q.owns u v ⟨huv, hp⟩
      refine ⟨C, ⟨Finset.mem_union_right _ hC.1, hC.2⟩, ?_⟩
      intro D hD
      rcases Finset.mem_union.mp hD.1 with hDP | hDQ
      · exact False.elim (hp ⟨D, hDP, hD.2⟩)
      · exact huniq D ⟨hDQ, hD.2⟩

@[simp] theorem complete_weight (P : CliquePacking G) (Q : CliquePartition P.remainder) :
    (P.complete Q).weight = P.weight + Q.weight := by
  classical
  exact Finset.sum_union (P.blocks_disjoint_remainder Q)

@[simp] theorem complete_count (P : CliquePacking G) (Q : CliquePartition P.remainder) :
    (P.complete Q).count = P.count + Q.count := by
  classical
  exact Finset.card_union_of_disjoint (P.blocks_disjoint_remainder Q)

/-- One nontrivial clique is always an admissible packing. -/
def singleton (G : SimpleGraph V) (C : Finset V) (hcard : 2 ≤ C.card)
    (hC : IsClique G C) : CliquePacking G where
  blocks := {C}
  nontrivial := by intro D hD; obtain rfl := Finset.mem_singleton.mp hD; exact hcard
  clique := by intro D hD; obtain rfl := Finset.mem_singleton.mp hD; exact hC
  unique := by
    intro D hD E hE u hu v hv huE hvE huv
    exact (Finset.mem_singleton.mp hD).trans (Finset.mem_singleton.mp hE).symm

/-- An empty packing leaves the graph unchanged. -/
def empty (G : SimpleGraph V) : CliquePacking G where
  blocks := ∅
  nontrivial := by simp
  clique := by simp
  unique := by simp

end CliquePacking

namespace CliquePartition

variable {G : SimpleGraph V}

def toPacking (P : CliquePartition G) : CliquePacking G where
  blocks := P.blocks
  nontrivial := P.nontrivial
  clique := P.clique
  unique := by
    intro C hC D hD u huC v hvC huD hvD huv
    exact P.eq_of_shared_edge hC hD huC hvC huD hvD huv

end CliquePartition

end Erdos1017
