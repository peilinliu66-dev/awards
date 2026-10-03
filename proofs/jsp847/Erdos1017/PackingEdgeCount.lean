import Erdos1017.Packing
import Erdos1017.GraphCut
import Mathlib.Data.Sym.Card

/-! Exact edge conservation for finite clique packings.
Original source implementation. UNCOMPILED. -/

open scoped BigOperators

namespace Erdos1017

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

local instance (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _

def cliqueEdges (C : Finset V) : Finset (Sym2 V) :=
  C.offDiag.image Sym2.mk.uncurry

@[simp] theorem mem_cliqueEdges (C : Finset V) (u v : V) :
    s(u, v) ∈ cliqueEdges C ↔ u ∈ C ∧ v ∈ C ∧ u ≠ v := by
  classical
  simp only [cliqueEdges, Finset.mem_image, Finset.mem_offDiag, Prod.exists,
    Function.uncurry, Sym2.eq_iff]
  aesop

@[simp] theorem card_cliqueEdges (C : Finset V) :
    (cliqueEdges C).card = C.card.choose 2 := Sym2.card_image_offDiag C

namespace CliquePacking

variable {G : SimpleGraph V}

def ownedEdges (P : CliquePacking G) : Finset (Sym2 V) :=
  P.blocks.biUnion cliqueEdges

@[simp] theorem mem_ownedEdges (P : CliquePacking G) (u v : V) :
    s(u, v) ∈ P.ownedEdges ↔ u ≠ v ∧ P.OwnsEdge u v := by
  classical
  simp only [ownedEdges, Finset.mem_biUnion, mem_cliqueEdges, OwnsEdge]
  aesop

theorem ownedEdges_subset (P : CliquePacking G) : P.ownedEdges ⊆ G.edgeFinset := by
  classical
  intro e
  refine Sym2.ind (fun u v h => ?_) e
  obtain ⟨huv, C, hC, hu, hv⟩ := (P.mem_ownedEdges u v).mp h
  simpa using P.clique C hC u hu v hv huv

theorem cliqueEdges_pairwise_disjoint (P : CliquePacking G) :
    (↑P.blocks : Set (Finset V)).PairwiseDisjoint cliqueEdges := by
  classical
  intro C hC D hD hCD
  apply Finset.disjoint_left.mpr
  intro e heC heD
  revert heC heD
  refine Sym2.ind (fun u v hu hv => ?_) e
  obtain ⟨huC, hvC, huv⟩ := (mem_cliqueEdges C u v).mp hu
  obtain ⟨huD, hvD, _⟩ := (mem_cliqueEdges D u v).mp hv
  exact hCD (P.unique C hC D hD u huC v hvC huD hvD huv)

theorem ownedEdges_card (P : CliquePacking G) :
    P.ownedEdges.card = ∑ C ∈ P.blocks, C.card.choose 2 := by
  classical
  rw [ownedEdges, Finset.card_biUnion P.cliqueEdges_pairwise_disjoint]
  simp only [card_cliqueEdges]

theorem remainder_edgeFinset (P : CliquePacking G) :
    P.remainder.edgeFinset = G.edgeFinset \ P.ownedEdges := by
  classical
  ext e
  refine Sym2.ind (fun u v => ?_) e
  simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet, remainder_adj, mem_ownedEdges]
  constructor
  · rintro ⟨hG, hn⟩
    exact ⟨hG, fun h => hn h.2⟩
  · rintro ⟨hG, hn⟩
    exact ⟨hG, fun h => hn ⟨hG.ne, h⟩⟩

theorem edgeCount_remainder_add (P : CliquePacking G) :
    edgeCount P.remainder + (∑ C ∈ P.blocks, C.card.choose 2) = edgeCount G := by
  classical
  rw [edgeCount, P.remainder_edgeFinset, ← P.ownedEdges_card]
  exact Finset.card_sdiff_add_card_eq_card P.ownedEdges_subset

theorem triangle_edgeCount_remainder (P : CliquePacking G)
    (hthree : ∀ C ∈ P.blocks, C.card = 3) :
    edgeCount P.remainder + 3 * P.count = edgeCount G := by
  have hsum : (∑ C ∈ P.blocks, C.card.choose 2) = 3 * P.count := by
    calc
      (∑ C ∈ P.blocks, C.card.choose 2) = ∑ _C ∈ P.blocks, (3 : ℕ) := by
        apply Finset.sum_congr rfl
        intro C hC
        rw [hthree C hC]
        norm_num
      _ = 3 * P.count := by simp [count, mul_comm]
  simpa only [hsum] using P.edgeCount_remainder_add

end CliquePacking

namespace CliquePartition

variable {G : SimpleGraph V}

theorem edgeCount_eq_sum_choose (P : CliquePartition G) :
    edgeCount G = ∑ C ∈ P.blocks, C.card.choose 2 := by
  have hbot : P.toPacking.remainder = ⊥ := by
    ext u v
    constructor
    · rintro ⟨hG, hn⟩
      obtain ⟨C, hC, _⟩ := P.owns u v hG
      exact hn ⟨C, hC⟩
    · simp
  have h := P.toPacking.edgeCount_remainder_add
  have hzero : edgeCount (⊥ : SimpleGraph V) = 0 := by
    classical
    unfold edgeCount
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have he' := (@SimpleGraph.mem_edgeFinset V (⊥ : SimpleGraph V) e
      (@SimpleGraph.fintypeEdgeSet V (⊥ : SimpleGraph V) inferInstance
        (fun _ _ => Classical.propDecidable _))).mp he
    simpa using he'
  rw [hbot, hzero] at h
  simpa only [zero_add, toPacking] using h.symm

theorem edgePartition_count (G : SimpleGraph V) :
    (edgePartition G).count = edgeCount G := by
  classical
  have h := (edgePartition G).edgeCount_eq_sum_choose
  have htwo : ∀ C ∈ (edgePartition G).blocks, C.card = 2 := by
    intro C hC
    exact (Finset.mem_filter.mp hC).2.1
  rw [Finset.sum_congr rfl (fun C hC =>
    congrArg (fun n => n.choose 2) (htwo C hC))] at h
  simpa [count] using h.symm

end CliquePartition

end

end Erdos1017
