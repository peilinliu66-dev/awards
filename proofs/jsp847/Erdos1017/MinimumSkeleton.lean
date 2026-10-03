/-
Copyright (c) 2026. Released under the Apache License 2.0.
Replacing selected pieces and the triangle-free minimum-weight skeleton.
UNCOMPILED source, with all new proof bodies written explicitly.
-/
import Erdos1017.PartitionRestriction
import Erdos1017.Packing

namespace Erdos1017

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace CliquePartition

variable {G : SimpleGraph V}

/-- Replace a subfamily by an exact packing of precisely the same edges. -/
theorem replaceByPacking (P : CliquePartition G) (D : Finset (Finset V))
    (hD : D ⊆ P.blocks) (K : CliquePacking G)
    (hsame : ∀ u v, u ≠ v →
      ((∃ C ∈ D, u ∈ C ∧ v ∈ C) ↔ K.OwnsEdge u v)) :
    ∃ Q : CliquePartition G,
      Q.weight + (∑ C ∈ D, C.card) = P.weight + K.weight := by
  classical
  let R : CliquePartition K.remainder := {
    blocks := P.blocks \ D
    nontrivial := fun C hC => P.nontrivial C (Finset.mem_sdiff.mp hC).1
    clique := by
      intro C hC u hu v hv huv
      obtain ⟨hCP, hCD⟩ := Finset.mem_sdiff.mp hC
      refine ⟨P.clique C hCP u hu v hv huv, ?_⟩
      intro hK
      obtain ⟨E, hE, huE, hvE⟩ := (hsame u v huv).mpr hK
      have hEq := P.eq_of_shared_edge hCP (hD hE) hu hv huE hvE huv
      exact hCD (hEq.symm ▸ hE)
    owns := by
      intro u v huv
      obtain ⟨C, hC, huniq⟩ := P.owns u v huv.1
      have hnot : C ∉ D := by
        intro hCD
        exact huv.2 ((hsame u v huv.1.ne).mp ⟨C, hCD, hC.2⟩)
      refine ⟨C, ⟨Finset.mem_sdiff.mpr ⟨hC.1, hnot⟩, hC.2⟩, ?_⟩
      intro E hE
      exact huniq E ⟨(Finset.mem_sdiff.mp hE.1).1, hE.2⟩ }
  refine ⟨K.complete R, ?_⟩
  have hsum : (∑ C ∈ P.blocks \ D, C.card) + (∑ C ∈ D, C.card) =
      P.weight := Finset.sum_sdiff hD
  rw [CliquePacking.complete_weight]
  change K.weight + (∑ C ∈ P.blocks \ D, C.card) + (∑ C ∈ D, C.card) = _
  omega

theorem minimum_weight_subfamily_le (P : CliquePartition G)
    (hmin : ∀ Q : CliquePartition G, P.weight ≤ Q.weight)
    (D : Finset (Finset V)) (hD : D ⊆ P.blocks) (K : CliquePacking G)
    (hsame : ∀ u v, u ≠ v →
      ((∃ C ∈ D, u ∈ C ∧ v ∈ C) ↔ K.OwnsEdge u v)) :
    (∑ C ∈ D, C.card) ≤ K.weight := by
  obtain ⟨Q, hQ⟩ := P.replaceByPacking D hD K hsame
  have h := hmin Q
  omega

private theorem overlapping_pairs_ne {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) :
    ({u, v} : Finset V) ≠ {v, w} := by
  intro h
  have : u ∈ ({v, w} : Finset V) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  exact this.elim huv huw

/-- Three single-edge pieces forming a triangle would admit a weight-saving
replacement by their three-vertex clique. -/
theorem skeleton_triangleFree (P : CliquePartition G)
    (hmin : ∀ Q : CliquePartition G, P.weight ≤ Q.weight) :
    TriangleFree P.skeleton := by
  classical
  intro u v w huv hvw hwu
  have huv' : u ≠ v := huv.1
  have hvw' : v ≠ w := hvw.1
  have hwu' : w ≠ u := hwu.1
  let D : Finset (Finset V) := {{u, v}, {v, w}, {w, u}}
  let T : Finset V := {u, v, w}
  have hD : D ⊆ P.blocks := by
    intro C hC
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl | rfl
    · exact huv.2
    · exact hvw.2
    · exact hwu.2
  have hTcard : T.card = 3 := by
    simp [T, huv', hvw', hwu', hwu'.symm]
  have hTclique : IsClique G T := by
    have hGuv := P.skeleton_le huv
    have hGvw := P.skeleton_le hvw
    have hGwu := P.skeleton_le hwu
    intro a ha b hb hab
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl
    all_goals first | exact False.elim (hab rfl) | assumption |
      exact hGuv.symm | exact hGvw.symm | exact hGwu.symm
  let K := CliquePacking.singleton G T (by omega) hTclique
  have hsame : ∀ a b, a ≠ b →
      ((∃ C ∈ D, a ∈ C ∧ b ∈ C) ↔ K.OwnsEdge a b) := by
    intro a b hab
    simp only [D, T, K, CliquePacking.OwnsEdge, CliquePacking.singleton,
      Finset.mem_insert, Finset.mem_singleton]
    aesop
  have h12 : ({u, v} : Finset V) ≠ {v, w} :=
    overlapping_pairs_ne huv' hwu'.symm
  have h23 : ({v, w} : Finset V) ≠ {w, u} :=
    overlapping_pairs_ne hvw' huv'.symm
  have h13 : ({u, v} : Finset V) ≠ {w, u} := by
    simpa only [Finset.pair_comm v u, Finset.pair_comm u w] using
      (overlapping_pairs_ne (u := v) (v := u) (w := w) huv'.symm hvw')
  have hDweight : (∑ C ∈ D, C.card) = 6 := by
    simp [D, h12, h13, h23, huv', hvw', hwu']
  have hKweight : K.weight = 3 := by
    simp [K, CliquePacking.weight, CliquePacking.singleton, hTcard]
  have h := P.minimum_weight_subfamily_le hmin D hD K hsame
  rw [hDweight, hKweight] at h
  omega

theorem skeleton_edges_add_large (P : CliquePartition G) :
    edgeCount P.skeleton + P.largeBlocks.card = P.count := by
  classical
  have hgraph : onVertices P.skeleton Finset.univ = P.skeleton := by
    ext u v
    simp [onVertices]
  have hpairs := P.pairBlocksOn_card Finset.univ
  rw [hgraph] at hpairs
  rw [← hpairs]
  calc
    (P.pairBlocksOn Finset.univ).card + P.largeBlocks.card =
        ∑ C ∈ P.blocks,
          ((if C.card = 2 then 1 else 0) + (if 3 ≤ C.card then 1 else 0)) := by
      simp only [pairBlocksOn, largeBlocks, Finset.subset_univ, and_true,
        Finset.card_filter, Finset.sum_add_distrib]
    _ = ∑ _C ∈ P.blocks, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro C hC
      have hn := P.nontrivial C hC
      by_cases h : C.card = 2
      · simp [h]
      · have hthree : 3 ≤ C.card := by omega
        simp [h, hthree]
    _ = P.count := by simp [count]

end CliquePartition

end Erdos1017
