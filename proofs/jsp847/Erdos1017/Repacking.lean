import Erdos1017.TriangleCandidates

/-! A genuine edge partition obtained from selected matching triangles.
Every discarded or rejected pair is explicitly budgeted. UNCOMPILED. -/

namespace Erdos1017

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

local instance (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _

namespace CliquePartition

theorem block_subset_onVertices {G : SimpleGraph V} {S : Finset V}
    (P : CliquePartition (onVertices G S)) {C : Finset V} (hC : C ∈ P.blocks) :
    C ⊆ S := by
  intro u hu
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < C.card by
    have := P.nontrivial C hC
    omega)
  by_cases hua : u = a
  · subst u
    exact (P.clique C hC a ha b hb hab).2.1
  · exact (P.clique C hC u hu a ha hua).2.1

def liftOnVertices {G : SimpleGraph V} {S : Finset V}
    (P : CliquePartition (onVertices G S)) : CliquePacking G where
  blocks := P.blocks
  nontrivial := P.nontrivial
  clique := by
    intro C hC u hu v hv huv
    exact (P.clique C hC u hu v hv huv).1
  unique := P.toPacking.unique

theorem liftOnVertices_no_owned {G : SimpleGraph V} {S : Finset V}
    (P : CliquePartition (onVertices G S)) {u v : V} (hu : u ∉ S) :
    ¬P.liftOnVertices.OwnsEdge u v := by
  rintro ⟨C, hC, huC, hvC⟩
  exact hu (P.block_subset_onVertices hC huC)

theorem liftOnVertices_remainder_adj {G : SimpleGraph V} {S : Finset V}
    (P : CliquePartition (onVertices G S)) {u v : V} (hu : u ∉ S) :
    P.liftOnVertices.remainder.Adj u v ↔ G.Adj u v := by
  exact and_iff_left (P.liftOnVertices_no_owned hu)

theorem liftOnVertices_edge_count {G : SimpleGraph V} {S : Finset V}
    (P : CliquePartition (onVertices G S)) :
    edgeCount P.liftOnVertices.remainder + edgeCount (onVertices G S) = edgeCount G := by
  have h := P.liftOnVertices.edgeCount_remainder_add
  have hp := P.edgeCount_eq_sum_choose
  simpa only [hp, liftOnVertices] using h

end CliquePartition

/-- Exact finite repacking inequality. The returned `Q` partitions each edge
once; `ell` counts only the internal edges whose cyclic colors were discarded. -/
theorem exists_repacked_partition (G : SimpleGraph V) (X : Finset V)
    (hx : 0 < X.card) (hy : 0 < Xᶜ.card)
    (QY : CliquePartition (onVertices G Xᶜ)) :
    ∃ ell : ℕ, ∃ Q : CliquePartition G,
      X.card * ell ≤ (X.card - min X.card Xᶜ.card) * edgeCount (onVertices G X) ∧
      Q.count + edgeCount (onVertices G X) ≤
        incidenceCount G X Xᶜ + 2 * ell + 2 * missingCount G X Xᶜ + QY.count := by
  classical
  let L := QY.liftOnVertices
  let H := L.remainder
  let E := (edgePartition (onVertices G X)).blocks
  have hXY : Disjoint X Xᶜ := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    exact (Finset.mem_compl.mp hv) hu
  have hE : ∀ e ∈ E, e.card = 2 ∧ e ⊆ X ∧ IsClique H e := by
    intro e he
    have hcard : e.card = 2 := (Finset.mem_filter.mp he).2.1
    have hsub := (edgePartition (onVertices G X)).block_subset_onVertices he
    refine ⟨hcard, hsub, ?_⟩
    intro u hu v hv huv
    have hG := ((edgePartition (onVertices G X)).clique e he u hu v hv huv).1
    exact (QY.liftOnVertices_remainder_adj (by simpa using hsub hu)).mpr hG
  have hEcard : E.card = edgeCount (onVertices G X) :=
    CliquePartition.edgePartition_count (onVertices G X)
  obtain ⟨S⟩ := exists_coloredPairSelection X Xᶜ hx hy E
    (fun e he => ⟨(hE e he).1, (hE e he).2.1⟩)
  let T := S.trianglePacking hXY hE
  let QH := T.complete (edgePartition T.remainder)
  let Q := L.complete QH
  let ell := (E \ S.retained).card
  have hmissing : missingCount H X Xᶜ = missingCount G X Xᶜ := by
    unfold missingCount
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    change (if QY.liftOnVertices.remainder.Adj u v then 0 else 1) =
      if G.Adj u v then 0 else 1
    simp only [QY.liftOnVertices_remainder_adj (by simpa using hu)]
  have hHedges : edgeCount H = edgeCount (onVertices G X) + incidenceCount G X Xᶜ := by
    have h1 := QY.liftOnVertices_edge_count
    have h2 := edgeCount_cut G X
    change edgeCount H + edgeCount (onVertices G Xᶜ) = edgeCount G at h1
    omega
  have hTcount : T.count = (S.goodPairs H).card :=
    S.trianglePacking_count hXY hE
  have hTedges : edgeCount T.remainder + 3 * T.count = edgeCount H :=
    T.triangle_edgeCount_remainder (S.trianglePacking_card hXY hE)
  have hgood := S.totalPairs_le_good_add_discard_add_missing (G := H)
    (fun e he => (hE e he).2.1)
  rw [← hTcount, hmissing, hEcard] at hgood
  have hQ : Q.count = QY.count + T.count + edgeCount T.remainder := by
    simp only [Q, QH, CliquePacking.complete_count, CliquePartition.edgePartition_count]
    change QY.count + (T.count + edgeCount T.remainder) =
      QY.count + T.count + edgeCount T.remainder
    omega
  refine ⟨ell, Q, ?_, ?_⟩
  · simpa only [ell, hEcard] using S.discard_budget
  · dsimp only [ell] at *
    omega

end

end Erdos1017
