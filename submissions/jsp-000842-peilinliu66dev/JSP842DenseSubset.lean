import Mathlib

/-! A maximum-edge induced subset and its minimum-degree edge bound.
All edge counts below are bridged to the actual SimpleGraph.edgeFinset.
-/

open Finset

namespace JSP842

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def edgePart (s : Finset V) : Finset (Sym2 V) := G.edgeFinset ∩ s.sym2

def neighborPart (s : Finset V) (v : V) : Finset V := s.filter (G.Adj v)

lemma edgePart_card (s : Finset V) :
    (edgePart G s).card = (G.induce (↑s : Set V)).edgeFinset.card := by
  rw [← G.card_filter_edgeFinset_toFinset_subset s,
    G.filter_edgeFinset_toFinset_subset]
  rfl

lemma neighborPart_card (s : Finset V) (v : (↑s : Set V)) :
    (neighborPart G s v).card = (G.induce (↑s : Set V)).degree v := by
  have h := congrArg Finset.card (G.map_neighborFinset_induce (s := (↑s : Set V)) v)
  rw [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree,
    Finset.toFinset_coe] at h
  have he : G.neighborFinset v ∩ s = neighborPart G s v := by
    ext w
    simp [neighborPart, and_comm]
  rw [he] at h
  convert! h.symm

lemma edgePart_insert (s : Finset V) (v : V) :
    edgePart G (insert v s) = edgePart G s ∪
      (neighborPart G s v).image (fun w => s(v, w)) := by
  have hi : G.edgeFinset ∩ ((insert v s).image (fun w => s(v, w))) =
      (neighborPart G s v).image (fun w => s(v, w)) := by
    ext e
    constructor
    · intro he
      obtain ⟨heG, heI⟩ := Finset.mem_inter.mp he
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp heI
      have hvw : G.Adj v w := by simpa using heG
      have hws : w ∈ s := by
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact (G.irrefl hvw).elim
        · exact hw
      exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hws, hvw⟩, rfl⟩
    · intro he
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hws, hvw⟩ := Finset.mem_filter.mp hw
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · simpa using hvw
      · exact Finset.mem_image.mpr ⟨w, Finset.mem_insert_of_mem hws, rfl⟩
  unfold edgePart
  rw [Finset.sym2_insert, Finset.inter_union_distrib_left, hi, Finset.union_comm]

lemma edgePart_insert_card (s : Finset V) (v : V) (hv : v ∉ s) :
    (edgePart G (insert v s)).card = (edgePart G s).card + (neighborPart G s v).card := by
  have hd : Disjoint (edgePart G s)
      ((neighborPart G s v).image (fun w => s(v, w))) := by
    apply Finset.disjoint_left.mpr
    intro e he hi
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
    have hs := (Finset.mem_inter.mp he).2
    exact hv ((Finset.mk_mem_sym2_iff.mp hs).1)
  rw [edgePart_insert, Finset.card_union_of_disjoint hd]
  congr 1
  exact Finset.card_image_of_injective _ (Sym2.mkEmbedding v).injective

lemma neighborPart_union_le (s t : Finset V) (v : V) :
    (neighborPart G (s ∪ t) v).card ≤ (neighborPart G s v).card + t.card := by
  have he : neighborPart G (s ∪ t) v = neighborPart G s v ∪ neighborPart G t v := by
    simp [neighborPart, Finset.filter_union]
  rw [he]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (Finset.card_filter_le _ _) _)

lemma edgePart_union_bound (s t : Finset V) (D : ℕ)
    (hst : Disjoint s t)
    (hD : ∀ v ∈ t, (neighborPart G s v).card ≤ D) :
    (edgePart G (s ∪ t)).card ≤
      (edgePart G s).card + t.card * D + t.card.choose 2 := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert v t hvt ih =>
    have hvs : v ∉ s := by
      intro hv
      exact Finset.disjoint_left.mp hst hv (Finset.mem_insert_self _ _)
    have hst' : Disjoint s t := hst.mono_right (Finset.subset_insert _ _)
    have htD : ∀ w ∈ t, (neighborPart G s w).card ≤ D :=
      fun w hw => hD w (Finset.mem_insert_of_mem hw)
    have hvD := hD v (Finset.mem_insert_self _ _)
    have hnew : v ∉ s ∪ t := by simp [hvs, hvt]
    have hset : s ∪ insert v t = insert v (s ∪ t) := by ext; simp
    rw [hset, edgePart_insert_card G _ _ hnew]
    calc
      (edgePart G (s ∪ t)).card + (neighborPart G (s ∪ t) v).card ≤
          ((edgePart G s).card + t.card * D + t.card.choose 2) + (D + t.card) := by
        exact Nat.add_le_add (ih hst' htD)
          ((neighborPart_union_le G s t v).trans (Nat.add_le_add_right hvD _))
      _ = (edgePart G s).card + (insert v t).card * D + (insert v t).card.choose 2 := by
        rw [Finset.card_insert_of_notMem hvt]
        simp only [Nat.choose_succ_succ, Nat.choose_one_right]
        ring

lemma neighborPart_erase_self (s : Finset V) (v : V) :
    neighborPart G (s.erase v) v = neighborPart G s v := by
  ext w
  by_cases hw : w = v
  · subst w
    simp [neighborPart]
  · simp [neighborPart, hw]

lemma neighborPart_le_erase_add_one (s : Finset V) (w v : V) :
    (neighborPart G s v).card ≤ (neighborPart G (s.erase w) v).card + 1 := by
  have hs : neighborPart G s v ⊆ insert w (neighborPart G (s.erase w) v) := by
    intro x hx
    by_cases h : x = w
    · subst x
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      have hh := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨h, hh.1⟩, hh.2⟩
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

/-- A maximum-edge m-vertex induced subgraph controls all edges outside it
through its true minimum degree. This is valid for every finite simple graph. -/
theorem exists_dense_induced_subset (m : ℕ) (hm0 : 0 < m) (hm : m ≤ Fintype.card V) :
    ∃ s : Finset V, s.card = m ∧
      G.edgeFinset.card ≤ (G.induce (↑s : Set V)).edgeFinset.card +
        (Fintype.card V - m) * (G.induce (↑s : Set V)).minDegree +
        (Fintype.card V - m + 1).choose 2 := by
  classical
  have hnon : ((Finset.univ : Finset V).powersetCard m).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    have hh := Finset.powersetCard_eq_empty.mp h
    simp only [Finset.card_univ] at hh
    omega
  obtain ⟨s, hsmem, hsmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset V).powersetCard m) (fun t => (edgePart G t).card) hnon
  have hs : s.card = m := (Finset.mem_powersetCard.mp hsmem).2
  have hsn : s.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty (↑s : Set V) := ⟨⟨hsn.choose, hsn.choose_spec⟩⟩
  let H := G.induce (↑s : Set V)
  obtain ⟨w, hw⟩ := H.exists_minimal_degree_vertex
  have hws : w.val ∈ s := w.property
  have hbase : (edgePart G s).card =
      (edgePart G (s.erase w.val)).card + (neighborPart G s w.val).card := by
    have hh := edgePart_insert_card G (s.erase w.val) w.val (Finset.notMem_erase _ _)
    rw [Finset.insert_erase hws, neighborPart_erase_self] at hh
    exact hh
  have hwdeg : (neighborPart G s w.val).card = H.minDegree := by
    rw [neighborPart_card G s w, ← hw]
  have hout : ∀ u ∈ (Finset.univ \ s), (neighborPart G s u).card ≤ H.minDegree + 1 := by
    intro u hu
    have hus : u ∉ s := (Finset.mem_sdiff.mp hu).2
    have hue : u ∉ s.erase w.val := fun h => hus (Finset.mem_of_mem_erase h)
    have hswapcard : (insert u (s.erase w.val)).card = m := by
      rw [Finset.card_insert_of_notMem hue, Finset.card_erase_of_mem hws]
      omega
    have hswap := hsmax (insert u (s.erase w.val))
      (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hswapcard⟩)
    rw [edgePart_insert_card G _ _ hue, hbase] at hswap
    have hsmall : (neighborPart G (s.erase w.val) u).card ≤ H.minDegree := by
      rw [← hwdeg]
      omega
    exact (neighborPart_le_erase_add_one G s w.val u).trans (Nat.add_le_add_right hsmall 1)
  have hdis : Disjoint s (Finset.univ \ s) := by
    exact Finset.disjoint_left.mpr (fun x hx hxs => (Finset.mem_sdiff.mp hxs).2 hx)
  have hb := edgePart_union_bound G s (Finset.univ \ s) (H.minDegree + 1) hdis hout
  have hcover : s ∪ (Finset.univ \ s) = Finset.univ := by ext; simp
  have hcard : (Finset.univ \ s).card = Fintype.card V - m := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ, hs]
  rw [hcover, hcard] at hb
  have he : (edgePart G Finset.univ).card = G.edgeFinset.card := by simp [edgePart]
  rw [he, edgePart_card] at hb
  refine ⟨s, hs, ?_⟩
  calc
    G.edgeFinset.card ≤ (G.induce (↑s : Set V)).edgeFinset.card +
        (Fintype.card V - m) * (H.minDegree + 1) + (Fintype.card V - m).choose 2 := hb
    _ = (G.induce (↑s : Set V)).edgeFinset.card +
        (Fintype.card V - m) * (G.induce (↑s : Set V)).minDegree +
        (Fintype.card V - m + 1).choose 2 := by
      simp only [Nat.choose_succ_succ, Nat.choose_one_right]
      dsimp [H]
      ring

#print axioms exists_dense_induced_subset

end JSP842
