import JSP619Moore
import JSP619ExpansionPath

set_option maxHeartbeats 1600000

namespace JSP619
namespace Expansion
open Finset SimpleGraph

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

lemma neighborPart_erase_self (s : Finset V) (v : V) :
    neighborPart G (s.erase v) v = neighborPart G s v := by
  ext w
  by_cases hw : w = v
  · subst w
    simp [neighborPart]
  · simp [neighborPart, hw]

theorem exists_min_degree_core (T : Finset V) (d : ℕ)
    (hT : d * T.card < (edgePart G T).card) :
    ∃ S : Finset V, S ⊆ T ∧ S.Nonempty ∧
      ∀ v : (↑S : Set V), d + 1 ≤ (G.induce (↑S : Set V)).degree v := by
  classical
  let A := T.powerset.filter (fun S => d * S.card < (edgePart G S).card)
  have hTA : T ∈ A := by simp [A, hT]
  obtain ⟨S, hSA, hmin⟩ := A.exists_min_image Finset.card ⟨T, hTA⟩
  have hST := mem_powerset.mp (mem_filter.mp hSA).1
  have hS := (mem_filter.mp hSA).2
  have hne : S.Nonempty := by
    by_contra hempty
    have : S = ∅ := not_nonempty_iff_eq_empty.mp hempty
    subst S
    simpa [edgePart] using hS
  refine ⟨S, hST, hne, ?_⟩
  intro v
  by_contra hdeg
  have hd : (neighborPart G S v).card ≤ d := by
    rw [neighborPart_card G S v]
    omega
  have hv : (v : V) ∈ S := v.2
  have hcard := card_erase_add_one hv
  have hedges : (edgePart G S).card =
      (edgePart G (S.erase v)).card + (neighborPart G S v).card := by
    have h := edgePart_insert_card G (S.erase v) v (by simp)
    rw [insert_erase hv, neighborPart_erase_self] at h
    exact h
  have herase : d * (S.erase v).card < (edgePart G (S.erase v)).card := by
    nlinarith
  have heraseA : S.erase v ∈ A := mem_filter.mpr
    ⟨mem_powerset.mpr ((erase_subset _ _).trans hST), herase⟩
  have := hmin _ heraseA
  omega

theorem sum_neighborPart (T : Finset V) :
    (∑ v ∈ T, (neighborPart G T v).card) = 2 * (edgePart G T).card := by
  rw [Finset.sum_subtype T (fun _ => Iff.rfl)]
  calc
    (∑ v : (↑T : Set V), (neighborPart G T v).card) =
        ∑ v : (↑T : Set V), (G.induce (↑T : Set V)).degree v := by
      apply sum_congr rfl
      intro v _
      exact neighborPart_card G T v
    _ = 2 * (G.induce (↑T : Set V)).edgeFinset.card :=
      (G.induce (↑T : Set V)).sum_degrees_eq_twice_card_edges
    _ = 2 * (edgePart G T).card := by rw [edgePart_card]

theorem neighborPart_union_external (S : Finset V) (v : V) (hv : v ∈ S) :
    neighborPart G (S ∪ externalNeighbors G S) v = G.neighborFinset v := by
  ext w
  constructor
  · intro hw
    exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hw).2
  · intro hw
    have hadj := (G.mem_neighborFinset _ _).mp hw
    apply mem_filter.mpr
    refine ⟨?_, hadj⟩
    by_cases hws : w ∈ S
    · exact mem_union_left _ hws
    · exact mem_union_right _ (mem_filter.mpr
        ⟨mem_sdiff.mpr ⟨mem_univ _, hws⟩, v, hv, hadj⟩)

end Expansion

open Finset SimpleGraph

theorem small_set_expansion {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d s : ℕ)
    (hd : 1 ≤ d) (hs : 1 ≤ s) (hdeg : ∀ v, 6 * (d + 1) ≤ G.degree v)
    (hgirth : ∀ v (p : G.Walk v v), p.IsCycle → 2 * s < p.length) :
    ∀ S : Finset V, 0 < S.card → 3 * S.card ≤ d ^ s →
      2 * S.card < (externalNeighbors G S).card := by
  classical
  intro S hS hsmall
  by_contra hbad
  have hN : (externalNeighbors G S).card ≤ 2 * S.card := by omega
  let T := S ∪ externalNeighbors G S
  have hST : S ⊆ T := subset_union_left
  have hTcard : T.card ≤ 3 * S.card := by
    have := card_union_le S (externalNeighbors G S)
    dsimp [T]
    omega
  have hsum : 6 * (d + 1) * S.card ≤ 2 * (Expansion.edgePart G T).card := by
    calc
      6 * (d + 1) * S.card = ∑ _v ∈ S, 6 * (d + 1) := by simp [mul_comm]
      _ ≤ ∑ v ∈ S, (Expansion.neighborPart G T v).card := by
        apply sum_le_sum
        intro v hv
        rw [show T = S ∪ externalNeighbors G S from rfl,
          Expansion.neighborPart_union_external G S v hv,
          G.card_neighborFinset_eq_degree]
        exact hdeg v
      _ ≤ ∑ v ∈ T, (Expansion.neighborPart G T v).card :=
        sum_le_sum_of_subset_of_nonneg hST (by intros; omega)
      _ = 2 * (Expansion.edgePart G T).card := Expansion.sum_neighborPart G T
  have hdense : d * T.card < (Expansion.edgePart G T).card := by
    have hmult := Nat.mul_le_mul_left d hTcard
    nlinarith
  obtain ⟨U, hUT, hUne, hUdeg⟩ := Expansion.exists_min_degree_core G T d hdense
  letI : Nonempty (↑U : Set V) := hUne.to_set.to_subtype
  let H := G.induce (↑U : Set V)
  have hUgirth : ∀ v (p : H.Walk v v), p.IsCycle → 2 * s < p.length := by
    intro v p hp
    let f : H →g G := (SimpleGraph.Embedding.induce (↑U : Set V)).toHom
    have hc : (p.map f).IsCycle := hp.map Subtype.val_injective
    exact (hgirth (v : V) (p.map f) hc).trans_eq (SimpleGraph.Walk.length_map f p)
  have hmoore := moore_card_gt_pow H d s hd hs hUdeg hUgirth
  have hUcard := card_le_card hUT
  have hc : Fintype.card (↑U : Set V) = U.card := by simp
  rw [hc] at hmoore
  omega

#print axioms small_set_expansion
end JSP619

