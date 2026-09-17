import JSP619Layers

/-!
# Edge-disjoint BFS bands and a dense band core

Every edge is assigned to the smaller depth of its endpoints. This keeps
same-layer edges at their own level, and makes the upper layer independent.
The counting and the nonempty core extraction are explicit. No maximum-cut,
bipartite-subgraph, or average-degree selection theorem is assumed.
-/
noncomputable section
open Finset Function
namespace JSP619
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- All edges having minimum endpoint level i. -/
def band (G : SimpleGraph V) (level : V → ℕ) (i : ℕ) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ min (level v) (level w) = i
  symm := ⟨fun _ _ h => ⟨h.1.symm, by simpa [min_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

def bandHom (G : SimpleGraph V) (level : V → ℕ) (i : ℕ) : band G level i →g G where
  toFun := id
  map_rel' := fun h => h.1

def bandVertices (level : V → ℕ) (i : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => level v = i ∨ level v = i + 1)

@[simp] lemma mem_bandVertices {level : V → ℕ} {i : ℕ} {v : V} :
    v ∈ bandVertices level i ↔ level v = i ∨ level v = i + 1 := by
  classical
  simp [bandVertices]

lemma band_supported (T : LayerTree G) (i : ℕ) {v w : V}
    (h : (band G T.level i).Adj v w) :
    v ∈ bandVertices T.level i ∧ w ∈ bandVertices T.level i := by
  have h1 := T.edge_level v w h.1
  have h2 := T.edge_level w v h.1.symm
  have hmin : min (T.level v) (T.level w) = i := h.2
  constructor <;> apply mem_bandVertices.mpr <;> omega

/-- Removing isolated ambient vertices does not change the edge mass. -/
lemma mass_univ_eq_of_supported (H : SimpleGraph V) (A : Finset V)
    (hsupp : ∀ v w, H.Adj v w → v ∈ A ∧ w ∈ A) :
    mass H Finset.univ = mass H A := by
  classical
  have hdeg (v : V) : degIn H Finset.univ v = degIn H A v := by
    apply congrArg Finset.card
    ext w
    simp only [mem_neighborsIn, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨(hsupp v w h).2, h⟩, And.right⟩
  have hzero (v : V) (hv : v ∉ A) : degIn H A v = 0 := by
    have he : neighborsIn H A v = ∅ := by
      ext w
      simp only [mem_neighborsIn, Finset.notMem_empty, iff_false, not_and]
      intro _ h
      exact hv (hsupp v w h).1
    simp [degIn, he]
  unfold mass
  simp_rw [hdeg]
  symm
  apply Finset.sum_subset (Finset.subset_univ A)
  intro v _ hv
  exact hzero v hv

namespace LayerTree
variable (T : LayerTree G)

/-- An explicit finite range containing every layer number. -/
def bound : ℕ := (∑ v : V, T.level v) + 1

lemma level_lt_bound (v : V) : T.level v < T.bound := by
  have h : T.level v ≤ ∑ w : V, T.level w :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  dsimp [bound]
  omega

lemma sum_band_mass :
    (∑ i : Fin T.bound, mass (band G T.level i.val) (bandVertices T.level i.val)) =
      mass G Finset.univ := by
  classical
  have hfull (i : Fin T.bound) :
      mass (band G T.level i.val) (bandVertices T.level i.val) =
        mass (band G T.level i.val) Finset.univ :=
    (mass_univ_eq_of_supported _ _ (fun _ _ h => band_supported T i.val h)).symm
  simp_rw [hfull, mass, degIn_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : G.Adj v w
  · let j : Fin T.bound := ⟨min (T.level v) (T.level w),
      (min_le_left _ _).trans_lt (T.level_lt_bound v)⟩
    have he (i : Fin T.bound) :
        (min (T.level v) (T.level w) = i.val) ↔ i = j := by
      constructor
      · intro hi
        apply Fin.ext
        exact hi.symm
      · rintro rfl
        rfl
    simp only [band, h, true_and, he]
    simp
  · simp [band, h]

/-- Each vertex occurs in at most two bands, including boundary layers. -/
lemma sum_band_card_le :
    (∑ i : Fin T.bound, (bandVertices T.level i.val).card) ≤ 2 * Fintype.card V := by
  classical
  let A := fun i : Fin T.bound => bandVertices T.level i.val
  let f : (Σ i : Fin T.bound, ↥(A i)) → V × Bool := fun z =>
    (z.2.1, decide (T.level z.2.1 = z.1.val))
  have hf : Injective f := by
    rintro ⟨i, vi⟩ ⟨j, vj⟩ h
    have hv : vi.1 = vj.1 := congrArg Prod.fst h
    have hb : decide (T.level vi.1 = i.val) = decide (T.level vj.1 = j.val) :=
      congrArg Prod.snd h
    have hvi := mem_bandVertices.mp vi.2
    have hvj := mem_bandVertices.mp vj.2
    have hij : i = j := by
      apply Fin.ext
      rw [← hv] at hb hvj
      by_cases hi : T.level vi.1 = i.val <;>
        by_cases hj : T.level vi.1 = j.val <;>
        simp [hi, hj] at hb <;> omega
    subst j
    congr 1
    exact Subtype.ext hv
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_coe, A, Nat.mul_comm] using hc

/-- A band contains a nonempty core of minimum degree 6*(d+1).
The factor 48 leaves harmless slack in the finite weighted averaging. -/
theorem exists_band_core [DecidableRel G.Adj] (d : ℕ)
    (hdeg : ∀ v, 48 * (d + 1) ≤ G.degree v) :
    ∃ (i : ℕ) (B : Finset V), B.Nonempty ∧ B ⊆ bandVertices T.level i ∧
      ∀ v ∈ B, 6 * (d + 1) ≤ degIn (band G T.level i) B v := by
  classical
  have hden : 48 * (d + 1) * Fintype.card V ≤ mass G Finset.univ := by
    calc
      48 * (d + 1) * Fintype.card V = ∑ _v : V, 48 * (d + 1) := by
        simp [Nat.mul_comm]
      _ ≤ mass G Finset.univ := by
        unfold mass
        apply Finset.sum_le_sum
        intro v _
        simpa using hdeg v
  have hex : ∃ i : Fin T.bound,
      (bandVertices T.level i.val).Nonempty ∧
      12 * (d + 1) * (bandVertices T.level i.val).card ≤
        mass (band G T.level i.val) (bandVertices T.level i.val) := by
    by_contra! hnone
    have hone (i : Fin T.bound) :
        mass (band G T.level i.val) (bandVertices T.level i.val) ≤
          12 * (d + 1) * (bandVertices T.level i.val).card := by
      by_cases hi : (bandVertices T.level i.val).Nonempty
      · exact (hnone i hi).le
      · have he := Finset.not_nonempty_iff_eq_empty.mp hi
        simp [he]
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin T.bound))) => hone i)
    rw [T.sum_band_mass, ← Finset.mul_sum] at hsum
    have hmul := Nat.mul_le_mul_left (12 * (d + 1)) T.sum_band_card_le
    have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨T.root⟩
    have hpositive : 0 < 24 * (d + 1) * Fintype.card V :=
      Nat.mul_pos (by omega) hn
    nlinarith
  obtain ⟨i, hi, hiDen⟩ := hex
  have hiDen' : 2 * (6 * (d + 1)) * (bandVertices T.level i.val).card ≤
      mass (band G T.level i.val) (bandVertices T.level i.val) := by
    nlinarith
  obtain ⟨B, hBsub, hBne, hBd⟩ := exists_core (band G T.level i.val)
    (bandVertices T.level i.val) (6 * (d + 1)) (by omega) hi hiDen'
  exact ⟨i.val, B, hBne, hBsub, hBd⟩

end LayerTree

#print axioms LayerTree.sum_band_mass
#print axioms LayerTree.sum_band_card_le
#print axioms LayerTree.exists_band_core

end JSP619
end
