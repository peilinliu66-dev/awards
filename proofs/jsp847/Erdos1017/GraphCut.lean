/-
Copyright (c) 2026. Released under the Apache License 2.0.
Original finite counting and maximum-degree cut proof. UNCOMPILED.
-/
import Erdos1017.Definitions
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace Erdos1017

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

local instance graphAdjDecidable (G : SimpleGraph V) : DecidableRel G.Adj :=
  Classical.decRel _

/-- The induced graph on `S`, retaining the ambient type and isolating its complement. -/
def onVertices (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

/-- Oriented incidences between two finite vertex sets. For disjoint sets each
crossing edge is counted once; for equal sets each internal edge is counted twice. -/
noncomputable def incidenceCount (G : SimpleGraph V) (A B : Finset V) : ℕ := by
  classical
  exact ∑ u ∈ A, ∑ v ∈ B, if G.Adj u v then 1 else 0

/-- Missing crossing pairs. This definition avoids natural-number subtraction. -/
noncomputable def missingCount (G : SimpleGraph V) (A B : Finset V) : ℕ := by
  classical
  exact ∑ u ∈ A, ∑ v ∈ B, if G.Adj u v then 0 else 1

theorem degree_eq_indicator_sum (G : SimpleGraph V) (u : V) :
    G.degree u = ∑ v : V, if G.Adj u v then 1 else 0 := by
  classical
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_filter]

theorem incidenceCount_symm (G : SimpleGraph V) (A B : Finset V) :
    incidenceCount G A B = incidenceCount G B A := by
  classical
  unfold incidenceCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  simp only [G.adj_comm]

theorem incidenceCount_univ_right (G : SimpleGraph V) (A : Finset V) :
    incidenceCount G A Finset.univ = ∑ u ∈ A, G.degree u := by
  classical
  unfold incidenceCount
  apply Finset.sum_congr rfl
  intro u _
  exact (degree_eq_indicator_sum G u).symm

theorem incidenceCount_univ (G : SimpleGraph V) :
    incidenceCount G Finset.univ Finset.univ = 2 * edgeCount G := by
  classical
  rw [incidenceCount_univ_right]
  exact G.sum_degrees_eq_twice_card_edges

theorem incidenceCount_split_left (G : SimpleGraph V) (A B : Finset V) :
    incidenceCount G Finset.univ B =
      incidenceCount G A B + incidenceCount G Aᶜ B := by
  classical
  exact (Finset.sum_add_sum_compl A
    (fun u => ∑ v ∈ B, if G.Adj u v then 1 else 0)).symm

theorem incidenceCount_split_right (G : SimpleGraph V) (A B : Finset V) :
    incidenceCount G A Finset.univ =
      incidenceCount G A B + incidenceCount G A Bᶜ := by
  rw [incidenceCount_symm G A Finset.univ,
    incidenceCount_split_left G B A,
    incidenceCount_symm G B A, incidenceCount_symm G Bᶜ A]

theorem incidenceCount_onVertices (G : SimpleGraph V) (S : Finset V) :
    incidenceCount (onVertices G S) Finset.univ Finset.univ =
      incidenceCount G S S := by
  classical
  have hfilter : (Finset.univ : Finset V).filter (· ∈ S) = S := by
    ext v
    simp
  calc
    incidenceCount (onVertices G S) Finset.univ Finset.univ =
        ∑ u ∈ (Finset.univ : Finset V).filter (· ∈ S),
          ∑ v ∈ (Finset.univ : Finset V).filter (· ∈ S),
            if G.Adj u v then 1 else 0 := by
      simp only [incidenceCount, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : u ∈ S
      · simp only [hu, if_true]
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v ∈ S <;> by_cases hadj : G.Adj u v <;>
          simp [onVertices, hu, hv, hadj]
      · simp [onVertices, hu]
    _ = incidenceCount G S S := by rw [hfilter]; rfl

theorem incidenceCount_self (G : SimpleGraph V) (S : Finset V) :
    incidenceCount G S S = 2 * edgeCount (onVertices G S) := by
  rw [← incidenceCount_onVertices, incidenceCount_univ]

theorem incidenceCount_add_missing (G : SimpleGraph V) (A B : Finset V) :
    incidenceCount G A B + missingCount G A B = A.card * B.card := by
  classical
  calc
    incidenceCount G A B + missingCount G A B =
        ∑ u ∈ A, ∑ v ∈ B,
          ((if G.Adj u v then 1 else 0) +
            (if G.Adj u v then 0 else 1)) := by
      simp [incidenceCount, missingCount, Finset.sum_add_distrib]
    _ = ∑ _u ∈ A, ∑ _v ∈ B, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : G.Adj u v <;> simp [h]
    _ = A.card * B.card := by simp

theorem edgeCount_cut (G : SimpleGraph V) (A : Finset V) :
    edgeCount G = edgeCount (onVertices G A) +
      edgeCount (onVertices G Aᶜ) + incidenceCount G A Aᶜ := by
  have ht := incidenceCount_univ G
  rw [incidenceCount_split_left G A Finset.univ,
    incidenceCount_split_right G A A,
    incidenceCount_split_right G Aᶜ A,
    incidenceCount_symm G Aᶜ A,
    incidenceCount_self G A, incidenceCount_self G Aᶜ] at ht
  omega

theorem sum_degrees_compl (G : SimpleGraph V) (A : Finset V) :
    (∑ v ∈ Aᶜ, G.degree v) = incidenceCount G A Aᶜ +
      2 * edgeCount (onVertices G Aᶜ) := by
  rw [← incidenceCount_univ_right, incidenceCount_split_right G Aᶜ A,
    incidenceCount_symm G Aᶜ A, incidenceCount_self]

theorem onVertices_eq_bot_of_independent (G : SimpleGraph V) (A : Finset V)
    (hind : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v) :
    onVertices G A = ⊥ := by
  ext u v
  simp only [onVertices, SimpleGraph.bot_adj, iff_false]
  rintro ⟨h, hu, hv⟩
  exact hind u hu v hv h

theorem edgeCount_onVertices_eq_zero (G : SimpleGraph V) (A : Finset V)
    (hind : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v) :
    edgeCount (onVertices G A) = 0 := by
  rw [onVertices_eq_bot_of_independent G A hind]
  classical
  simp [edgeCount]

/-- Explicit cycle formulation convenient for the triangle replacement proof. -/
def TriangleFree (G : SimpleGraph V) : Prop :=
  ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False

/-- An actual cut, rather than an assumed numerical stability estimate. -/
structure MantelCut (G : SimpleGraph V) where
  left : Finset V
  independent : ∀ u ∈ left, ∀ v ∈ left, ¬ G.Adj u v
  internal_le : (edgeCount (onVertices G leftᶜ) : ℝ) ≤
    (Fintype.card V : ℝ)^2 / 4 - edgeCount G
  missing_le : (missingCount G left leftᶜ : ℝ) ≤
    2 * ((Fintype.card V : ℝ)^2 / 4 - edgeCount G)
  balance_sq_le : ((left.card : ℝ) - (Fintype.card V : ℝ) / 2)^2 ≤
    2 * ((Fintype.card V : ℝ)^2 / 4 - edgeCount G)

/-- Quantitative Mantel stability from a maximum-degree vertex. There is no
Cauchy--Schwarz or unspecified extremal input in this proof. -/
theorem exists_mantelCut [Nonempty V] (G : SimpleGraph V)
    (htri : TriangleFree G) : Nonempty (MantelCut G) := by
  classical
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  let A := G.neighborFinset v
  have hcardA : A.card = G.degree v := rfl
  have hind : ∀ u ∈ A, ∀ w ∈ A, ¬ G.Adj u w := by
    intro u hu w hw huw
    have hvu : G.Adj v u := by simpa [A] using hu
    have hvw : G.Adj v w := by simpa [A] using hw
    exact htri v u w hvu huw hvw.symm
  have hzero := edgeCount_onVertices_eq_zero G A hind
  have hcut := edgeCount_cut G A
  rw [hzero, zero_add] at hcut
  have hdeg : ∀ u : V, G.degree u ≤ A.card := by
    intro u
    rw [hcardA, ← hv]
    exact G.degree_le_maxDegree u
  have hsum : (∑ u ∈ Aᶜ, G.degree u) ≤ Aᶜ.card * A.card := by
    calc
      (∑ u ∈ Aᶜ, G.degree u) ≤ ∑ _u ∈ Aᶜ, A.card :=
        Finset.sum_le_sum (fun u _ => hdeg u)
      _ = Aᶜ.card * A.card := by simp
  rw [sum_degrees_compl] at hsum
  have hcards : A.card + Aᶜ.card = Fintype.card V :=
    Finset.card_add_card_compl A
  have hmiss := incidenceCount_add_missing G A Aᶜ
  have hcutR : (edgeCount G : ℝ) =
      (edgeCount (onVertices G Aᶜ) : ℝ) + incidenceCount G A Aᶜ := by
    exact_mod_cast hcut
  have hsumR : (incidenceCount G A Aᶜ : ℝ) +
      2 * edgeCount (onVertices G Aᶜ) ≤ (Aᶜ.card : ℝ) * A.card := by
    exact_mod_cast hsum
  have hcardsR : (A.card : ℝ) + Aᶜ.card = Fintype.card V := by
    exact_mod_cast hcards
  have hmissR : (incidenceCount G A Aᶜ : ℝ) + missingCount G A Aᶜ =
      (A.card : ℝ) * Aᶜ.card := by
    exact_mod_cast hmiss
  have hcompR : (Aᶜ.card : ℝ) = (Fintype.card V : ℝ) - A.card := by
    linarith [hcardsR]
  have hprod : (A.card : ℝ) * Aᶜ.card =
      (Fintype.card V : ℝ)^2 / 4 -
        ((A.card : ℝ) - (Fintype.card V : ℝ) / 2)^2 := by
    rw [hcompR]
    ring
  have hsq := sq_nonneg ((A.card : ℝ) - (Fintype.card V : ℝ) / 2)
  have hb : (edgeCount (onVertices G Aᶜ) : ℝ) ≤
      (Fintype.card V : ℝ)^2 / 4 - edgeCount G := by
    nlinarith
  refine ⟨⟨A, hind, hb, ?_, ?_⟩⟩
  · nlinarith
  · have hm : (0 : ℝ) ≤ missingCount G A Aᶜ := Nat.cast_nonneg _
    nlinarith

end

end Erdos1017
