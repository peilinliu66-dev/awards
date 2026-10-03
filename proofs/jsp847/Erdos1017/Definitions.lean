import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs

/-!
# Exact clique partitions for Erdős 1017

Original research source, 2026-10-03. UNCOMPILED.
The structure records unique ownership of every edge. A clique cover does not
satisfy this interface unless its edges are in fact pairwise disjoint.
-/

open scoped BigOperators

namespace Erdos1017

variable {V : Type*} [DecidableEq V]

/-- A finite vertex set spanning a complete subgraph. -/
def IsClique (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v

/-- An exact edge partition into nontrivial complete subgraphs. -/
structure CliquePartition (G : SimpleGraph V) where
  blocks : Finset (Finset V)
  nontrivial : ∀ C ∈ blocks, 2 ≤ C.card
  clique : ∀ C ∈ blocks, IsClique G C
  owns : ∀ u v, G.Adj u v → ∃! C, C ∈ blocks ∧ u ∈ C ∧ v ∈ C

namespace CliquePartition

variable {G : SimpleGraph V}

def count (P : CliquePartition G) : ℕ := P.blocks.card

def weight (P : CliquePartition G) : ℕ := ∑ C ∈ P.blocks, C.card

theorem two_mul_count_le_weight (P : CliquePartition G) :
    2 * P.count ≤ P.weight := by
  classical
  have h := Finset.sum_le_sum (s := P.blocks)
    (f := fun _ => (2 : ℕ)) (g := fun C => C.card)
    (fun C hC => P.nontrivial C hC)
  simpa [count, weight, Nat.mul_comm] using h

theorem eq_of_shared_edge (P : CliquePartition G)
    {C D : Finset V} (hC : C ∈ P.blocks) (hD : D ∈ P.blocks)
    {u v : V} (huC : u ∈ C) (hvC : v ∈ C)
    (huD : u ∈ D) (hvD : v ∈ D) (huv : u ≠ v) : C = D := by
  obtain ⟨E, _, hE⟩ := P.owns u v (P.clique C hC u huC v hvC huv)
  exact (hE C ⟨hC, huC, hvC⟩).trans (hE D ⟨hD, huD, hvD⟩).symm

end CliquePartition

variable [Fintype V]

/-- Number of unoriented edges; loops never contribute. -/
noncomputable def edgeCount (G : SimpleGraph V) : ℕ := by
  classical
  exact G.edgeFinset.card

/-- The minimum number of pieces in an exact clique partition.
Existence and attainment are proved separately, not postulated in this definition.
-/
noncomputable def partitionNumber (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ P : CliquePartition G, P.count = m}

/-- The classical balanced bipartite edge threshold. -/
def balancedThreshold (n : ℕ) : ℕ := n ^ 2 / 4

/-- Intended unconditional final endpoint; this file does not assert it. -/
def DenseSavingStatement : Prop :=
  ∀ G : SimpleGraph V,
    5000 * partitionNumber G + edgeCount G ≤
      5001 * balancedThreshold (Fintype.card V)

end Erdos1017
