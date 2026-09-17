import Mathlib

/-!
# JSP-000656 / Erdos 799: the random-graph module

Target toolchain: Lean 4.33.1.
Target Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474.

This module and the complete JSP656 assembly have passed local Lean
compilation. Both terminal theorems report only propext, Classical.choice,
and Quot.sound. Package build evidence is recorded in verification/;
this is not official prize verification.

This file does not implement the separately assigned Hall/list-colouring lemma.
Its unconditional main result is `JSP656.badRich_tendsto_zero`.
`JSP656.assembly_from_localHallBound` is a generic assembly lemma; its explicit
hypothesis is precisely the deterministic corollary to be supplied by that
separate Hall module.  It is NOT an unconditional formalization of Erdos 799 by
itself.

Mathematical attribution: the list-chromatic-number problem was already solved
by Noga Alon (1992).  This work concerns formalization, not a claim of first
mathematical solution.  The proof here only targets the original o(n) bound.
-/

noncomputable section

open Function Filter Finset
open scoped Topology

namespace JSP656

attribute [local instance] Classical.propDecidable

universe u v w

/-! ## 1. Uniform finite counting, with no measure-theoretic assumptions -/

/-- The exact fraction of elements satisfying `P` in a finite universe. -/
def fraction {A : Type u} [Fintype A] (P : A → Prop) : ℝ := by
  classical
  exact (Fintype.card {a : A // P a} : ℝ) / (Fintype.card A : ℝ)

lemma fraction_nonneg {A : Type u} [Fintype A] (P : A → Prop) :
    0 ≤ fraction P := by
  classical
  unfold fraction
  positivity

lemma fraction_mono {A : Type u} [Fintype A] {P Q : A → Prop}
    (h : ∀ a, P a → Q a) : fraction P ≤ fraction Q := by
  classical
  unfold fraction
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Fintype.card_subtype_mono P Q h

@[simp] lemma fraction_false {A : Type u} [Fintype A] :
    fraction (fun _ : A => False) = 0 := by
  classical
  simp [fraction]

/-- Uniform counting is invariant under an actual bijection. -/
lemma fraction_equiv {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (e : A ≃ B) (P : B → Prop) :
    fraction (fun a => P (e a)) = fraction P := by
  classical
  let ep : {a : A // P (e a)} ≃ {b : B // P b} :=
    { toFun := fun a => ⟨e a.1, a.2⟩
      invFun := fun b => ⟨e.symm b.1, by simpa using b.2⟩
      left_inv := by intro a; apply Subtype.ext; simp
      right_inv := by intro b; apply Subtype.ext; simp }
  unfold fraction
  rw [Fintype.card_congr ep, Fintype.card_congr e]

/-- Finite union bound proved by an injection into the disjoint union of events. -/
lemma fraction_exists_le {A : Type u} {J : Type v}
    [Fintype A] [Fintype J] (P : J → A → Prop) :
    fraction (fun a => ∃ j, P j a) ≤ ∑ j : J, fraction (P j) := by
  classical
  let f : {a : A // ∃ j, P j a} → (Σ j : J, {a : A // P j a}) :=
    fun a => ⟨Classical.choose a.2, ⟨a.1, Classical.choose_spec a.2⟩⟩
  have hf : Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : Σ j : J, {a : A // P j a} => z.2.1) hab
  have hc : Fintype.card {a : A // ∃ j, P j a} ≤
      ∑ j : J, Fintype.card {a : A // P j a} := by
    simpa only [Fintype.card_sigma] using Fintype.card_le_of_injective f hf
  calc
    fraction (fun a => ∃ j, P j a) ≤
        (∑ j : J, (Fintype.card {a : A // P j a} : ℝ)) /
          (Fintype.card A : ℝ) := by
      unfold fraction
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      convert (Nat.cast_le.mpr hc :
        (Fintype.card {a : A // ∃ j, P j a} : ℝ) ≤
          (∑ j : J, Fintype.card {a : A // P j a} : ℕ)) using 1 <;>
        push_cast <;> congr 1
      simp only [Fintype.card_eq_nat_card]
    _ = ∑ j : J, fraction (P j) := by
      simp only [fraction, Finset.sum_div]

lemma card_all_finsets (A : Type u) [Fintype A] [DecidableEq A] :
    Fintype.card (Finset A) = 2 ^ Fintype.card A := by
  have he : (Finset.univ : Finset (Finset A)) =
      (Finset.univ : Finset A).powerset := by
    ext s
    simp
  calc
    Fintype.card (Finset A) = (Finset.univ : Finset (Finset A)).card := rfl
    _ = ((Finset.univ : Finset A).powerset).card := congrArg Finset.card he
    _ = 2 ^ Fintype.card A := by simp

/-! ## 2. Exact counts for disjoint blocks of Boolean coordinates -/

/-- Coordinates not used by an embedding. -/
abbrev Unused {D : Type u} {X : Type v} (e : D ↪ X) :=
  {x : X // x ∉ Set.range e}

/-- A block of bits other than the all-false block. -/
abbrev NonzeroBits (C : Type u) := {f : C → Bool // f ≠ (fun _ => false)}

/-- Every block is different from its all-false assignment. -/
def AvoidZero {B : Type u} {C : Type v} {X : Type w}
    (e : (B × C) ↪ X) (ω : X → Bool) : Prop :=
  ∀ b : B, (fun c : C => ω (e (b, c))) ≠ (fun _ => false)

/-- Restriction to the used coordinates and to their complement is a bijection. -/
def splitBits {B : Type u} {C : Type v} {X : Type w}
    (e : (B × C) ↪ X) :
    (X → Bool) ≃ (B → C → Bool) × (Unused e → Bool) := by
  classical
  let r : (B × C) ≃ Set.range e := Equiv.ofInjective e e.injective
  exact
    { toFun := fun ω => (fun b c => ω (e (b, c)), fun x => ω x.1)
      invFun := fun z x =>
        if h : x ∈ Set.range e then
          z.1 (r.symm ⟨x, h⟩).1 (r.symm ⟨x, h⟩).2
        else z.2 ⟨x, h⟩
      left_inv := by
        intro ω
        funext x
        dsimp
        split_ifs with hx
        · have hh : e (r.symm ⟨x, hx⟩) = x :=
            Equiv.apply_ofInjective_symm e.injective ⟨x, hx⟩
          exact congrArg ω hh
        · rfl
      right_inv := by
        rintro ⟨f, g⟩
        apply Prod.ext
        · funext b c
          simp [r]
        · funext x
          simp [Unused, x.2] }

@[simp] lemma splitBits_apply_fst {B : Type u} {C : Type v} {X : Type w}
    (e : (B × C) ↪ X) (ω : X → Bool) (b : B) (c : C) :
    (splitBits e ω).1 b c = ω (e (b, c)) := rfl

@[simp] lemma splitBits_apply_snd {B : Type u} {C : Type v} {X : Type w}
    (e : (B × C) ↪ X) (ω : X → Bool) (x : Unused e) :
    (splitBits e ω).2 x = ω x.1 := rfl

@[simp] lemma splitBits_symm_image {B : Type u} {C : Type v} {X : Type w}
    (e : (B × C) ↪ X) (z : (B → C → Bool) × (Unused e → Bool))
    (b : B) (c : C) :
    (splitBits e).symm z (e (b, c)) = z.1 b c := by
  have h := congrArg (fun y => y.1 b c) ((splitBits e).apply_symm_apply z)
  exact h

@[simp] lemma splitBits_symm_unused {B : Type u} {C : Type v} {X : Type w}
    (e : (B × C) ↪ X) (z : (B → C → Bool) × (Unused e → Bool))
    (x : Unused e) :
    (splitBits e).symm z x.1 = z.2 x := by
  have h := congrArg (fun y => y.2 x) ((splitBits e).apply_symm_apply z)
  exact h

/-- The avoidance event is a product of nonzero block assignments and unused bits. -/
def avoidZeroEquiv {B : Type u} {C : Type v} {X : Type w}
    (e : (B × C) ↪ X) :
    {ω : X → Bool // AvoidZero e ω} ≃
      (B → NonzeroBits C) × (Unused e → Bool) where
  toFun ω := (fun b => ⟨fun c => ω.1 (e (b, c)), ω.2 b⟩,
    fun x => ω.1 x.1)
  invFun z :=
    ⟨(splitBits e).symm (fun b c => (z.1 b).1 c, z.2), by
      intro b
      simpa only [splitBits_symm_image] using (z.1 b).2⟩
  left_inv := by
    intro ω
    apply Subtype.ext
    apply (splitBits e).injective
    rw [Equiv.apply_symm_apply]
    rfl
  right_inv := by
    intro z
    apply Prod.ext
    · funext b
      apply Subtype.ext
      funext c
      simp only [splitBits_symm_image]
    · funext x
      simp only [splitBits_symm_unused]

lemma card_nonzeroBits (C : Type u) [Fintype C] :
    Fintype.card (NonzeroBits C) = 2 ^ Fintype.card C - 1 := by
  classical
  change Fintype.card {f : C → Bool // ¬f = (fun _ => false)} = _
  rw [Fintype.card_subtype_compl]
  simp

lemma card_unused {D : Type u} {X : Type v} [Fintype D] [Fintype X]
    (e : D ↪ X) :
    Fintype.card (Unused e) = Fintype.card X - Fintype.card D := by
  classical
  change Fintype.card (↥((Set.range e)ᶜ : Set X)) = _
  rw [Fintype.card_compl_set]
  rw [← Fintype.card_congr (Equiv.ofInjective e e.injective)]

/-- Exact integer cylinder count, including all unqueried edge coordinates. -/
theorem avoidZero_count {B : Type u} {C : Type v} {X : Type w}
    [Fintype B] [Fintype C] [Fintype X] (e : (B × C) ↪ X) :
    Fintype.card {ω : X → Bool // AvoidZero e ω} =
      (2 ^ Fintype.card C - 1) ^ Fintype.card B *
        2 ^ (Fintype.card X - Fintype.card B * Fintype.card C) := by
  classical
  have h := Fintype.card_congr (avoidZeroEquiv e)
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    card_nonzeroBits, card_unused] using h

/-- Exact finite probability; independence is proved by the preceding bijection. -/
theorem avoidZero_fraction {B : Type u} {C : Type v} {X : Type w}
    [Fintype B] [Fintype C] [Fintype X] (e : (B × C) ↪ X) :
    fraction (AvoidZero e) =
      (1 - (1 / 2 : ℝ) ^ Fintype.card C) ^ Fintype.card B := by
  classical
  let q := Fintype.card C
  let b := Fintype.card B
  let r := Fintype.card (Unused e)
  have hc : Fintype.card {ω : X → Bool // AvoidZero e ω} =
      (2 ^ q - 1) ^ b * 2 ^ r := by
    simpa [q, b, r, card_nonzeroBits] using Fintype.card_congr (avoidZeroEquiv e)
  have ht : Fintype.card (X → Bool) = (2 ^ q) ^ b * 2 ^ r := by
    simpa [q, b, r] using Fintype.card_congr (splitBits e)
  have hp : (1 : ℕ) ≤ 2 ^ q := by
    have : (0 : ℕ) < 2 ^ q := pow_pos (by decide) _
    omega
  have h2q : (2 : ℝ) ^ q ≠ 0 := by positivity
  have h2r : (2 : ℝ) ^ r ≠ 0 := by positivity
  have hbase : (((2 : ℝ) ^ q - 1) / (2 : ℝ) ^ q) =
      1 - (1 / 2 : ℝ) ^ q := by
    rw [div_pow, one_pow]
    field_simp [h2q] <;> ring
  unfold fraction
  rw [hc, ht]
  push_cast [Nat.cast_sub hp]
  calc
    (((2 : ℝ) ^ q - 1) ^ b * (2 : ℝ) ^ r) /
        (((2 : ℝ) ^ q) ^ b * (2 : ℝ) ^ r) =
        (((2 : ℝ) ^ q - 1) / (2 : ℝ) ^ q) ^ b := by
      rw [div_pow]
      field_simp [h2q, h2r] <;> ring
    _ = (1 - (1 / 2 : ℝ) ^ Fintype.card C) ^ Fintype.card B := by
      rw [hbase]

/-! ## 3. Edge coordinates and the actual uniform simple-graph universe -/

/-- An unordered pair of distinct vertices, represented as a two-element finset. -/
abbrev Edge (V : Type u) := {e : Finset V // e.card = 2}

lemma card_edge (V : Type u) [Fintype V] [DecidableEq V] :
    Fintype.card (Edge V) = (Fintype.card V).choose 2 := by
  classical
  calc
    Fintype.card (Edge V) = ((Finset.univ : Finset V).powersetCard 2).card := by
      apply Fintype.card_of_subtype
      intro e
      simp [Edge]
    _ = (Fintype.card V).choose 2 := by simp

/-- The edge with specified unequal endpoints. -/
def pairEdge {V : Type u} [DecidableEq V] (x y : V) (h : x ≠ y) : Edge V :=
  ⟨{x, y}, by simp [h]⟩

lemma edge_pair_rep {V : Type u} [DecidableEq V] (e : Edge V) :
    ∃ (x y : V) (h : x ≠ y), e = pairEdge x y h := by
  rcases Finset.card_eq_two.mp e.2 with ⟨x, y, hxy, he⟩
  exact ⟨x, y, hxy, Subtype.ext he⟩

/-- Transport unordered edge coordinates along a vertex embedding. -/
def mapEdge {V : Type u} {W : Type v} (f : V ↪ W) (e : Edge V) : Edge W :=
  ⟨e.1.map f, by simpa using e.2⟩

lemma mapEdge_injective {V : Type u} {W : Type v} (f : V ↪ W) :
    Injective (mapEdge f) := by
  classical
  intro e d h
  apply Subtype.ext
  have he : e.1.map f = d.1.map f := congrArg Subtype.val h
  ext x
  constructor
  · intro hx
    have hh : f x ∈ d.1.map f := by
      rw [← he]
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    rcases Finset.mem_map.mp hh with ⟨y, hy, hyx⟩
    have : y = x := f.injective hyx
    simpa [this] using hy
  · intro hx
    have hh : f x ∈ e.1.map f := by
      rw [he]
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    rcases Finset.mem_map.mp hh with ⟨y, hy, hyx⟩
    have : y = x := f.injective hyx
    simpa [this] using hy

@[simp] lemma mapEdge_pair {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W] (f : V ↪ W) (x y : V) (h : x ≠ y) :
    mapEdge f (pairEdge x y h) =
      pairEdge (f x) (f y) (fun he => h (f.injective he)) := by
  apply Subtype.ext
  simp [mapEdge, pairEdge]

/-- Decoding is directly into `SimpleGraph`, with symmetric and loopless adjacency. -/
def graphOfBits {V : Type u} [DecidableEq V] (ω : Edge V → Bool) : SimpleGraph V where
  Adj x y := ∃ h : ({x, y} : Finset V).card = 2, ω ⟨{x, y}, h⟩ = true
  symm := ⟨by
    intro x y h
    rcases h with ⟨hc, hw⟩
    refine ⟨by simpa [Finset.pair_comm] using hc, ?_⟩
    simpa [Finset.pair_comm] using hw⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨hc, _⟩
    simp at hc⟩

@[simp] lemma graphOfBits_adj {V : Type u} [DecidableEq V]
    (ω : Edge V → Bool) (x y : V) (h : x ≠ y) :
    (graphOfBits ω).Adj x y ↔ ω (pairEdge x y h) = true := by
  constructor
  · rintro ⟨hc, hw⟩
    exact hw
  · intro hw
    exact ⟨by simp [h], hw⟩

/-- Encoding a graph by the presence or absence of each two-vertex edge. -/
def bitsOfGraph {V : Type u} (G : SimpleGraph V) : Edge V → Bool := by
  classical
  exact fun e => decide (∃ x ∈ e.1, ∃ y ∈ e.1, G.Adj x y)

@[simp] lemma bitsOfGraph_pair {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (x y : V) (h : x ≠ y) :
    bitsOfGraph G (pairEdge x y h) = decide (G.Adj x y) := by
  classical
  simp [bitsOfGraph, pairEdge, G.adj_comm]

/-- Every bit assignment is exactly one labelled simple graph and conversely. -/
def bitsGraphEquiv (V : Type u) [DecidableEq V] :
    (Edge V → Bool) ≃ SimpleGraph V where
  toFun := graphOfBits
  invFun := bitsOfGraph
  left_inv := by
    intro ω
    funext e
    rcases edge_pair_rep e with ⟨x, y, h, rfl⟩
    rw [bitsOfGraph_pair, graphOfBits_adj ω x y h]
    cases ω (pairEdge x y h) <;> simp
  right_inv := by
    classical
    intro G
    ext x y
    by_cases h : x = y
    · subst y
      simp
    · rw [graphOfBits_adj (bitsOfGraph G) x y h, bitsOfGraph_pair]
      simp

lemma card_simpleGraphs (V : Type u) [Fintype V] [DecidableEq V] :
    Fintype.card (SimpleGraph V) = 2 ^ ((Fintype.card V).choose 2) := by
  have h := (Fintype.card_congr (bitsGraphEquiv V)).symm
  simpa [card_edge] using h

/-! ## 4. A reusable family of blocks whose edge sets are pairwise disjoint -/

/-- Two distinct common vertices force two block indices to be equal. -/
structure LinearBlocks (B : Type u) (W : Type v) (V : Type w) where
  vertex : B → (W ↪ V)
  common : ∀ (b c : B) (i j k l : W), i ≠ j →
    vertex b i = vertex c k → vertex b j = vertex c l → b = c

/-- Transport a family of blocks to a larger vertex universe. -/
def LinearBlocks.map {B : Type u} {W : Type v} {V : Type w} {Y : Type*}
    (P : LinearBlocks B W V) (f : V ↪ Y) : LinearBlocks B W Y where
  vertex b := (P.vertex b).trans f
  common := by
    intro b c i j k l hij h1 h2
    exact P.common b c i j k l hij (f.injective h1) (f.injective h2)

/-- Distinct blocks really do use disjoint edge coordinates. -/
def LinearBlocks.edgeEmbedding {B : Type u} {W : Type v} {V : Type w}
    (P : LinearBlocks B W V) : (B × Edge W) ↪ Edge V := by
  classical
  refine ⟨fun z => mapEdge (P.vertex z.1) z.2, ?_⟩
  rintro ⟨b, e⟩ ⟨c, f⟩ h
  have he : e.1.map (P.vertex b) = f.1.map (P.vertex c) :=
    congrArg Subtype.val h
  rcases Finset.card_eq_two.mp e.2 with ⟨i, j, hij, heij⟩
  have hi : P.vertex b i ∈ f.1.map (P.vertex c) := by
    rw [← he]
    exact Finset.mem_map.mpr ⟨i, by simp [heij], rfl⟩
  have hj : P.vertex b j ∈ f.1.map (P.vertex c) := by
    rw [← he]
    exact Finset.mem_map.mpr ⟨j, by simp [heij], rfl⟩
  rcases Finset.mem_map.mp hi with ⟨k, hk, hki⟩
  rcases Finset.mem_map.mp hj with ⟨l, hl, hlj⟩
  have hbc : b = c := P.common b c i j k l hij hki.symm hlj.symm
  subst c
  have hef : e = f := mapEdge_injective (P.vertex b) h
  subst f
  rfl

/-- The m by (m*t) grid. Its cardinality is m^2*t. -/
abbrev Grid (m t : ℕ) := Fin m × Fin (m * t)

/-- Line (a,b) consists of the m vertices (i,a+i*b). -/
def lineVertex (m t : ℕ) (z : Fin t × Fin t) : Fin m ↪ Grid m t where
  toFun i := (i, ⟨z.1.val + i.val * z.2.val, by
    have h1 : i.val * z.2.val ≤ i.val * t :=
      Nat.mul_le_mul_left i.val (Nat.le_of_lt z.2.isLt)
    have h2 : (i.val + 1) * t ≤ m * t :=
      Nat.mul_le_mul_right t (Nat.succ_le_of_lt i.isLt)
    nlinarith [z.1.isLt]⟩)
  inj' := by
    intro i j h
    exact congrArg Prod.fst h

/-- Integer lines have at most one common grid point unless their parameters coincide. -/
def gridBlocks (m t : ℕ) : LinearBlocks (Fin t × Fin t) (Fin m) (Grid m t) where
  vertex := lineVertex m t
  common := by
    intro b c i j k l hij h1 h2
    have hik : i = k := congrArg Prod.fst h1
    have hjl : j = l := congrArg Prod.fst h2
    subst k
    subst l
    have hc1 : b.1.val + i.val * b.2.val = c.1.val + i.val * c.2.val :=
      congrArg (fun z : Grid m t => z.2.val) h1
    have hc2 : b.1.val + j.val * b.2.val = c.1.val + j.val * c.2.val :=
      congrArg (fun z : Grid m t => z.2.val) h2
    have hz1 : (b.1.val : ℤ) + (i.val : ℤ) * b.2.val =
        (c.1.val : ℤ) + (i.val : ℤ) * c.2.val := by exact_mod_cast hc1
    have hz2 : (b.1.val : ℤ) + (j.val : ℤ) * b.2.val =
        (c.1.val : ℤ) + (j.val : ℤ) * c.2.val := by exact_mod_cast hc2
    have hp : ((i.val : ℤ) - j.val) * ((b.2.val : ℤ) - c.2.val) = 0 := by
      nlinarith only [hz1, hz2]
    have hi0 : ((i.val : ℤ) - j.val) ≠ 0 := by
      intro he
      apply hij
      apply Fin.ext
      exact_mod_cast sub_eq_zero.mp he
    have hbc2z : (b.2.val : ℤ) = c.2.val :=
      sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hi0)
    have hbc2 : b.2 = c.2 := by
      apply Fin.ext
      exact_mod_cast hbc2z
    have hbc1 : b.1 = c.1 := by
      apply Fin.ext
      rw [hbc2] at hc1
      omega
    exact Prod.ext hbc1 hbc2

/-- A finite type embeds into any finite type of at least its cardinality. -/
def embeddingOfCardLE {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (h : Fintype.card A ≤ Fintype.card B) : A ↪ B :=
  (Fintype.equivFin A).toEmbedding.trans
    (({ toFun := fun x => ⟨x.val, lt_of_lt_of_le x.isLt h⟩
        inj' := by intro x y hxy; exact Fin.ext (congrArg (fun z : Fin (Fintype.card B) => z.val) hxy) } :
          Fin (Fintype.card A) ↪ Fin (Fintype.card B)).trans
      (Fintype.equivFin B).symm.toEmbedding)

/-- Explicitly realized finite block packing inside an arbitrary sufficiently large set. -/
theorem exists_grid_packing {V : Type u} [Fintype V] [DecidableEq V]
    (U : Finset V) (m t : ℕ) (hcap : m * (m * t) ≤ U.card) :
    ∃ P : LinearBlocks (Fin t × Fin t) (Fin m) V,
      ∀ b i, P.vertex b i ∈ U := by
  classical
  let f : Grid m t ↪ ↥U := embeddingOfCardLE (by simpa [Grid] using hcap)
  let g : Grid m t ↪ V := f.trans (Function.Embedding.subtype (· ∈ U))
  refine ⟨(gridBlocks m t).map g, ?_⟩
  intro b i
  exact (f ((gridBlocks m t).vertex b i)).2

/-! ## 5. The exact interface to the separately implemented Hall module -/

/-- U contains exactly m pairwise nonadjacent vertices. -/
def HasIndependent {V : Type u} (G : SimpleGraph V) (U : Finset V) (m : ℕ) : Prop :=
  ∃ I : Finset V, I ⊆ U ∧ I.card = m ∧
    ∀ x ∈ I, ∀ y ∈ I, ¬G.Adj x y

/-- Every set of at least s vertices contains an independent m-set. -/
def Rich {V : Type u} (G : SimpleGraph V) (m s : ℕ) : Prop :=
  ∀ U : Finset V, s ≤ U.card → HasIndependent G U m

/-- With no independent m-set, every packed block has a present edge. -/
lemma noIndependent_implies_avoidZero {V : Type u} [Fintype V] [DecidableEq V]
    {m t : ℕ} (U : Finset V)
    (P : LinearBlocks (Fin t × Fin t) (Fin m) V)
    (hU : ∀ b i, P.vertex b i ∈ U) (ω : Edge V → Bool)
    (hbad : ¬HasIndependent (graphOfBits ω) U m) :
    AvoidZero P.edgeEmbedding ω := by
  classical
  intro b hz
  apply hbad
  let I : Finset V := Finset.univ.map (P.vertex b)
  refine ⟨I, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
    exact hU b i
  · simp [I]
  · intro x hx y hy hxy
    rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨j, hj, rfl⟩
    by_cases hij : i = j
    · subst j
      simpa using hxy
    · have hne : P.vertex b i ≠ P.vertex b j :=
        fun h => hij ((P.vertex b).injective h)
      have ht : ω (pairEdge (P.vertex b i) (P.vertex b j) hne) = true :=
        (graphOfBits_adj ω _ _ hne).mp hxy
      have hf := congrFun hz (pairEdge i j hij)
      change ω (mapEdge (P.vertex b) (pairEdge i j hij)) = false at hf
      rw [mapEdge_pair] at hf
      rw [hf] at ht
      contradiction

set_option maxHeartbeats 1000000 in
/-- One-set upper bound, with the independence assertion fully discharged. -/
lemma fraction_noIndependent_le {V : Type u} [Fintype V] [DecidableEq V]
    (U : Finset V) (m t : ℕ) (hcap : m * (m * t) ≤ U.card) :
    fraction (fun ω : Edge V → Bool => ¬HasIndependent (graphOfBits ω) U m) ≤
      (1 - (1 / 2 : ℝ) ^ (m.choose 2)) ^ (t * t) := by
  classical
  obtain ⟨P, hP⟩ := exists_grid_packing U m t hcap
  calc
    fraction (fun ω : Edge V → Bool => ¬HasIndependent (graphOfBits ω) U m) ≤
        fraction (AvoidZero P.edgeEmbedding) := by
      apply fraction_mono
      intro ω hω
      exact noIndependent_implies_avoidZero U P hP ω hω
    _ = (1 - (1 / 2 : ℝ) ^ (m.choose 2)) ^ (t * t) := by
      have hh := avoidZero_fraction P.edgeEmbedding
      simp only [card_edge, Fintype.card_fin, Fintype.card_prod] at hh
      convert hh using 1
      simp only [fraction, Fintype.card_eq_nat_card]

/-- Finite-n bound for the uniform distribution on ALL labelled simple graphs. -/
theorem badRich_fraction_le (n m s t : ℕ) (hcap : m * (m * t) ≤ s) :
    fraction (fun G : SimpleGraph (Fin n) => ¬Rich G m s) ≤
      (2 : ℝ) ^ n * (1 - (1 / 2 : ℝ) ^ (m.choose 2)) ^ (t * t) := by
  classical
  let a : ℝ := (1 - (1 / 2 : ℝ) ^ (m.choose 2)) ^ (t * t)
  have ha : 0 ≤ a := by
    apply pow_nonneg
    apply sub_nonneg.mpr
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hone (U : Finset (Fin n)) :
      fraction (fun ω : Edge (Fin n) → Bool =>
        s ≤ U.card ∧ ¬HasIndependent (graphOfBits ω) U m) ≤ a := by
    by_cases hU : s ≤ U.card
    · calc
        fraction (fun ω : Edge (Fin n) → Bool =>
            s ≤ U.card ∧ ¬HasIndependent (graphOfBits ω) U m) ≤
            fraction (fun ω : Edge (Fin n) → Bool =>
              ¬HasIndependent (graphOfBits ω) U m) :=
          fraction_mono (fun _ h => h.2)
        _ ≤ a := fraction_noIndependent_le U m t (hcap.trans hU)
    · simpa [hU, fraction] using ha
  have hbits : fraction (fun ω : Edge (Fin n) → Bool =>
      ¬Rich (graphOfBits ω) m s) ≤ (2 : ℝ) ^ n * a := by
    have he : (fun ω : Edge (Fin n) → Bool => ¬Rich (graphOfBits ω) m s) =
        (fun ω => ∃ U : Finset (Fin n),
          s ≤ U.card ∧ ¬HasIndependent (graphOfBits ω) U m) := by
      funext ω
      apply propext
      simp only [Rich, not_forall, _root_.not_imp]
      constructor <;> rintro ⟨U, hU, hbad⟩ <;> exact ⟨U, hU, hbad⟩
    rw [he]
    calc
      fraction (fun ω : Edge (Fin n) → Bool =>
          ∃ U : Finset (Fin n), s ≤ U.card ∧
            ¬HasIndependent (graphOfBits ω) U m) ≤
          ∑ U : Finset (Fin n), fraction (fun ω : Edge (Fin n) → Bool =>
            s ≤ U.card ∧ ¬HasIndependent (graphOfBits ω) U m) :=
        fraction_exists_le _
      _ ≤ ∑ _U : Finset (Fin n), a := by
        apply Finset.sum_le_sum
        intro U _
        exact hone U
      _ = (2 : ℝ) ^ n * a := by
        simp [card_all_finsets]
  have heq := fraction_equiv (bitsGraphEquiv (Fin n))
    (fun G : SimpleGraph (Fin n) => ¬Rich G m s)
  rw [← heq]
  exact hbits

/-- Floor-based version of the finite bound; no lower-size restrictions on n or s. -/
theorem badRich_fraction_le_floor (n m s : ℕ) :
    fraction (fun G : SimpleGraph (Fin n) => ¬Rich G m s) ≤
      (2 : ℝ) ^ n * (1 - (1 / 2 : ℝ) ^ (m.choose 2)) ^
        ((s / (m * m)) * (s / (m * m))) := by
  apply badRich_fraction_le
  calc
    m * (m * (s / (m * m))) = (m * m) * (s / (m * m)) := by ring
    _ ≤ s := Nat.mul_div_le s (m * m)

/-! ## 6. An elementary geometric domination, avoiding logarithmic-scale estimates -/

lemma real_pow_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    x ^ n ≤ y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hxy hx (pow_nonneg (hx.trans hxy) _)

lemma real_pow_antitone_exponent {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {i j : ℕ} (hij : i ≤ j) : a ^ j ≤ a ^ i := by
  have he : i + (j - i) = j := by omega
  calc
    a ^ j = a ^ i * a ^ (j - i) := by rw [← pow_add, he]
    _ ≤ a ^ i * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ ha0 ha1) (pow_nonneg ha0 _)
    _ = a ^ i := mul_one _

/-- For fixed positive D, (n/D)^2 eventually dominates any fixed multiple of n. -/
lemma quotient_square_eventually (D L : ℕ) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, L * n ≤ (n / D) * (n / D) := by
  refine Filter.eventually_atTop.mpr ⟨D * (2 * D * L + 1), ?_⟩
  intro n hn
  let t := n / D
  have ht : 2 * D * L + 1 ≤ t := by
    apply (Nat.le_div_iff_mul_le hD).mpr
    simpa [Nat.mul_comm] using hn
  have ht1 : 1 ≤ t := by omega
  have hrem : n % D < D := Nat.mod_lt n hD
  have hdecomp : n % D + D * t = n := Nat.mod_add_div n D
  have hDt : D ≤ D * t := by
    simpa using Nat.mul_le_mul_left D ht1
  have hn2 : n ≤ 2 * D * t := by
    nlinarith only [hrem, hdecomp, hDt]
  calc
    L * n ≤ L * (2 * D * t) := Nat.mul_le_mul_left L hn2
    _ = (2 * D * L) * t := by ring
    _ ≤ t * t := Nat.mul_le_mul_right t (by omega)

/-- A quadratic number of independent tests beats the 2^n union bound. -/
theorem two_pow_mul_pow_quotient_square_tendsto_zero
    (D : ℕ) (hD : 0 < D) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ n * a ^ ((n / D) * (n / D)))
      atTop (𝓝 0) := by
  have halim : Tendsto (fun L : ℕ => a ^ L) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1
  have he : ∀ᶠ L : ℕ in atTop, a ^ L < (1 / 4 : ℝ) :=
    halim (gt_mem_nhds (by norm_num))
  obtain ⟨L, hL⟩ := he.exists
  have hupper : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ n * a ^ ((n / D) * (n / D)) ≤ (1 / 2 : ℝ) ^ n := by
    filter_upwards [quotient_square_eventually D L hD] with n hn
    calc
      (2 : ℝ) ^ n * a ^ ((n / D) * (n / D)) ≤
          (2 : ℝ) ^ n * a ^ (L * n) := by
        exact mul_le_mul_of_nonneg_left
          (real_pow_antitone_exponent ha0 ha1.le hn) (by positivity)
      _ = ((2 : ℝ) * a ^ L) ^ n := by rw [pow_mul, mul_pow]
      _ ≤ (1 / 2 : ℝ) ^ n := by
        apply real_pow_mono (mul_nonneg (by norm_num) (pow_nonneg ha0 _))
        linarith only [hL]
  apply squeeze_zero' _ hupper
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
  exact Filter.Eventually.of_forall (fun n =>
    mul_nonneg (by positivity) (pow_nonneg ha0 _))

/-- MAIN UNCONDITIONAL RANDOM-GRAPH THEOREM.

For every fixed positive m,d, the fraction of labelled graphs having a set of
at least floor(n/d)+1 vertices but no independent m-set tends to zero.
There is no unproved pseudorandomness or packing hypothesis in this statement. -/
theorem badRich_tendsto_zero (m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    Tendsto (fun n : ℕ =>
      fraction (fun G : SimpleGraph (Fin n) => ¬Rich G m (n / d + 1)))
      atTop (𝓝 0) := by
  classical
  let D : ℕ := d * (m * m)
  let a : ℝ := 1 - (1 / 2 : ℝ) ^ (m.choose 2)
  have hD : 0 < D := Nat.mul_pos hd (Nat.mul_pos hm hm)
  have ha0 : 0 ≤ a := by
    apply sub_nonneg.mpr
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have ha1 : a < 1 := by
    have hp : 0 < (1 / 2 : ℝ) ^ (m.choose 2) := pow_pos (by norm_num) _
    dsimp [a]
    linarith
  have hbound (n : ℕ) :
      fraction (fun G : SimpleGraph (Fin n) => ¬Rich G m (n / d + 1)) ≤
        (2 : ℝ) ^ n * a ^ ((n / D) * (n / D)) := by
    apply badRich_fraction_le
    have hmul : (m * (m * (n / D))) * d ≤ n := by
      calc
        (m * (m * (n / D))) * d = D * (n / D) := by dsimp [D]; ring
        _ ≤ n := Nat.mul_div_le n D
    have hc : m * (m * (n / D)) ≤ n / d :=
      (Nat.le_div_iff_mul_le hd).mpr hmul
    omega
  exact squeeze_zero'
    (Filter.Eventually.of_forall (fun n => fraction_nonneg _))
    (Filter.Eventually.of_forall hbound)
    (two_pow_mul_pow_quotient_square_tendsto_zero D hD a ha0 ha1)

/-! ## 7. Final o(n) assembly: the ONLY input is the separate Hall corollary -/

/-- For any epsilon, choose a fixed m so the Hall output is eventually ≤ epsilon*n. -/
lemma choose_m_for_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, m ≤ n →
      ((2 * (n / m + 1) : ℕ) : ℝ) ≤ ε * (n : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max (4 / ε) 1)
  have hm1 : (1 : ℝ) < m := (le_max_right _ _).trans_lt hm
  have hm0 : 0 < m := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hm1)
  have hm4 : (4 / ε : ℝ) < m := (le_max_left _ _).trans_lt hm
  have hem : (4 : ℝ) < ε * m := by
    have h := (div_lt_iff₀ hε).mp hm4
    nlinarith only [h]
  refine ⟨m, hm0, ?_⟩
  intro n hn
  have hq : 1 ≤ n / m := by
    apply (Nat.le_div_iff_mul_le hm0).mpr
    simpa using hn
  have hqR : (1 : ℝ) ≤ ((n / m : ℕ) : ℝ) := by exact_mod_cast hq
  have hmn : (m : ℝ) * ((n / m : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.mul_div_le n m
  have hscale := mul_le_mul_of_nonneg_left hmn hε.le
  have hfour := mul_le_mul_of_nonneg_right hem.le
    (show (0 : ℝ) ≤ ((n / m : ℕ) : ℝ) by positivity)
  push_cast
  nlinarith only [hqR, hscale, hfour]

/-- Assembly adapter, not the independent proof of its Hall hypothesis.

To instantiate with the list chromatic number, the local Hall module supplies:
  Rich G m (n/m+1) -> chi_L G <= 2*(n/m+1).
It obtains this with k=s=n/m+1 and n <= k*m.  No assertion about ordinary
chromatic number is used.  The random module itself has no remaining hypothesis.
-/
theorem assembly_from_localHallBound
    (C : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ)
    (hHall : ∀ (m : ℕ), 0 < m → ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      Rich G m (n / m + 1) → C n G ≤ 2 * (n / m + 1))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      fraction (fun G : SimpleGraph (Fin n) => ε * (n : ℝ) < (C n G : ℝ)))
      atTop (𝓝 0) := by
  classical
  obtain ⟨m, hm, hsize⟩ := choose_m_for_epsilon ε hε
  have hupper : ∀ᶠ n : ℕ in atTop,
      fraction (fun G : SimpleGraph (Fin n) => ε * (n : ℝ) < (C n G : ℝ)) ≤
        fraction (fun G : SimpleGraph (Fin n) => ¬Rich G m (n / m + 1)) := by
    refine Filter.eventually_atTop.mpr ⟨m, ?_⟩
    intro n hn
    apply fraction_mono
    intro G hbad hRich
    have hc : (C n G : ℝ) ≤ ((2 * (n / m + 1) : ℕ) : ℝ) := by
      exact_mod_cast hHall m hm n G hRich
    exact (not_lt_of_ge (hc.trans (hsize n hn))) hbad
  exact squeeze_zero'
    (Filter.Eventually.of_forall (fun n => fraction_nonneg _))
    hupper (badRich_tendsto_zero m m hm hm)


/-- The capacity inequality used when k=s=floor(n/m)+1. -/
lemma vertex_count_le_hall_blocks (n m : ℕ) (hm : 0 < m) :
    n ≤ (n / m + 1) * m := by
  have hr := Nat.mod_lt n hm
  have hd := Nat.mod_add_div n m
  nlinarith only [hr, hd]

/-- An adapter matching the numerical conclusion of the local Hall theorem.
The Hall theorem is an explicit input, not reimplemented in this file. -/
theorem assembly_from_localHall
    (C : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ)
    (hHall : ∀ (m s k n : ℕ) (G : SimpleGraph (Fin n)),
      0 < m → 0 < s → n ≤ k * m → Rich G m s → C n G ≤ k + s)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      fraction (fun G : SimpleGraph (Fin n) => ε * (n : ℝ) < (C n G : ℝ)))
      atTop (𝓝 0) := by
  apply assembly_from_localHallBound C _ ε hε
  intro m hm n G hRich
  have h := hHall m (n / m + 1) (n / m + 1) n G hm (Nat.succ_pos _)
    (vertex_count_le_hall_blocks n m hm) hRich
  simpa [two_mul] using h

end JSP656
