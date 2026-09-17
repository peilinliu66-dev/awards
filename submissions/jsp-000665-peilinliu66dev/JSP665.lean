import Mathlib

/-!
# JSP-000665 / Erdos 808: a counterexample to graph-restricted sum-product expansion

Mathematical attribution: N. Alon, I. Z. Ruzsa, J. Solymosi,
"Sums, products, and ratios along the edges of a graph", Publ. Mat. 64 (2020),
143--155; author preprint, Theorem 3, page 2.

This file uses a deliberately nonoptimal, integer-interval version of the
reciprocal-factor construction. It needs neither a prime-counting estimate nor
an asymptotic theorem. A finite simple undirected graph is encoded canonically
by a finite set of pairs (a,b) with a < b. Thus edges are counted once.

Target toolchain: Lean 4.33.1; Mathlib commit
0df444a360eaa60ab8c11dca51a86af692955474.
The complete arbitrary-size counterexample and both conjecture negations
have been checked against this pinned environment. This package formalizes
the attributed mathematics and does not claim a new mathematical result.
-/

namespace JSP665

open Finset

/-- Canonically oriented edges of a finite simple undirected graph on `A`. -/
def GraphOn (A : Finset ℕ) (E : Finset (ℕ × ℕ)) : Prop :=
  ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 < e.2

/-- Values of the sum along the (once-counted) edges. -/
def sumValues (E : Finset (ℕ × ℕ)) : Finset ℕ :=
  E.image (fun e => e.1 + e.2)

/-- Values of the product along the (once-counted) edges. -/
def productValues (E : Finset (ℕ × ℕ)) : Finset ℕ :=
  E.image (fun e => e.1 * e.2)

/-- The max formulation of the original graph-restricted conjecture. -/
def OriginalConjecture : Prop :=
  ∀ c ε : ℝ, 0 < c → 0 < ε →
    ∃ N : ℕ, ∀ (A : Finset ℕ) (E : Finset (ℕ × ℕ)),
      N ≤ A.card → (∀ a ∈ A, 0 < a) → GraphOn A E →
      (A.card : ℝ) ^ (1 + c) ≤ (E.card : ℝ) →
      (A.card : ℝ) ^ (1 + c - ε) ≤
        max ((sumValues E).card : ℝ) ((productValues E).card : ℝ)

/-- The sum formulation appearing in ARS, Conjecture 2. -/
def OriginalSumConjecture : Prop :=
  ∀ c ε : ℝ, 0 < c → 0 < ε →
    ∃ N : ℕ, ∀ (A : Finset ℕ) (E : Finset (ℕ × ℕ)),
      N ≤ A.card → (∀ a ∈ A, 0 < a) → GraphOn A E →
      (A.card : ℝ) ^ (1 + c) ≤ (E.card : ℝ) →
      (A.card : ℝ) ^ (1 + c - ε) ≤
        ((sumValues E).card : ℝ) + ((productValues E).card : ℝ)

section Construction

/-- A common multiple of all denominators 2,...,g+1. -/
def scale (g : ℕ) : ℕ := (g + 1).factorial

/-- A translation large enough to separate the different reciprocal slopes. -/
def base (g h : ℕ) : ℕ := (g + 2) * h

def leftLabel (g h i u : ℕ) : ℕ :=
  scale g * ((i + 2) * (base g h + u))

def rightLabel (g h i u : ℕ) : ℕ :=
  (scale g / (i + 2)) * (base g h + u)

def vertexParameters (g h : ℕ) : Finset (ℕ × ℕ) :=
  range g ×ˢ range h

def leftVertices (g h : ℕ) : Finset ℕ :=
  (vertexParameters g h).image (fun p => leftLabel g h p.1 p.2)

def rightVertices (g h : ℕ) : Finset ℕ :=
  (vertexParameters g h).image (fun p => rightLabel g h p.1 p.2)

def vertices (g h : ℕ) : Finset ℕ :=
  leftVertices g h ∪ rightVertices g h

def edgeParameters (g h : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  range g ×ˢ (range h ×ˢ range h)

/-- One complete bipartite component for each index `i < g`. -/
def edges (g h : ℕ) : Finset (ℕ × ℕ) :=
  (edgeParameters g h).image
    (fun p => (rightLabel g h p.1 p.2.1, leftLabel g h p.1 p.2.2))

lemma mem_vertexParameters {g h : ℕ} {p : ℕ × ℕ} :
    p ∈ vertexParameters g h ↔ p.1 < g ∧ p.2 < h := by
  simp [vertexParameters]

lemma mem_edgeParameters {g h : ℕ} {p : ℕ × (ℕ × ℕ)} :
    p ∈ edgeParameters g h ↔ p.1 < g ∧ p.2.1 < h ∧ p.2.2 < h := by
  simp [edgeParameters]

lemma scale_pos (g : ℕ) : 0 < scale g := Nat.factorial_pos _

lemma base_pos {g h : ℕ} (hh : 0 < h) : 0 < base g h := by
  exact Nat.mul_pos (by omega) hh

lemma h_le_base (g h : ℕ) : h ≤ base g h := by
  have hg : 1 ≤ g + 2 := by omega
  simpa only [one_mul, base] using Nat.mul_le_mul_right h hg

lemma quotient_mul {g i : ℕ} (hi : i < g) :
    (scale g / (i + 2)) * (i + 2) = scale g := by
  apply Nat.div_mul_cancel
  exact Nat.dvd_factorial (by omega) (by omega)

lemma quotient_pos {g i : ℕ} (hi : i < g) :
    0 < scale g / (i + 2) := by
  by_contra hn
  have hz : scale g / (i + 2) = 0 := Nat.eq_zero_of_not_pos hn
  have hm := quotient_mul hi
  rw [hz, zero_mul] at hm
  have hp := scale_pos g
  omega

lemma leftLabel_pos {g h i u : ℕ} (hh : 0 < h) :
    0 < leftLabel g h i u := by
  apply Nat.mul_pos (scale_pos g)
  apply Nat.mul_pos (by omega)
  have := base_pos (g := g) hh
  omega

lemma rightLabel_pos {g h i u : ℕ} (hh : 0 < h) (hi : i < g) :
    0 < rightLabel g h i u := by
  apply Nat.mul_pos (quotient_pos hi)
  have := base_pos (g := g) hh
  omega

/-- Nonoverlap of the intervals with distinct integer slopes. -/
lemma core_order {g h i j u v : ℕ} (hh : 0 < h) (hi : i < g)
    (hij : i < j) (hu : u < h) :
    (i + 2) * (base g h + u) < (j + 2) * (base g h + v) := by
  have hi2 : i + 2 ≤ g + 1 := by omega
  have hiu : (i + 2) * u < base g h := by
    calc
      (i + 2) * u < (i + 2) * h :=
        Nat.mul_lt_mul_of_pos_left hu (by omega)
      _ ≤ (g + 1) * h := Nat.mul_le_mul_right h hi2
      _ < base g h := by dsimp [base]; nlinarith
  have hstep : (i + 3) * base g h ≤ (j + 2) * base g h :=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith [Nat.zero_le ((j + 2) * v)]

lemma core_injective {g h i j u v : ℕ} (hh : 0 < h)
    (hi : i < g) (hj : j < g) (hu : u < h) (hv : v < h)
    (heq : (i + 2) * (base g h + u) = (j + 2) * (base g h + v)) :
    i = j ∧ u = v := by
  have hij : i = j := by
    rcases lt_trichotomy i j with hij | hij | hij
    · have hc := core_order (v := v) hh hi hij hu
      omega
    · exact hij
    · have hc := core_order (v := u) hh hj hij hv
      omega
  subst j
  have huv : base g h + u = base g h + v :=
    Nat.eq_of_mul_eq_mul_left (by omega) heq
  exact ⟨rfl, by omega⟩

lemma leftLabel_injective {g h i j u v : ℕ} (hh : 0 < h)
    (hi : i < g) (hj : j < g) (hu : u < h) (hv : v < h)
    (heq : leftLabel g h i u = leftLabel g h j v) :
    i = j ∧ u = v := by
  have hc : (i + 2) * (base g h + u) = (j + 2) * (base g h + v) :=
    Nat.eq_of_mul_eq_mul_left (scale_pos g) heq
  exact core_injective hh hi hj hu hv hc

lemma right_mul_index {g h i u : ℕ} (hi : i < g) :
    rightLabel g h i u * (i + 2) = scale g * (base g h + u) := by
  calc
    rightLabel g h i u * (i + 2) =
        ((scale g / (i + 2)) * (i + 2)) * (base g h + u) := by
          dsimp [rightLabel]; ring
    _ = scale g * (base g h + u) := by rw [quotient_mul hi]

lemma rightLabel_injective {g h i j u v : ℕ} (hh : 0 < h)
    (hi : i < g) (hj : j < g) (hu : u < h) (hv : v < h)
    (heq : rightLabel g h i u = rightLabel g h j v) :
    i = j ∧ u = v := by
  have hc : scale g * ((j + 2) * (base g h + u)) =
      scale g * ((i + 2) * (base g h + v)) := by
    calc
      scale g * ((j + 2) * (base g h + u)) =
          (rightLabel g h i u * (i + 2)) * (j + 2) := by
            rw [right_mul_index hi]; ring
      _ = (rightLabel g h j v * (j + 2)) * (i + 2) := by rw [heq]; ring
      _ = scale g * ((i + 2) * (base g h + v)) := by
            rw [right_mul_index hj]; ring
  have hc' : (j + 2) * (base g h + u) = (i + 2) * (base g h + v) :=
    Nat.eq_of_mul_eq_mul_left (scale_pos g) hc
  obtain ⟨hji, huv⟩ := core_injective hh hj hi hu hv hc'
  exact ⟨hji.symm, huv⟩

/-- All right labels are strictly smaller than all left labels. -/
lemma right_lt_left {g h i j u v : ℕ} (hh : 0 < h) (hu : u < h) :
    rightLabel g h i u < leftLabel g h j v := by
  have huB : u < base g h := lt_of_lt_of_le hu (h_le_base g h)
  have hlast : 2 * base g h ≤ (j + 2) * (base g h + v) := by
    nlinarith [Nat.zero_le (j * base g h), Nat.zero_le ((j + 2) * v)]
  calc
    rightLabel g h i u ≤ scale g * (base g h + u) :=
      Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
    _ < scale g * (2 * base g h) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (scale_pos g)
    _ ≤ leftLabel g h j v := Nat.mul_le_mul_left _ hlast

lemma leftVertices_card {g h : ℕ} (hh : 0 < h) :
    (leftVertices g h).card = g * h := by
  have hinj : Set.InjOn (fun p : ℕ × ℕ => leftLabel g h p.1 p.2)
      (vertexParameters g h : Set (ℕ × ℕ)) := by
    intro p hp q hq heq
    obtain ⟨hp1, hp2⟩ := mem_vertexParameters.mp hp
    obtain ⟨hq1, hq2⟩ := mem_vertexParameters.mp hq
    obtain ⟨h1, h2⟩ := leftLabel_injective hh hp1 hq1 hp2 hq2 heq
    exact Prod.ext h1 h2
  calc
    (leftVertices g h).card = (vertexParameters g h).card := by
      exact Finset.card_image_iff.mpr hinj
    _ = g * h := by simp [vertexParameters]

lemma rightVertices_card {g h : ℕ} (hh : 0 < h) :
    (rightVertices g h).card = g * h := by
  have hinj : Set.InjOn (fun p : ℕ × ℕ => rightLabel g h p.1 p.2)
      (vertexParameters g h : Set (ℕ × ℕ)) := by
    intro p hp q hq heq
    obtain ⟨hp1, hp2⟩ := mem_vertexParameters.mp hp
    obtain ⟨hq1, hq2⟩ := mem_vertexParameters.mp hq
    obtain ⟨h1, h2⟩ := rightLabel_injective hh hp1 hq1 hp2 hq2 heq
    exact Prod.ext h1 h2
  calc
    (rightVertices g h).card = (vertexParameters g h).card := by
      exact Finset.card_image_iff.mpr hinj
    _ = g * h := by simp [vertexParameters]

lemma sides_disjoint {g h : ℕ} (hh : 0 < h) :
    Disjoint (leftVertices g h) (rightVertices g h) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨p, hp, hpEq⟩ := Finset.mem_image.mp ha
  obtain ⟨q, hq, hqEq⟩ := Finset.mem_image.mp hb
  have hq2 := (mem_vertexParameters.mp hq).2
  have hc := right_lt_left (g := g) (i := q.1) (j := p.1) (v := p.2) hh hq2
  omega

lemma vertices_card {g h : ℕ} (hh : 0 < h) :
    (vertices g h).card = 2 * g * h := by
  rw [vertices, Finset.card_union_of_disjoint (sides_disjoint hh),
    leftVertices_card hh, rightVertices_card hh]
  ring

lemma vertices_positive {g h : ℕ} (hh : 0 < h) :
    ∀ a ∈ vertices g h, 0 < a := by
  intro a ha
  rcases Finset.mem_union.mp ha with ha | ha
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact leftLabel_pos hh
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact rightLabel_pos hh (mem_vertexParameters.mp hp).1

lemma edges_card {g h : ℕ} (hh : 0 < h) :
    (edges g h).card = g * h ^ 2 := by
  have hinj : Set.InjOn
      (fun p : ℕ × (ℕ × ℕ) =>
        (rightLabel g h p.1 p.2.1, leftLabel g h p.1 p.2.2))
      (edgeParameters g h : Set (ℕ × (ℕ × ℕ))) := by
    intro p hp q hq heq
    obtain ⟨hp1, hp2, hp3⟩ := mem_edgeParameters.mp hp
    obtain ⟨hq1, hq2, hq3⟩ := mem_edgeParameters.mp hq
    have heq1 := congrArg Prod.fst heq
    have heq2 := congrArg Prod.snd heq
    obtain ⟨hi, hu⟩ := rightLabel_injective hh hp1 hq1 hp2 hq2 heq1
    obtain ⟨_, hv⟩ := leftLabel_injective hh hp1 hq1 hp3 hq3 heq2
    exact Prod.ext hi (Prod.ext hu hv)
  calc
    (edges g h).card = (edgeParameters g h).card := by
      exact Finset.card_image_iff.mpr hinj
    _ = g * h ^ 2 := by simp [edgeParameters, pow_two]

lemma edges_graphOn {g h : ℕ} (hh : 0 < h) :
    GraphOn (vertices g h) (edges g h) := by
  intro e he
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hi, hu, hv⟩ := mem_edgeParameters.mp hp
  refine ⟨?_, ?_, right_lt_left hh hu⟩
  · apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr ⟨(p.1, p.2.1), mem_vertexParameters.mpr ⟨hi, hu⟩, rfl⟩
  · apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr ⟨(p.1, p.2.2), mem_vertexParameters.mpr ⟨hi, hv⟩, rfl⟩

lemma product_formula {g h i u v : ℕ} (hi : i < g) :
    rightLabel g h i u * leftLabel g h i v =
      scale g ^ 2 * (base g h + u) * (base g h + v) := by
  calc
    rightLabel g h i u * leftLabel g h i v =
        ((scale g / (i + 2)) * (i + 2)) * scale g *
          (base g h + u) * (base g h + v) := by
            dsimp [rightLabel, leftLabel]; ring
    _ = scale g ^ 2 * (base g h + u) * (base g h + v) := by
          rw [quotient_mul hi]; ring

lemma sum_formula {g h i u v : ℕ} (hi : i < g) :
    rightLabel g h i u + leftLabel g h i v =
      (scale g / (i + 2)) *
        (((i + 2) ^ 2 + 1) * base g h + ((i + 2) ^ 2 * v + u)) := by
  calc
    rightLabel g h i u + leftLabel g h i v =
        (scale g / (i + 2)) * (base g h + u) +
          (((scale g / (i + 2)) * (i + 2)) *
            ((i + 2) * (base g h + v))) := by
              rw [quotient_mul hi]; rfl
    _ = _ := by ring

lemma productValues_card_le (g h : ℕ) :
    (productValues (edges g h)).card ≤ h ^ 2 := by
  let C : Finset ℕ := (range h ×ˢ range h).image
    (fun p : ℕ × ℕ => scale g ^ 2 * (base g h + p.1) * (base g h + p.2))
  have hsub : productValues (edges g h) ⊆ C := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hi, hu, hv⟩ := mem_edgeParameters.mp hp
    refine Finset.mem_image.mpr ⟨(p.2.1, p.2.2), ?_, ?_⟩
    · simp [hu, hv]
    · exact (product_formula hi).symm
  calc
    (productValues (edges g h)).card ≤ C.card := Finset.card_le_card hsub
    _ ≤ (range h ×ˢ range h).card := Finset.card_image_le
    _ = h ^ 2 := by simp [pow_two]

lemma sumValues_card_le_raw (g h : ℕ) :
    (sumValues (edges g h)).card ≤ g * (((g + 1) ^ 2 + 1) * h) := by
  let K := ((g + 1) ^ 2 + 1) * h
  let C : Finset ℕ := (range g ×ˢ range K).image
    (fun p : ℕ × ℕ => (scale g / (p.1 + 2)) *
      (((p.1 + 2) ^ 2 + 1) * base g h + p.2))
  have hsub : sumValues (edges g h) ⊆ C := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hi, hu, hv⟩ := mem_edgeParameters.mp hp
    have hi2 : (p.1 + 2) ^ 2 ≤ (g + 1) ^ 2 := by
      exact Nat.pow_le_pow_left (by omega) 2
    have hr : (p.1 + 2) ^ 2 * p.2.2 + p.2.1 < K := by
      calc
        (p.1 + 2) ^ 2 * p.2.2 + p.2.1 < (p.1 + 2) ^ 2 * h + h :=
          Nat.add_lt_add_of_le_of_lt
            (Nat.mul_le_mul_left _ (Nat.le_of_lt hv)) hu
        _ = ((p.1 + 2) ^ 2 + 1) * h := by ring
        _ ≤ K := Nat.mul_le_mul_right h (Nat.add_le_add_right hi2 1)
    refine Finset.mem_image.mpr ⟨(p.1, (p.1 + 2) ^ 2 * p.2.2 + p.2.1), ?_, ?_⟩
    · simp [hi, hr]
    · exact (sum_formula hi).symm
  calc
    (sumValues (edges g h)).card ≤ C.card := Finset.card_le_card hsub
    _ ≤ (range g ×ˢ range K).card := Finset.card_image_le
    _ = g * (((g + 1) ^ 2 + 1) * h) := by simp [K]

lemma sumValues_card_le {g h : ℕ} (hg : 0 < g) :
    (sumValues (edges g h)).card ≤ 5 * g ^ 3 * h := by
  have hg1 : 1 ≤ g := hg
  have hs : g ≤ g * g := by
    simpa using Nat.mul_le_mul_left g hg1
  have hc : (g + 1) ^ 2 + 1 ≤ 5 * g ^ 2 := by nlinarith
  calc
    (sumValues (edges g h)).card ≤ g * (((g + 1) ^ 2 + 1) * h) :=
      sumValues_card_le_raw g h
    _ ≤ g * ((5 * g ^ 2) * h) :=
      Nat.mul_le_mul_left g (Nat.mul_le_mul_right h hc)
    _ = 5 * g ^ 3 * h := by ring

/-- The complete finite construction: exact vertex/edge counts and both value bounds. -/
theorem finite_construction {g h : ℕ} (hg : 0 < g) (hh : 0 < h) :
    (vertices g h).card = 2 * g * h ∧
    (edges g h).card = g * h ^ 2 ∧
    (∀ a ∈ vertices g h, 0 < a) ∧
    GraphOn (vertices g h) (edges g h) ∧
    (sumValues (edges g h)).card + (productValues (edges g h)).card ≤
      5 * g ^ 3 * h + h ^ 2 := by
  refine ⟨vertices_card hh, edges_card hh, vertices_positive hh, edges_graphOn hh, ?_⟩
  exact Nat.add_le_add (sumValues_card_le hg) (productValues_card_le g h)

end Construction

section Exponents

lemma power16_rpow_13_8 (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (16 : ℕ)) ^ (13 / 8 : ℝ) = x ^ (26 : ℕ) := by
  calc
    (x ^ (16 : ℕ)) ^ (13 / 8 : ℝ) = x ^ ((16 : ℝ) * (13 / 8 : ℝ)) :=
      (Real.rpow_natCast_mul hx 16 (13 / 8)).symm
    _ = x ^ 26 := by norm_num

lemma power16_rpow_25_16 (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (16 : ℕ)) ^ (25 / 16 : ℝ) = x ^ (25 : ℕ) := by
  calc
    (x ^ (16 : ℕ)) ^ (25 / 16 : ℝ) = x ^ ((16 : ℝ) * (25 / 16 : ℝ)) :=
      (Real.rpow_natCast_mul hx 16 (25 / 16)).symm
    _ = x ^ 25 := by norm_num

lemma parameter_edge_bound {t : ℕ} (ht : 0 < t) :
    (2 * t) ^ 26 ≤ (8 * t ^ 4) * (4096 * t ^ 12) ^ 2 := by
  have ht2 : 1 ≤ t ^ 2 := pow_pos ht _
  have hm : 1 ≤ 2 * t ^ 2 := by omega
  calc
    (2 * t) ^ 26 = 67108864 * t ^ 26 := by ring
    _ ≤ (67108864 * t ^ 26) * (2 * t ^ 2) := by
      simpa using Nat.mul_le_mul_left (67108864 * t ^ 26) hm
    _ = (8 * t ^ 4) * (4096 * t ^ 12) ^ 2 := by ring

lemma parameter_value_bound {t : ℕ} (ht : 0 < t) :
    5 * (8 * t ^ 4) ^ 3 * (4096 * t ^ 12) + (4096 * t ^ 12) ^ 2 <
      (2 * t) ^ 25 := by
  have ht1 : 1 ≤ t := ht
  have hpow : 0 < t ^ 24 := pow_pos ht _
  have hstep : t ^ 24 ≤ t ^ 25 := by
    calc
      t ^ 24 = t ^ 24 * 1 := by simp
      _ ≤ t ^ 24 * t := Nat.mul_le_mul_left _ ht1
      _ = t ^ 25 := by ring
  calc
    5 * (8 * t ^ 4) ^ 3 * (4096 * t ^ 12) + (4096 * t ^ 12) ^ 2 =
        27262976 * t ^ 24 := by ring
    _ < 33554432 * t ^ 24 := Nat.mul_lt_mul_of_pos_right (by norm_num) hpow
    _ ≤ 33554432 * t ^ 25 := Nat.mul_le_mul_left _ hstep
    _ = (2 * t) ^ 25 := by ring

lemma parameter_size {t : ℕ} (ht : 0 < t) : t ≤ (2 * t) ^ 16 := by
  have hp : 1 ≤ t ^ 15 := pow_pos ht _
  calc
    t = t * 1 := by simp
    _ ≤ t * t ^ 15 := Nat.mul_le_mul_left _ hp
    _ = t ^ 16 := by ring
    _ ≤ (2 * t) ^ 16 := by gcongr; omega

set_option maxHeartbeats 400000 in
/-- Arbitrarily large, genuine simple graphs violating the conjectured bound.
The fixed parameters are c=5/8 and epsilon=1/16. The sum of the two output
cardinalities is already below the proposed lower bound. -/
theorem arbitrarily_large_counterexamples (N : ℕ) :
    ∃ (A : Finset ℕ) (E : Finset (ℕ × ℕ)),
      N ≤ A.card ∧ (∀ a ∈ A, 0 < a) ∧ GraphOn A E ∧
      (A.card : ℝ) ^ (13 / 8 : ℝ) ≤ (E.card : ℝ) ∧
      ((sumValues E).card : ℝ) + ((productValues E).card : ℝ) <
        (A.card : ℝ) ^ (25 / 16 : ℝ) := by
  let t := N + 1
  let g := 8 * t ^ 4
  let h := 4096 * t ^ 12
  have ht : 0 < t := by dsimp [t]; omega
  have hg : 0 < g := Nat.mul_pos (by norm_num) (pow_pos ht _)
  have hh : 0 < h := Nat.mul_pos (by norm_num) (pow_pos ht _)
  obtain ⟨hn, he, hpos, hgraph, hout⟩ := finite_construction hg hh
  have hn' : (vertices g h).card = (2 * t) ^ 16 := by
    rw [hn]
    dsimp [g, h]
    ring
  have hsize : N ≤ (vertices g h).card := by
    rw [hn']
    exact le_trans (by dsimp [t]; omega) (parameter_size ht)
  have hedge : (2 * t) ^ 26 ≤ (edges g h).card := by
    rw [he]
    exact parameter_edge_bound ht
  have hvalues : (sumValues (edges g h)).card + (productValues (edges g h)).card <
      (2 * t) ^ 25 := lt_of_le_of_lt hout (parameter_value_bound ht)
  have hnR : ((vertices g h).card : ℝ) = (((2 * t : ℕ) : ℝ) ^ 16) := by
    rw [hn']
    exact Nat.cast_pow (2 * t) 16
  refine ⟨vertices g h, edges g h, hsize, hpos, hgraph, ?_, ?_⟩
  · rw [hnR, power16_rpow_13_8 ((2 * t : ℕ) : ℝ) (Nat.cast_nonneg _)]
    simpa only [Nat.cast_pow] using (Nat.cast_le (α := ℝ)).mpr hedge
  · rw [hnR, power16_rpow_25_16 ((2 * t : ℕ) : ℝ) (Nat.cast_nonneg _)]
    simpa only [Nat.cast_add, Nat.cast_pow] using (Nat.cast_lt (α := ℝ)).mpr hvalues

/-- Full negative answer to the max formulation of Erdos problem 808. -/
theorem erdos_808 : ¬ OriginalConjecture := by
  intro hconj
  obtain ⟨N, hN⟩ := hconj (5 / 8) (1 / 16) (by norm_num) (by norm_num)
  obtain ⟨A, E, hsize, hpos, hgraph, hedge, hvalues⟩ :=
    arbitrarily_large_counterexamples N
  have hedge' : (A.card : ℝ) ^ (1 + (5 / 8 : ℝ)) ≤ (E.card : ℝ) := by
    convert hedge using 1 <;> norm_num
  have hc := hN A E hsize hpos hgraph hedge'
  have hc' : (A.card : ℝ) ^ (25 / 16 : ℝ) ≤
      max ((sumValues E).card : ℝ) ((productValues E).card : ℝ) := by
    convert hc using 1 <;> norm_num
  have hm : max ((sumValues E).card : ℝ) ((productValues E).card : ℝ) ≤
      ((sumValues E).card : ℝ) + ((productValues E).card : ℝ) := by
    apply max_le
    · exact le_add_of_nonneg_right (by positivity)
    · exact le_add_of_nonneg_left (by positivity)
  linarith

/-- Full negative answer also to the weaker sum formulation in ARS. -/
theorem erdos_808_sum : ¬ OriginalSumConjecture := by
  intro hconj
  obtain ⟨N, hN⟩ := hconj (5 / 8) (1 / 16) (by norm_num) (by norm_num)
  obtain ⟨A, E, hsize, hpos, hgraph, hedge, hvalues⟩ :=
    arbitrarily_large_counterexamples N
  have hedge' : (A.card : ℝ) ^ (1 + (5 / 8 : ℝ)) ≤ (E.card : ℝ) := by
    convert hedge using 1 <;> norm_num
  have hc := hN A E hsize hpos hgraph hedge'
  have hc' : (A.card : ℝ) ^ (25 / 16 : ℝ) ≤
      ((sumValues E).card : ℝ) + ((productValues E).card : ℝ) := by
    convert hc using 1 <;> norm_num
  linarith

end Exponents

#print axioms JSP665.arbitrarily_large_counterexamples
#print axioms JSP665.erdos_808
#print axioms JSP665.erdos_808_sum

end JSP665
