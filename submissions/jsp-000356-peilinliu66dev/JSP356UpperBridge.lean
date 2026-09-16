import JSP356Finite
import Erdos437Upper

/-!
# From square prefixes to ordered square-product blocks

Target: Lean 4.33.1, Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.

The two imports supply `JSP356.prefixProduct`, `JSP356.squareCuts`,
`JSP356.DensityZeroUpperQuestion`, and the upper-bound interface in
`Erdos437Upper`. None of those declarations is redefined here.

For increasing square-prefix endpoints t[0], ..., t[K-1], the blocks are
  {a in A | a <= t[i] and every earlier endpoint is < a}.
The first block is the first prefix. Each later block is the interval
between two consecutive endpoints. A disjoint-product identity and
`Erdos437Upper.isSquare_right_of_mul` prove that every block product is
square. The endpoint itself witnesses that its block is nonempty.

Main declarations:
* `JSP356.squareCutsOrderedBlocks`: the actual block family;
* `JSP356.nonempty_orderedSquareBlocks_of_squareCuts`: the requested existence;
* `JSP356.densityZeroUpperQuestion`: the original strict density-zero statement.

This file is a bridge only; it does not reprove the analytic upper bound.
Compilation against the two project modules has not been run by the author
of this generated file.
-/

namespace JSP356

noncomputable section

namespace UpperBridge

/-- Split a prefix into the preceding prefix and the intervening interval. -/
private theorem prefixProduct_split (A : Finset ℕ) {s t : ℕ}
    (hst : s ≤ t) :
    prefixProduct A t =
      prefixProduct A s * (A.filter (fun a => s < a ∧ a ≤ t)).prod id := by
  classical
  have hunion :
      A.filter (fun a => a ≤ t) =
        A.filter (fun a => a ≤ s) ∪
          A.filter (fun a => s < a ∧ a ≤ t) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨ha, hat⟩
      by_cases has : a ≤ s
      · exact Or.inl ⟨ha, has⟩
      · exact Or.inr ⟨ha, Nat.lt_of_not_ge has, hat⟩
    · rintro (⟨ha, has⟩ | ⟨ha, _, hat⟩)
      · exact ⟨ha, le_trans has hst⟩
      · exact ⟨ha, hat⟩
  have hdisjoint :
      Disjoint (A.filter (fun a => a ≤ s))
        (A.filter (fun a => s < a ∧ a ≤ t)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have has : a ≤ s := (Finset.mem_filter.mp ha).2
    have hsa : s < a := (Finset.mem_filter.mp hb).2.1
    exact (not_lt_of_ge has) hsa
  change (A.filter (fun a => a ≤ t)).prod id =
    (A.filter (fun a => a ≤ s)).prod id *
      (A.filter (fun a => s < a ∧ a ≤ t)).prod id
  rw [hunion, Finset.prod_union hdisjoint]

/-- Two positive square prefixes have a square-product interval between them. -/
private theorem interval_product_isSquare (A : Finset ℕ)
    (hpos : ∀ a ∈ A, 0 < a) {s t : ℕ} (hst : s ≤ t)
    (hs : IsSquare (prefixProduct A s))
    (ht : IsSquare (prefixProduct A t)) :
    IsSquare ((A.filter (fun a => s < a ∧ a ≤ t)).prod id) := by
  classical
  have hp : 0 < prefixProduct A s := by
    change 0 < (A.filter (fun a => a ≤ s)).prod id
    exact Finset.prod_pos (fun a ha => hpos a (Finset.mem_filter.mp ha).1)
  have hb : 0 < (A.filter (fun a => s < a ∧ a ≤ t)).prod id := by
    exact Finset.prod_pos (fun a ha => hpos a (Finset.mem_filter.mp ha).1)
  apply Erdos437Upper.isSquare_right_of_mul hp hb hs
  rw [← prefixProduct_split A hst]
  exact ht

/-- This predecessor-free definition also works when there are no endpoints. -/
private def cutBlock {K : ℕ} (A : Finset ℕ) (t : Fin K → ℕ)
    (i : Fin K) : Finset ℕ := by
  classical
  exact A.filter (fun a => a ≤ t i ∧ ∀ j : Fin K, j < i → t j < a)

private theorem mem_cutBlock_iff {K : ℕ} (A : Finset ℕ) (t : Fin K → ℕ)
    (i : Fin K) (a : ℕ) :
    a ∈ cutBlock A t i ↔
      a ∈ A ∧ a ≤ t i ∧ ∀ j : Fin K, j < i → t j < a := by
  classical
  simp only [cutBlock, Finset.mem_filter]

/-- At index zero, the block is exactly the whole first prefix. -/
private theorem cutBlock_eq_first {K : ℕ} (A : Finset ℕ) (t : Fin K → ℕ)
    (i : Fin K) (hi : i.val = 0) :
    cutBlock A t i = A.filter (fun a => a ≤ t i) := by
  classical
  ext a
  rw [mem_cutBlock_iff, Finset.mem_filter]
  constructor
  · rintro ⟨ha, hat, _⟩
    exact ⟨ha, hat⟩
  · rintro ⟨ha, hat⟩
    refine ⟨ha, hat, ?_⟩
    intro j hji
    have hjival : j.val < i.val := hji
    omega

/-- At a nonzero index, the block is the interval after the immediate predecessor. -/
private theorem cutBlock_eq_interval {K : ℕ} (A : Finset ℕ) (t : Fin K → ℕ)
    (hmono : StrictMono t) (i j : Fin K) (hji : j.val + 1 = i.val) :
    cutBlock A t i = A.filter (fun a => t j < a ∧ a ≤ t i) := by
  classical
  have hjlt : j < i := by
    change j.val < i.val
    omega
  ext a
  rw [mem_cutBlock_iff, Finset.mem_filter]
  constructor
  · rintro ⟨ha, hat, hprev⟩
    exact ⟨ha, hprev j hjlt, hat⟩
  · rintro ⟨ha, hja, hat⟩
    refine ⟨ha, hat, ?_⟩
    intro l hli
    have hlival : l.val < i.val := hli
    have hlj : l ≤ j := by
      change l.val ≤ j.val
      omega
    exact lt_of_le_of_lt (hmono.monotone hlj) hja

/-- Every block cut out by increasing square-prefix endpoints has square product. -/
private theorem cutBlock_isSquare {K : ℕ} (A : Finset ℕ)
    (hpos : ∀ a ∈ A, 0 < a) (t : Fin K → ℕ) (hmono : StrictMono t)
    (hsq : ∀ i : Fin K, IsSquare (prefixProduct A (t i))) (i : Fin K) :
    IsSquare ((cutBlock A t i).prod id) := by
  classical
  by_cases hi : i.val = 0
  · rw [cutBlock_eq_first A t i hi]
    change IsSquare (prefixProduct A (t i))
    exact hsq i
  · let j : Fin K :=
      ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩
    have hji : j.val + 1 = i.val := by
      dsimp only [j]
      omega
    have hjlt : j < i := by
      change j.val < i.val
      omega
    rw [cutBlock_eq_interval A t hmono i j hji]
    exact interval_product_isSquare A hpos
      (le_of_lt (hmono hjlt)) (hsq j) (hsq i)

end UpperBridge

/--
The original square-prefix set automatically gives exactly one nonempty
ordered square-product block per square cut. No block decomposition is assumed.
-/
def squareCutsOrderedBlocks (N : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) :
    Erdos437Upper.OrderedSquareBlocks N (squareCuts A).card := by
  classical
  let t : Fin ((squareCuts A).card) ↪o ℕ :=
    (squareCuts A).orderEmbOfFin rfl
  have hcuts : ∀ i : Fin ((squareCuts A).card),
      t i ∈ A ∧ IsSquare (prefixProduct A (t i)) := by
    intro i
    have hi : t i ∈ squareCuts A := by
      dsimp only [t]
      exact Finset.orderEmbOfFin_mem (squareCuts A) rfl i
    simpa only [squareCuts, Finset.mem_filter] using hi
  have hpos : ∀ a ∈ A, 0 < a := by
    intro a ha
    have h1 : 1 ≤ a := (Finset.mem_Icc.mp (hA ha)).1
    exact lt_of_lt_of_le Nat.zero_lt_one h1
  refine
    { block := UpperBridge.cutBlock A (fun i => t i)
      nonempty := ?_
      positive := ?_
      bounded := ?_
      ordered := ?_
      square := ?_ }
  · intro i
    refine ⟨t i, ?_⟩
    apply (UpperBridge.mem_cutBlock_iff A (fun i => t i) i (t i)).mpr
    exact ⟨(hcuts i).1, le_rfl, fun j hj => t.strictMono hj⟩
  · intro i a ha
    have haA : a ∈ A :=
      ((UpperBridge.mem_cutBlock_iff A (fun i => t i) i a).mp ha).1
    exact hpos a haA
  · intro i a ha
    have haA : a ∈ A :=
      ((UpperBridge.mem_cutBlock_iff A (fun i => t i) i a).mp ha).1
    exact (Finset.mem_Icc.mp (hA haA)).2
  · intro i j hij a ha b hb
    have hai := (UpperBridge.mem_cutBlock_iff A (fun i => t i) i a).mp ha
    have hbj := (UpperBridge.mem_cutBlock_iff A (fun i => t i) j b).mp hb
    exact lt_of_le_of_lt hai.2.1 (hbj.2.2 i hij)
  · intro i
    exact UpperBridge.cutBlock_isSquare A hpos (fun j => t j)
      t.strictMono (fun j => (hcuts j).2) i

/-- The precise existence statement needed to connect the two project modules. -/
theorem nonempty_orderedSquareBlocks_of_squareCuts (N : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) :
    Nonempty (Erdos437Upper.OrderedSquareBlocks N (squareCuts A).card) :=
  ⟨squareCutsOrderedBlocks N A hA⟩

/--
The uniform non-strict block bound, used at epsilon/2 and with N >= 1,
proves the original strict density-zero upper question.
-/
theorem densityZeroUpperQuestion : DensityZeroUpperQuestion := by
  unfold DensityZeroUpperQuestion
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨N₀, hN₀⟩ := Erdos437Upper.uniform_epsilon_bound (ε / 2) hhalf
  refine ⟨max N₀ 1, ?_⟩
  intro N hN A hA
  have hlarge : N₀ ≤ N := le_trans (le_max_left N₀ 1) hN
  have hNone : 1 ≤ N := le_trans (le_max_right N₀ 1) hN
  have hNposNat : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hNone
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNposNat
  have hbound : ((squareCuts A).card : ℝ) ≤ (ε / 2) * (N : ℝ) :=
    hN₀ N (squareCuts A).card hlarge (squareCutsOrderedBlocks N A hA)
  have hhalflt : ε / 2 < ε := by linarith
  exact lt_of_le_of_lt hbound (mul_lt_mul_of_pos_right hhalflt hNpos)

end

end JSP356
