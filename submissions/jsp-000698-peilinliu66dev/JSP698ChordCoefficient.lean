import Mathlib
import JSP698PolynomialBridge
import JSP698OddTransversal

/-!
# Cycle-plus-triangles: finite chord model and the central coefficient

Mathematical source: F. Petrov, "General Parity Result and
Cycle-plus-Triangles Graphs", arXiv:1512.06205, pp. 1--2;
original cycle-plus-triangles theorem: Fleischner--Stiebitz (1992).

This file directly imports the two already proved local modules:
* `JSP698PolynomialBridge`;
* `JSP698OddTransversal`.

It proves, rather than assumes, the chord-matrix hypotheses and the central
coefficient congruence.  The final colourability theorem has only a concrete
cycle/triangle presentation as its graph hypothesis.  The empty graph is
handled separately.

All chords are pairs of positions in a finite linear order.  No Euclidean
geometry, Laurent polynomials, additional axioms, or native computation are used.
The small `decide` proofs are fixed truth tables over `Fin 3` and `ZMod 2`.

Target: Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
The working source is checked locally against this pinned environment.
-/

open scoped BigOperators

namespace JSP698
namespace PetrovFinite

noncomputable section

set_option maxRecDepth 4096

abbrev Bit := ZMod 2
abbrev Vertex (I : Type*) := I × Fin 3

/-- The next and previous vertices in an oriented triangle. -/
def next3 (j : Fin 3) : Fin 3 := if j = 0 then 1 else if j = 1 then 2 else 0
def prev3 (j : Fin 3) : Fin 3 := if j = 0 then 2 else if j = 1 then 0 else 1

private theorem triangle_indices :
    ∀ j : Fin 3, next3 j ≠ j ∧ prev3 j ≠ j ∧ next3 j ≠ prev3 j := by
  decide

private theorem triangle_adjacent :
    ∀ j k : Fin 3, j ≠ k → next3 j = k ∨ next3 k = j := by
  decide

private theorem bit_cases : ∀ b : Bit, b = 0 ∨ b = 1 := by decide
private theorem bit_add_self : ∀ b : Bit, b + b = 0 := by decide
private theorem bit_eq_of_add_zero : ∀ a b : Bit, a + b = 0 → a = b := by decide
private theorem bit_same_delta : ∀ a b c d : Bit,
    a + b = c + d → a + c = b + d := by decide
private theorem bit_cancel_one : ∀ a : Bit, 1 + a = 1 ↔ a = 0 := by decide
private theorem bit_triangle_cancel : ∀ a b c : Bit,
    (b + c) + (c + a) + (a + b) = 0 := by decide

/-- The sign of choosing the second term of a binomial. -/
def bitSign (b : Bit) : ℤ := if b = 0 then 1 else -1

private theorem bitSign_one_add (b : Bit) : bitSign (1 + b) = -bitSign b := by
  rcases bit_cases b with rfl | rfl <;> norm_num [bitSign, Bit] <;> decide

private theorem bitSign_mod_two (b : Bit) : bitSign b % 2 = 1 := by
  rcases bit_cases b with rfl | rfl <;> norm_num [bitSign, Bit] <;> decide

private theorem bit_endpoint_table : ∀ s j : Fin 3,
    (if next3 s = j then (1 : Bit) else 0) +
      (if prev3 s = j then (1 : Bit) else 0) =
        if j = s then 0 else 1 := by
  decide

/-! ## Finite coefficient expansion, before introducing an order -/

section PolynomialExpansion

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The two labelled edge copies are retained even if the underlying simple
    graph has an edge in both the Hamiltonian cycle and a triangle. -/
def leftEnd (σ : Equiv.Perm (Vertex I)) : Vertex I ⊕ Vertex I → Vertex I :=
  Sum.elim id (fun v => (v.1, next3 v.2))

def rightEnd (σ : Equiv.Perm (Vertex I)) : Vertex I ⊕ Vertex I → Vertex I :=
  Sum.elim σ id

/-- Exponents from a choice of one endpoint of each cycle edge. -/
def cycleExponent (σ : Equiv.Perm (Vertex I)) (q : Vertex I → Bit) :
    Vertex I →₀ ℕ :=
  ∑ v, if q v = 0 then Finsupp.single v 1 else Finsupp.single (σ v) 1

/-- A triangle term has exponent 1 at the omitted vertex, 2 at one endpoint,
    and 0 at the other endpoint of the selected chord. -/
def triangleExponent (i : I) (s : Fin 3) (r : Bit) : Vertex I →₀ ℕ :=
  Finsupp.single (i, s) 1 +
    Finsupp.single (i, if r = 0 then prev3 s else next3 s) 2

def totalExponent (σ : Equiv.Perm (Vertex I))
    (q : Vertex I → Bit) (s : I → Fin 3) (r : I → Bit) : Vertex I →₀ ℕ :=
  cycleExponent σ q + ∑ i, triangleExponent i (s i) (r i)

def termWeight (q : Vertex I → Bit) (r : I → Bit) : ℤ :=
  (∏ v, bitSign (q v)) * ∏ i, bitSign (r i)

def endpointFlag (s : I → Fin 3) (v : Vertex I) : Bit :=
  if v.2 = s v.1 then 0 else 1

def forcedOrientation (s : I → Fin 3) (q : Vertex I → Bit) : I → Bit :=
  fun i => q (i, next3 (s i))

/-- The exact finite balance equations for a central monomial. -/
def BalancedState (σ : Equiv.Perm (Vertex I))
    (s : I → Fin 3) (q : Vertex I → Bit) : Prop :=
  (∀ v, q v + q (σ.symm v) = endpointFlag s v) ∧
    ∀ i, q (i, next3 (s i)) + q (i, prev3 (s i)) = 1

instance balancedStateDecidable (σ : Equiv.Perm (Vertex I))
    (s : I → Fin 3) (q : Vertex I → Bit) : Decidable (BalancedState σ s q) := by
  unfold BalancedState
  infer_instance

def stateWeight (s : I → Fin 3) (q : Vertex I → Bit) : ℤ :=
  termWeight q (forcedOrientation s q)

private def cycleDegree (outgoing incoming : Bit) : ℕ :=
  (if outgoing = 0 then 1 else 0) + (if incoming = 0 then 0 else 1)

private def triangleDegree (s : Fin 3) (r : Bit) (j : Fin 3) : ℕ :=
  (if j = s then 1 else 0) +
    (if j = (if r = 0 then prev3 s else next3 s) then 2 else 0)

set_option maxHeartbeats 0 in
/-- The local balance table, checked in small separate finite cases. -/
private theorem local_balance_table :
    ∀ (s : Fin 3) (r : Bit) (outgoing incoming : Fin 3 → Bit),
      (∀ j, cycleDegree (outgoing j) (incoming j) + triangleDegree s r j = 2) ↔
        ((∀ j, outgoing j + incoming j = if j = s then 0 else 1) ∧
          outgoing (next3 s) + outgoing (prev3 s) = 1 ∧
          r = outgoing (next3 s)) := by
  intro s r outgoing incoming
  fin_cases s
  all_goals rcases bit_cases r with rfl | rfl
  all_goals rcases bit_cases (outgoing 0) with ho0 | ho0
  all_goals rcases bit_cases (outgoing 1) with ho1 | ho1
  all_goals rcases bit_cases (outgoing 2) with ho2 | ho2
  all_goals rcases bit_cases (incoming 0) with hi0 | hi0
  all_goals rcases bit_cases (incoming 1) with hi1 | hi1
  all_goals rcases bit_cases (incoming 2) with hi2 | hi2
  all_goals norm_num [Fin.forall_fin_succ, cycleDegree, triangleDegree,
    next3, prev3, ho0, ho1, ho2, hi0, hi1, hi2] <;> decide

private theorem sum_bit {A : Type*} [AddCommMonoid A] (f : Bit → A) :
    ∑ b, f b = f 0 + f 1 := by
  change (∑ b : Fin 2, f b) = _
  exact Fin.sum_univ_two f

private theorem cycle_factor_expansion
    (σ : Equiv.Perm (Vertex I)) (v : Vertex I) :
    (MvPolynomial.X v - MvPolynomial.X (σ v) : MvPolynomial (Vertex I) ℤ) =
      ∑ b : Bit, MvPolynomial.monomial
        (if b = 0 then Finsupp.single v 1 else Finsupp.single (σ v) 1)
        (bitSign b) := by
  rw [sum_bit]
  simp [bitSign, MvPolynomial.X, sub_eq_add_neg]

private theorem triangle_monomial_as_product (i : I) (s : Fin 3) (r : Bit) :
    (MvPolynomial.monomial (triangleExponent i s r) (bitSign r) :
      MvPolynomial (Vertex I) ℤ) =
      MvPolynomial.C (bitSign r) * MvPolynomial.X (i, s) *
        MvPolynomial.X (i, if r = 0 then prev3 s else next3 s) ^ 2 := by
  rw [triangleExponent, MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_eq_monomial]

private theorem triangle_factor_expansion (i : I) :
    (∏ j : Fin 3,
        (MvPolynomial.X (i, next3 j) - MvPolynomial.X (i, j) :
          MvPolynomial (Vertex I) ℤ)) =
      ∑ s : Fin 3, ∑ r : Bit,
        MvPolynomial.monomial (triangleExponent i s r) (bitSign r) := by
  simp_rw [triangle_monomial_as_product]
  simp_rw [sum_bit]
  simp [Fin.sum_univ_three, Fin.prod_univ_three, bitSign, next3, prev3]
  ring

/-- The complete expansion of the actual edge polynomial, not an assumed
    correspondence between monomials and combinatorial configurations. -/
theorem edgePolynomial_expansion (σ : Equiv.Perm (Vertex I)) :
    edgePolynomial (leftEnd σ) (rightEnd σ) =
      ∑ q : Vertex I → Bit, ∑ s : I → Fin 3, ∑ r : I → Bit,
        MvPolynomial.monomial (totalExponent σ q s r) (termWeight q r) := by
  classical
  have hcycle :
      (∏ v, (MvPolynomial.X v - MvPolynomial.X (σ v) :
        MvPolynomial (Vertex I) ℤ)) =
        ∑ q : Vertex I → Bit,
          MvPolynomial.monomial (cycleExponent σ q) (∏ v, bitSign (q v)) := by
    simp_rw [cycle_factor_expansion]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro q _
    exact (MvPolynomial.monomial_sum_prod Finset.univ
      (fun v => if q v = 0 then Finsupp.single v 1 else Finsupp.single (σ v) 1)
      (fun v => bitSign (q v))).symm
  have htri :
      (∏ i : I, ∏ j : Fin 3,
        (MvPolynomial.X (i, next3 j) - MvPolynomial.X (i, j) :
          MvPolynomial (Vertex I) ℤ)) =
        ∑ s : I → Fin 3, ∑ r : I → Bit,
          MvPolynomial.monomial (∑ i, triangleExponent i (s i) (r i))
            (∏ i, bitSign (r i)) := by
    simp_rw [triangle_factor_expansion]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro r _
    exact (MvPolynomial.monomial_sum_prod Finset.univ
      (fun i => triangleExponent i (s i) (r i)) (fun i => bitSign (r i))).symm
  have htriFull :
      (∏ v : Vertex I,
        (MvPolynomial.X (v.1, next3 v.2) - MvPolynomial.X v :
          MvPolynomial (Vertex I) ℤ)) =
        ∑ s : I → Fin 3, ∑ r : I → Bit,
          MvPolynomial.monomial (∑ i, triangleExponent i (s i) (r i))
            (∏ i, bitSign (r i)) := by
    rw [Fintype.prod_prod_type]
    exact htri
  unfold edgePolynomial
  rw [Fintype.prod_sum_type]
  change (∏ v, (MvPolynomial.X v - MvPolynomial.X (σ v))) *
    (∏ v : Vertex I, (MvPolynomial.X (v.1, next3 v.2) - MvPolynomial.X v)) = _
  rw [hcycle, htriFull]
  simp_rw [Finset.sum_mul, Finset.mul_sum, MvPolynomial.monomial_mul]
  rfl

private theorem cycleExponent_apply (σ : Equiv.Perm (Vertex I))
    (q : Vertex I → Bit) (v : Vertex I) :
    cycleExponent σ q v = cycleDegree (q v) (q (σ.symm v)) := by
  classical
  have hperm : ∀ x, σ x = v ↔ x = σ.symm v := by
    intro x
    constructor
    · intro h
      exact σ.injective (by simpa using h)
    · rintro rfl
      exact σ.apply_symm_apply v
  calc
    cycleExponent σ q v =
        ∑ x : Vertex I,
          ((if x = v then (if q x = 0 then 1 else 0) else 0) +
            (if x = σ.symm v then (if q x = 0 then 0 else 1) else 0)) := by
      simp only [cycleExponent, Finsupp.finset_sum_apply]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : q x = 0 <;>
        simp [hx, Finsupp.single_apply, hperm, eq_comm]
    _ = cycleDegree (q v) (q (σ.symm v)) := by
      rw [Finset.sum_add_distrib]
      simp [cycleDegree]

private theorem triangleExponent_sum_apply
    (s : I → Fin 3) (r : I → Bit) (i : I) (j : Fin 3) :
    (∑ x, triangleExponent x (s x) (r x)) (i, j) = triangleDegree (s i) (r i) j := by
  classical
  rw [Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single i]
  · simp [triangleExponent, triangleDegree, Finsupp.single_apply, eq_comm]
  · intro x _ hxi
    simp [triangleExponent, Finsupp.single_apply, hxi, hxi.symm]
  · simp

private theorem totalExponent_eq_iff (σ : Equiv.Perm (Vertex I))
    (q : Vertex I → Bit) (s : I → Fin 3) (r : I → Bit) :
    totalExponent σ q s r = exponentTwo (Vertex I) ↔
      BalancedState σ s q ∧ r = forcedOrientation s q := by
  classical
  have hlocal : totalExponent σ q s r = exponentTwo (Vertex I) ↔
      ∀ i j, cycleDegree (q (i, j)) (q (σ.symm (i, j))) +
        triangleDegree (s i) (r i) j = 2 := by
    constructor
    · intro h i j
      have h' := congrArg (fun z : Vertex I →₀ ℕ => z (i, j)) h
      simpa only [totalExponent, Finsupp.add_apply, cycleExponent_apply,
        triangleExponent_sum_apply, exponentTwo_apply] using h'
    · intro h
      apply Finsupp.ext
      rintro ⟨i, j⟩
      simpa only [totalExponent, Finsupp.add_apply, cycleExponent_apply,
        triangleExponent_sum_apply, exponentTwo_apply] using h i j
  rw [hlocal]
  constructor
  · intro h
    have hi := fun i => (local_balance_table (s i) (r i)
      (fun j => q (i, j)) (fun j => q (σ.symm (i, j)))).mp (h i)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ⟨i, j⟩
      exact (hi i).1 j
    · intro i
      exact (hi i).2.1
    · funext i
      exact (hi i).2.2
  · rintro ⟨⟨hdelta, hopposite⟩, rfl⟩ i
    apply (local_balance_table (s i) (forcedOrientation s q i)
      (fun j => q (i, j)) (fun j => q (σ.symm (i, j)))).mpr
    exact ⟨fun j => hdelta (i, j), hopposite i, rfl⟩

/-- Central coefficient as a signed sum over binary states and chord choices. -/
theorem centralCoeff_as_states (σ : Equiv.Perm (Vertex I)) :
    (edgePolynomial (leftEnd σ) (rightEnd σ)).coeff (exponentTwo (Vertex I)) =
      ∑ s : I → Fin 3, ∑ q : Vertex I → Bit,
        if BalancedState σ s q then stateWeight s q else 0 := by
  classical
  rw [edgePolynomial_expansion]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    totalExponent_eq_iff]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro q _
  by_cases hs : BalancedState σ s q
  · simp [hs, stateWeight]
  · simp [hs]

end PolynomialExpansion

/-! ## Chords: the adjacency matrix is an F₂ cut pairing -/

/-- The prefix indicator of a position on the linearized circle. -/
def leBit (x y : ℕ) : Bit := if x ≤ y then 1 else 0

/-- A half-open interval indicator, written additively over F₂. -/
def cutBit (a b x : ℕ) : Bit := leBit x a + leBit x b

/-- For disjoint chords this is 1 exactly when their endpoints alternate. -/
def rawCross (a b c d : ℕ) : Bit := cutBit a b c + cutBit a b d

private theorem leBit_swap {a b : ℕ} (hab : a ≠ b) :
    leBit a b + leBit b a = 1 := by
  rcases lt_or_gt_of_ne hab with h | h
  · simp [leBit, le_of_lt h, not_le.mpr h]
  · simp [leBit, le_of_lt h, not_le.mpr h]

private theorem rawCross_self {a b : ℕ} (hab : a ≠ b) :
    rawCross a b a b = 1 := by
  have h := leBit_swap hab
  calc
    rawCross a b a b =
      (leBit a b + leBit b a) + (leBit a a + leBit b b) := by
        unfold rawCross cutBit
        abel
    _ = 1 := by rw [h]; norm_num [leBit, Bit] <;> decide

private theorem rawCross_symm {a b c d : ℕ}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    rawCross a b c d = rawCross c d a b := by
  apply bit_eq_of_add_zero
  calc
    rawCross a b c d + rawCross c d a b =
      (leBit a c + leBit c a) + (leBit a d + leBit d a) +
      (leBit b c + leBit c b) + (leBit b d + leBit d b) := by
        unfold rawCross cutBit
        abel
    _ = 0 := by
      rw [leBit_swap hac, leBit_swap had, leBit_swap hbc, leBit_swap hbd]
      decide

/-- The order-theoretic meaning of the cut pairing; endpoints must be distinct. -/
theorem cutBit_eq_open_interval {a b x : ℕ} (hxa : x ≠ a) (hxb : x ≠ b) :
    cutBit a b x = if min a b < x ∧ x < max a b then 1 else 0 := by
  unfold cutBit leBit
  simp only [min_def, max_def]
  split_ifs <;> norm_num [Bit] at * <;> first | omega | decide

section Chords

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {N : ℕ} (ord : Vertex I ≃ Fin N)

/-- A chord is indexed by its triangle and the vertex omitted from that triangle. -/
def chordLeft (e : Vertex I) : Vertex I := (e.1, next3 e.2)
def chordRight (e : Vertex I) : Vertex I := (e.1, prev3 e.2)

def chordMatrix (e f : Vertex I) : Bit :=
  if e.1 = f.1 then 0 else
    rawCross (ord (chordLeft e)).val (ord (chordRight e)).val
      (ord (chordLeft f)).val (ord (chordRight f)).val

private theorem position_ne {v w : Vertex I} (h : v ≠ w) :
    (ord v).val ≠ (ord w).val := by
  intro he
  apply h
  exact ord.injective (Fin.ext he)

private theorem chord_ends_ne (e : Vertex I) : chordLeft e ≠ chordRight e := by
  intro h
  exact (triangle_indices e.2).2.2 (congrArg Prod.snd h)

theorem chordMatrix_same_block (i : I) (s t : Fin 3) :
    chordMatrix ord (i, s) (i, t) = 0 := by
  simp [chordMatrix]

theorem chordMatrix_symmetric (e f : Vertex I) :
    chordMatrix ord e f = chordMatrix ord f e := by
  classical
  by_cases h : e.1 = f.1
  · simp only [chordMatrix, if_pos h, if_pos h.symm]
  · simp only [chordMatrix, if_neg h, if_neg (Ne.symm h)]
    apply rawCross_symm <;> apply position_ne ord <;>
      intro he <;> have hh := congrArg Prod.fst he <;> exact h hh

/-- Every row has even sum into each other triangle block. -/
theorem chordMatrix_block_sum (e : Vertex I) (j : I) :
    (∑ t : Fin 3, chordMatrix ord e (j, t)) = 0 := by
  classical
  by_cases h : e.1 = j
  · simp [chordMatrix, h]
  · simp only [chordMatrix, if_neg h]
    let a := (ord (chordLeft e)).val
    let b := (ord (chordRight e)).val
    change (∑ t : Fin 3,
      (cutBit a b (ord (j, next3 t)).val +
        cutBit a b (ord (j, prev3 t)).val)) = 0
    simpa [Fin.sum_univ_succ, next3, prev3, add_assoc] using
      bit_triangle_cancel
        (cutBit a b (ord (j, (0 : Fin 3))).val)
        (cutBit a b (ord (j, (1 : Fin 3))).val)
        (cutBit a b (ord (j, (2 : Fin 3))).val)

private theorem three_bits_even_count :
    ∀ f : Fin 3 → Bit, (∑ j, f j) = 0 →
      (Finset.univ.filter (fun j => f j = 1)).card = 0 ∨
      (Finset.univ.filter (fun j => f j = 1)).card = 2 := by
  decide

/-- In ordinary graph language, a chord crosses zero or two edges of a triangle. -/
theorem chord_crosses_zero_or_two (e : Vertex I) (j : I) :
    (Finset.univ.filter (fun t : Fin 3 => chordMatrix ord e (j, t) = 1)).card = 0 ∨
    (Finset.univ.filter (fun t : Fin 3 => chordMatrix ord e (j, t) = 1)).card = 2 := by
  exact three_bits_even_count _ (chordMatrix_block_sum ord e j)

/-- One selected chord from each triangle, and even crossing degree at every chord. -/
def EulerianChoice (s : I → Fin 3) : Prop :=
  ∀ i, (∑ j, chordMatrix ord (i, s i) (j, s j)) = 0

instance eulerianChoiceDecidable (s : I → Fin 3) : Decidable (EulerianChoice ord s) := by
  unfold EulerianChoice
  infer_instance

def eulerianChoices : Finset (I → Fin 3) :=
  Finset.univ.filter (EulerianChoice ord)

end Chords

/-! ## Linearized cycle and its two binary states -/

def finSucc {N : ℕ} (hN : 0 < N) (v : Fin N) : Fin N :=
  if h : v.val + 1 < N then ⟨v.val + 1, h⟩ else ⟨0, hN⟩

def finPred {N : ℕ} (hN : 0 < N) (v : Fin N) : Fin N :=
  if h : v.val = 0 then ⟨N - 1, by omega⟩ else ⟨v.val - 1, by omega⟩

private theorem finPred_succ {N : ℕ} (hN : 0 < N) (v : Fin N) :
    finPred hN (finSucc hN v) = v := by
  apply Fin.ext
  dsimp [finPred, finSucc]
  split_ifs <;> simp_all <;> omega

private theorem finSucc_pred {N : ℕ} (hN : 0 < N) (v : Fin N) :
    finSucc hN (finPred hN v) = v := by
  exact (Function.LeftInverse.rightInverse_of_card_le (finPred_succ hN) le_rfl) v

def finCycle {N : ℕ} (hN : 0 < N) : Equiv.Perm (Fin N) where
  toFun := finSucc hN
  invFun := finPred hN
  left_inv := finPred_succ hN
  right_inv := finSucc_pred hN

section CycleStates

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {N : ℕ} (ord : Vertex I ≃ Fin N) (hN : 0 < N)

def cyclePerm : Equiv.Perm (Vertex I) :=
  (ord.trans (finCycle hN)).trans ord.symm

def lastVertex : Vertex I := ord.symm ⟨N - 1, by omega⟩

def endpointPrefix (s : I → Fin 3) (v : Vertex I) : Bit :=
  ∑ i, (leBit (ord (i, next3 (s i))).val (ord v).val +
    leBit (ord (i, prev3 (s i))).val (ord v).val)

/-- The unique state with prescribed value at the final cycle edge. -/
def canonicalState (s : I → Fin 3) (seed : Bit) (v : Vertex I) : Bit :=
  seed + endpointPrefix ord s v

private theorem canonicalState_last (s : I → Fin 3) (seed : Bit) :
    canonicalState ord s seed (lastVertex ord hN) = seed := by
  have hle : ∀ v : Vertex I, (ord v).val ≤ N - 1 := by
    intro v
    have := (ord v).isLt
    omega
  have htwo : (1 : Bit) + 1 = 0 := by decide
  simp [canonicalState, endpointPrefix, lastVertex, leBit, hle, htwo]

private theorem canonicalState_one (s : I → Fin 3) (v : Vertex I) :
    canonicalState ord s 1 v = 1 + canonicalState ord s 0 v := by
  simp [canonicalState]

include hN in
private theorem canonicalState_ne (s : I → Fin 3) :
    canonicalState ord s 0 ≠ canonicalState ord s 1 := by
  intro h
  have hh := congrArg (fun q : Vertex I → Bit => q (lastVertex ord hN)) h
  have h01 : (0 : Bit) = 1 := by
    simpa only [canonicalState_last] using hh
  exact zero_ne_one h01

/-- One discrete prefix difference.  The wrap-around adds 1 for each endpoint;
    the two endpoints of each chord cancel those additional terms. -/
private theorem leBit_pred_identity {N a b : ℕ}
    (hN : 0 < N) (ha : a < N) (hb : b < N) :
    leBit a b + leBit a (if b = 0 then N - 1 else b - 1) =
      (if a = b then (1 : Bit) else 0) + (if b = 0 then 1 else 0) := by
  unfold leBit
  split_ifs <;> norm_num [Bit] at * <;> first | omega | decide

private theorem position_equal_iff (v w : Vertex I) :
    (ord v).val = (ord w).val ↔ v = w := by
  constructor
  · intro h
    exact ord.injective (Fin.ext h)
  · rintro rfl
    rfl

private theorem endpointPrefix_delta (s : I → Fin 3) (v : Vertex I) :
    endpointPrefix ord s v + endpointPrefix ord s ((cyclePerm ord hN).symm v) =
      endpointFlag s v := by
  classical
  have hpred : (ord ((cyclePerm ord hN).symm v)).val =
      if (ord v).val = 0 then N - 1 else (ord v).val - 1 := by
    simp only [cyclePerm, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply, finCycle]
    dsimp [finPred]
    split_ifs <;> simp
  have hle (w : Vertex I) :
      leBit (ord w).val (ord v).val +
        leBit (ord w).val (ord ((cyclePerm ord hN).symm v)).val =
      (if w = v then (1 : Bit) else 0) +
        (if (ord v).val = 0 then 1 else 0) := by
    rw [hpred]
    simpa only [position_equal_iff] using
      leBit_pred_identity hN (ord w).isLt (ord v).isLt
  calc
    endpointPrefix ord s v + endpointPrefix ord s ((cyclePerm ord hN).symm v) =
        ∑ i, ((if (i, next3 (s i)) = v then (1 : Bit) else 0) +
          (if (i, prev3 (s i)) = v then (1 : Bit) else 0)) := by
      unfold endpointPrefix
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = (leBit (ord (i, next3 (s i))).val (ord v).val +
              leBit (ord (i, next3 (s i))).val
                (ord ((cyclePerm ord hN).symm v)).val) +
            (leBit (ord (i, prev3 (s i))).val (ord v).val +
              leBit (ord (i, prev3 (s i))).val
                (ord ((cyclePerm ord hN).symm v)).val) := by abel
        _ = _ := by
          rw [hle, hle]
          have hw := bit_add_self (if (ord v).val = 0 then (1 : Bit) else 0)
          linear_combination hw
    _ = endpointFlag s v := by
      rcases v with ⟨i, j⟩
      rw [Finset.sum_eq_single i]
      · simpa [endpointFlag] using bit_endpoint_table (s i) j
      · intro x _ hxi
        simp [hxi]
      · simp

/-- The canonical state flips exactly at selected chord endpoints. -/
theorem canonicalState_delta (s : I → Fin 3) (seed : Bit) (v : Vertex I) :
    canonicalState ord s seed v +
      canonicalState ord s seed ((cyclePerm ord hN).symm v) = endpointFlag s v := by
  calc
    _ = (seed + seed) +
        (endpointPrefix ord s v + endpointPrefix ord s ((cyclePerm ord hN).symm v)) := by
      unfold canonicalState
      abel
    _ = _ := by rw [bit_add_self, zero_add, endpointPrefix_delta]

/-- The exact cut-pairing identity: endpoints are opposite precisely when the
    selected chord has even crossing degree. -/
theorem canonicalState_chord_sum (s : I → Fin 3) (seed : Bit) (i : I) :
    canonicalState ord s seed (i, next3 (s i)) +
      canonicalState ord s seed (i, prev3 (s i)) =
        1 + ∑ j, chordMatrix ord (i, s i) (j, s j) := by
  classical
  have hself :
      rawCross (ord (i, next3 (s i))).val (ord (i, prev3 (s i))).val
        (ord (i, next3 (s i))).val (ord (i, prev3 (s i))).val = 1 := by
    apply rawCross_self
    apply position_ne ord
    exact chord_ends_ne (i, s i)
  calc
    _ = ∑ j,
        rawCross (ord (i, next3 (s i))).val (ord (i, prev3 (s i))).val
          (ord (j, next3 (s j))).val (ord (j, prev3 (s j))).val := by
      unfold canonicalState
      calc
        _ = (seed + seed) +
            (endpointPrefix ord s (i, next3 (s i)) +
              endpointPrefix ord s (i, prev3 (s i))) := by abel
        _ = _ := by
          rw [bit_add_self, zero_add]
          unfold endpointPrefix
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          unfold rawCross cutBit
          abel
    _ = ∑ j, ((if j = i then (1 : Bit) else 0) +
        chordMatrix ord (i, s i) (j, s j)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i
      · subst j
        simpa [chordMatrix] using hself
      · simp [chordMatrix, h, Ne.symm h, chordLeft, chordRight]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

private theorem cycle_invariant_constant {A : Type*} (f : Vertex I → A)
    (hf : ∀ v, f v = f ((cyclePerm ord hN).symm v)) :
    ∀ v, f v = f (lastVertex ord hN) := by
  let g : Fin N → A := fun j => f (ord.symm j)
  have hgp : ∀ j, g j = g (finPred hN j) := by
    intro j
    simpa [g, cyclePerm, finCycle] using hf (ord.symm j)
  have hnat : ∀ j (hj : j < N), g ⟨j, hj⟩ = g ⟨N - 1, by omega⟩ := by
    intro j
    induction j with
    | zero =>
        intro hj
        simpa [finPred] using hgp ⟨0, hj⟩
    | succ j ih =>
        intro hj
        have hj' : j < N := by omega
        have hp : finPred hN ⟨j + 1, hj⟩ = ⟨j, hj'⟩ := by
          apply Fin.ext
          simp [finPred]
        rw [hgp, hp]
        exact ih hj'
  intro v
  simpa [g, lastVertex] using hnat (ord v).val (ord v).isLt

/-- Uniqueness of the binary state after its value at one cycle edge is fixed. -/
theorem state_eq_canonical (s : I → Fin 3) (q : Vertex I → Bit)
    (hdelta : ∀ v, q v + q ((cyclePerm ord hN).symm v) = endpointFlag s v) :
    q = canonicalState ord s (q (lastVertex ord hN)) := by
  let z := canonicalState ord s (q (lastVertex ord hN))
  have hz : ∀ v, z v + z ((cyclePerm ord hN).symm v) = endpointFlag s v :=
    canonicalState_delta ord hN s _
  have hinv : ∀ v, q v + z v =
      q ((cyclePerm ord hN).symm v) + z ((cyclePerm ord hN).symm v) := by
    intro v
    apply bit_same_delta
    exact (hdelta v).trans (hz v).symm
  have hconst := cycle_invariant_constant ord hN (fun v => q v + z v) hinv
  funext v
  apply bit_eq_of_add_zero
  calc
    q v + z v = q (lastVertex ord hN) + z (lastVertex ord hN) := hconst v
    _ = 0 := by simp [z, canonicalState_last, bit_add_self]

/-- A chord transversal is Eulerian iff either of its two canonical states is balanced. -/
theorem canonicalState_balanced_iff (s : I → Fin 3) (seed : Bit) :
    BalancedState (cyclePerm ord hN) s (canonicalState ord s seed) ↔
      EulerianChoice ord s := by
  constructor
  · intro h i
    have hi := h.2 i
    rw [canonicalState_chord_sum] at hi
    exact (bit_cancel_one _).mp hi
  · intro h
    refine ⟨canonicalState_delta ord hN s seed, ?_⟩
    intro i
    rw [canonicalState_chord_sum, h i, add_zero]

/-- No additional balanced states exist beyond the two explicitly constructed ones. -/
theorem balancedState_two_choices (s : I → Fin 3) (q : Vertex I → Bit)
    (hq : BalancedState (cyclePerm ord hN) s q) :
    q = canonicalState ord s 0 ∨ q = canonicalState ord s 1 := by
  have heq := state_eq_canonical ord hN s q hq.1
  rcases bit_cases (q (lastVertex ord hN)) with h | h
  · exact Or.inl (by simpa [h] using heq)
  · exact Or.inr (by simpa [h] using heq)

end CycleStates

/-! ## Pairing signs and reducing modulo four -/

private theorem sum_eq_two {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℤ) (a b : A) (hab : a ≠ b)
    (hzero : ∀ x, x ≠ a → x ≠ b → f x = 0) :
    (∑ x, f x) = f a + f b := by
  classical
  have hs : ({a, b} : Finset A) ⊆ Finset.univ := Finset.subset_univ _
  have hsum := Finset.sum_subset hs (by
    intro x _ hx
    exact hzero x
      (fun h => hx (by simp [h]))
      (fun h => hx (by simp [h])))
  simpa [hab] using hsum.symm

private theorem prod_mod_two_eq_one {A : Type*} (s : Finset A) (f : A → ℤ)
    (hf : ∀ x ∈ s, f x % 2 = 1) : (∏ x ∈ s, f x) % 2 = 1 := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | @insert a s ha ih =>
      intro hf
      have ha' := hf a (by simp)
      have hs : ∀ x ∈ s, f x % 2 = 1 := fun x hx => hf x (by simp [hx])
      rw [Finset.prod_insert ha]
      calc
        (f a * ∏ x ∈ s, f x) % 2 =
            (f a % 2 * ((∏ x ∈ s, f x) % 2)) % 2 := Int.mul_emod _ _ _
        _ = 1 := by rw [ha', ih hs]; norm_num

private theorem sum_emod_congr {A : Type*} (s : Finset A) (f g : A → ℤ) (m : ℤ)
    (h : ∀ x ∈ s, f x % m = g x % m) :
    (∑ x ∈ s, f x) % m = (∑ x ∈ s, g x) % m := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | @insert a s ha ih =>
      intro h
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        (f a + ∑ x ∈ s, f x) % m =
            (f a % m + ((∑ x ∈ s, f x) % m)) % m := Int.add_emod _ _ _
        _ = (g a % m + ((∑ x ∈ s, g x) % m)) % m := by
          rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]
        _ = (g a + ∑ x ∈ s, g x) % m := (Int.add_emod _ _ _).symm

section CoefficientPairing

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {N : ℕ} (ord : Vertex I ≃ Fin N) (hN : 0 < N)

private theorem stateWeight_factorization (s : I → Fin 3) (q : Vertex I → Bit) :
    stateWeight s q = ∏ i : I,
      ((∏ j : Fin 3, bitSign (q (i, j))) * bitSign (q (i, next3 (s i)))) := by
  unfold stateWeight termWeight forcedOrientation
  rw [Fintype.prod_prod_type, Finset.prod_mul_distrib]

private theorem stateWeight_pair_equal (s : I → Fin 3) :
    stateWeight s (canonicalState ord s 1) =
      stateWeight s (canonicalState ord s 0) := by
  rw [stateWeight_factorization, stateWeight_factorization]
  apply Finset.prod_congr rfl
  intro i _
  simp_rw [canonicalState_one, bitSign_one_add]
  simp only [Fin.prod_univ_three]
  ring

private theorem stateWeight_mod_two (s : I → Fin 3) (q : Vertex I → Bit) :
    stateWeight s q % 2 = 1 := by
  unfold stateWeight termWeight
  rw [Int.mul_emod,
    prod_mod_two_eq_one Finset.univ _ (fun x _ => bitSign_mod_two _),
    prod_mod_two_eq_one Finset.univ _ (fun x _ => bitSign_mod_two _)]
  norm_num

/-- Exact integer identity, before reducing modulo four. -/
theorem centralCoeff_twice_signed_choices :
    (edgePolynomial (leftEnd (cyclePerm ord hN)) (rightEnd (cyclePerm ord hN))).coeff
        (exponentTwo (Vertex I)) =
      2 * ∑ s : I → Fin 3,
        if EulerianChoice ord s then stateWeight s (canonicalState ord s 0) else 0 := by
  classical
  rw [centralCoeff_as_states, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hsum := sum_eq_two
    (fun q : Vertex I → Bit =>
      if BalancedState (cyclePerm ord hN) s q then stateWeight s q else 0)
    (canonicalState ord s 0) (canonicalState ord s 1)
    (canonicalState_ne ord hN s) (by
      intro q hq0 hq1
      by_cases hq : BalancedState (cyclePerm ord hN) s q
      · rcases balancedState_two_choices ord hN s q hq with h | h
        · exact (hq0 h).elim
        · exact (hq1 h).elim
      · simp [hq])
  rw [hsum]
  simp only [canonicalState_balanced_iff, stateWeight_pair_equal]
  by_cases hs : EulerianChoice ord s <;> simp [hs] <;> ring

/-- The signed choice sum has the same parity as the unsigned Eulerian count. -/
theorem signed_choice_sum_mod_two :
    (∑ s : I → Fin 3,
      if EulerianChoice ord s then stateWeight s (canonicalState ord s 0) else 0) % 2 =
      ((eulerianChoices ord).card : ℤ) % 2 := by
  classical
  have h := sum_emod_congr Finset.univ
    (fun s : I → Fin 3 =>
      if EulerianChoice ord s then stateWeight s (canonicalState ord s 0) else 0)
    (fun s : I → Fin 3 => if EulerianChoice ord s then 1 else 0) 2 (by
      intro s _
      by_cases hs : EulerianChoice ord s
      · simpa [hs] using stateWeight_mod_two s (canonicalState ord s 0)
      · simp [hs])
  have hc : (∑ s : I → Fin 3, if EulerianChoice ord s then (1 : ℤ) else 0) =
      ((eulerianChoices ord).card : ℤ) := by
    calc
      _ = ∑ s ∈ eulerianChoices ord, (1 : ℤ) := by
        simp [eulerianChoices, Finset.sum_filter]
      _ = _ := by simp
  exact h.trans (congrArg (fun z : ℤ => z % 2) hc)

/-- Intermediate arithmetic bridge: an odd Eulerian count gives the coefficient
    congruence. The input is discharged below by the imported local theorem. -/
theorem centralCoeff_mod_four_of_odd_eulerianChoices
    (hodd : Odd (eulerianChoices ord).card) :
    (edgePolynomial (leftEnd (cyclePerm ord hN)) (rightEnd (cyclePerm ord hN))).coeff
        (exponentTwo (Vertex I)) % 4 = 2 := by
  have hc : ((eulerianChoices ord).card : ℤ) % 2 = 1 := by
    rcases hodd with ⟨r, hr⟩
    rw [hr]
    push_cast
    omega
  have hs := (signed_choice_sum_mod_two ord).trans hc
  rw [centralCoeff_twice_signed_choices]
  omega

end CoefficientPairing

/-! ## Direct application of the already compiled odd-transversal theorem -/

section FinalBridge

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {N : ℕ} (ord : Vertex I ≃ Fin N) (hN : 0 < N)

/-- The curried matrix expected by `JSP698.OddTransversal`. -/
def crossingA (i j : I) (a b : Fin 3) : ZMod 2 :=
  chordMatrix ord (i, a) (j, b)

/-- This is the *column* sum in the local core's exact `CrossEven` convention. -/
theorem crossingA_crossEven :
    JSP698.OddTransversal.CrossEven (crossingA ord) := by
  intro i j _hij b
  calc
    (∑ a : Fin 3, crossingA ord i j a b) =
        ∑ a : Fin 3, chordMatrix ord (j, b) (i, a) := by
      apply Finset.sum_congr rfl
      intro a _
      exact chordMatrix_symmetric ord (i, a) (j, b)
    _ = 0 := chordMatrix_block_sum ord (j, b) i

theorem crossingA_symmetric :
    JSP698.OddTransversal.Symmetric (crossingA ord) := by
  intro i j a b
  exact chordMatrix_symmetric ord (i, a) (j, b)

theorem crossingA_diagonal (i : I) (a : Fin 3) :
    crossingA ord i i a a = 0 := by
  exact chordMatrix_same_block ord i a a

/-- No abstract-core hypothesis remains: this invokes the actual compiled theorem. -/
theorem eulerianChoices_odd : Odd (eulerianChoices ord).card := by
  classical
  have hc : Odd (Fintype.card (Fin 3)) := by decide
  have h := JSP698.OddTransversal.odd_eulerian_transversals
    (crossingA ord)
    (crossingA_crossEven ord)
    (crossingA_symmetric ord)
    (crossingA_diagonal ord)
    hc
  exact h

/-- The complete central-coefficient theorem, with no parity or coefficient hypothesis. -/
theorem centralCoeff_mod_four :
    (edgePolynomial (leftEnd (cyclePerm ord hN)) (rightEnd (cyclePerm ord hN))).coeff
        (exponentTwo (Vertex I)) % 4 = 2 := by
  exact centralCoeff_mod_four_of_odd_eulerianChoices ord hN
    (eulerianChoices_odd ord)

/-- All cycle edges and all triangle edges receive different colours. -/
theorem threeColours_in_model :
    ∃ c : Vertex I → Fin 3,
      (∀ v, c v ≠ c (cyclePerm ord hN v)) ∧
      ∀ i j k, j ≠ k → c (i, j) ≠ c (i, k) := by
  have hcount : Fintype.card (Vertex I ⊕ Vertex I) ≤
      2 * Fintype.card (Vertex I) := by
    simp only [Fintype.card_sum]
    omega
  obtain ⟨c, hc⟩ := threeColours_of_centralCoeff_mod_four
    (leftEnd (cyclePerm ord hN)) (rightEnd (cyclePerm ord hN)) hcount
    (centralCoeff_mod_four ord hN)
  refine ⟨c, ?_, ?_⟩
  · intro v
    exact hc (Sum.inl v)
  · intro i j k hjk
    rcases triangle_adjacent j k hjk with h | h
    · have h' := hc (Sum.inr (i, j))
      change c (i, next3 j) ≠ c (i, j) at h'
      rw [h] at h'
      exact h'.symm
    · have h' := hc (Sum.inr (i, k))
      change c (i, next3 k) ≠ c (i, k) at h'
      simpa [h] using h'

end FinalBridge

/-- A directly usable original-graph interface.  `tri` enumerates the disjoint
    triangles covering the vertices, and `ham` enumerates the Hamiltonian cycle.
    Repeated cycle/triangle edges are harmless.  No size restriction is imposed;
    the empty graph is handled separately. -/
theorem threeColours_of_cycle_and_triangle_cover
    {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]
    {N : ℕ} (tri : (I × Fin 3) ≃ W) (ham : W ≃ Fin N)
    (G : SimpleGraph W)
    (hedges : ∀ u v, G.Adj u v →
      ((∃ hN : 0 < N, ham v = finSucc hN (ham u)) ∨
        (∃ hN : 0 < N, ham u = finSucc hN (ham v))) ∨
      ∃ i j k, j ≠ k ∧ tri (i, j) = u ∧ tri (i, k) = v) :
    ∃ c : W → Fin 3, ∀ u v, G.Adj u v → c u ≠ c v := by
  classical
  by_cases hN : 0 < N
  · let ord : Vertex I ≃ Fin N := tri.trans ham
    obtain ⟨c, hcycle, htriangle⟩ := threeColours_in_model ord hN
    refine ⟨fun w => c (tri.symm w), ?_⟩
    intro u v huv
    rcases hedges u v huv with (⟨_, h⟩ | ⟨_, h⟩) | ⟨i, j, k, hjk, rfl, rfl⟩
    · have hp : cyclePerm ord hN (tri.symm u) = tri.symm v := by
        apply (tri.trans ham).injective
        simpa [cyclePerm, finCycle, ord] using h.symm
      simpa [hp] using hcycle (tri.symm u)
    · have hp : cyclePerm ord hN (tri.symm v) = tri.symm u := by
        apply (tri.trans ham).injective
        simpa [cyclePerm, finCycle, ord] using h.symm
      exact (show c (tri.symm v) ≠ c (tri.symm u) by
        simpa [hp] using hcycle (tri.symm v)).symm
    · simpa using htriangle i j k hjk
  · have hN0 : N = 0 := by omega
    refine ⟨fun _ => 0, ?_⟩
    intro u
    have hu := (ham u).isLt
    omega

/-- Standard Mathlib `Colorable` endpoint for an arbitrary finite triangle cover. -/
theorem colorable_of_cycle_and_triangle_cover
    {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]
    {N : ℕ} (tri : (I × Fin 3) ≃ W) (ham : W ≃ Fin N)
    (G : SimpleGraph W)
    (hedges : ∀ u v, G.Adj u v →
      ((∃ hN : 0 < N, ham v = finSucc hN (ham u)) ∨
        (∃ hN : 0 < N, ham u = finSucc hN (ham v))) ∨
      ∃ i j k, j ≠ k ∧ tri (i, j) = u ∧ tri (i, k) = v) :
    G.Colorable 3 := by
  obtain ⟨c, hc⟩ := threeColours_of_cycle_and_triangle_cover tri ham G hedges
  exact ⟨SimpleGraph.Coloring.mk c (fun {u v} huv => hc u v huv)⟩

end
end PetrovFinite

/-- Cyclic adjacency in a Hamiltonian enumeration.  For an empty enumeration
    the relation is empty; no positivity condition is hidden in this definition. -/
def CycleEdge {W : Type*} {N : ℕ} (ham : W ≃ Fin N) (u v : W) : Prop :=
  (∃ hN : 0 < N, ham v = PetrovFinite.finSucc hN (ham u)) ∨
    (∃ hN : 0 < N, ham u = PetrovFinite.finSucc hN (ham v))

/-- Two distinct vertices belonging to one triangle in the given cover. -/
def TriangleEdge {I W : Type*} (tri : (I × Fin 3) ≃ W) (u v : W) : Prop :=
  ∃ i j k, j ≠ k ∧ tri (i, j) = u ∧ tri (i, k) = v

/-- All-scale cycle-plus-triangles theorem.  `hedges` simply says that every
    graph edge is in the displayed cycle or in one of the displayed triangles.
    The conclusion therefore also applies to every subgraph of their union.

    There is no restriction to bounded `n`, no coefficient/parity hypothesis,
    and no abstract transversal-core hypothesis.  `n = 0` is included. -/
theorem erdos_842
    (n : ℕ) {W : Type*} [Fintype W]
    (tri : (Fin n × Fin 3) ≃ W) (ham : W ≃ Fin (3 * n))
    (G : SimpleGraph W)
    (hedges : ∀ u v, G.Adj u v → CycleEdge ham u v ∨ TriangleEdge tri u v) :
    G.Colorable 3 := by
  apply PetrovFinite.colorable_of_cycle_and_triangle_cover tri ham G
  intro u v huv
  exact hedges u v huv

/-- Chromatic-number form of the same theorem. -/
theorem erdos_842_chromaticNumber_le
    (n : ℕ) {W : Type*} [Fintype W]
    (tri : (Fin n × Fin 3) ≃ W) (ham : W ≃ Fin (3 * n))
    (G : SimpleGraph W)
    (hedges : ∀ u v, G.Adj u v → CycleEdge ham u v ∨ TriangleEdge tri u v) :
    G.chromaticNumber ≤ 3 := by
  exact (erdos_842 n tri ham G hedges).chromaticNumber_le

end JSP698

#print axioms JSP698.PetrovFinite.centralCoeff_mod_four
#print axioms JSP698.erdos_842
#print axioms JSP698.erdos_842_chromaticNumber_le
