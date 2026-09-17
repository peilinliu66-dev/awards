/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Enumeration.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import Mathlib

namespace Horton

/-- The abstract sign vector satisfies alternation and the four- and five-point sign constraints
that every real orientation assignment satisfies. -/
def Consistent (σ : Fin 5 → Fin 5 → Fin 5 → Bool) : Prop :=
  (∀ i j k, i ≠ j → i ≠ k → j ≠ k → σ j i k = !σ i j k) ∧
  (∀ i j k, i ≠ j → i ≠ k → j ≠ k → σ i k j = !σ i j k) ∧
  (∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ¬ (σ a b c = !σ a b d ∧ σ a c d = !σ a b d ∧ σ b c d = σ a b d)) ∧
  (∀ a b c d e, a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
    ¬ ((σ a b c == σ a d e) = (σ a b d != σ a c e) ∧ (σ a b d != σ a c e) = (σ a b e == σ a c d)))

/-- Certificate that indices `i j k l` in this cyclic order bound a convex quadrilateral whose
interior avoids the fifth index `m`: every edge sees the two remaining vertices positively, each
vertex lies negatively against the diagonal of its two neighbours, and some edge sees `m`
negatively. -/
def QuadCert (σ : Fin 5 → Fin 5 → Fin 5 → Bool) (i j k l m : Fin 5) : Prop :=
  σ i j k = true ∧ σ i j l = true ∧ σ j k l = true ∧ σ j k i = true ∧
  σ k l i = true ∧ σ k l j = true ∧ σ l i j = true ∧ σ l i k = true ∧
  σ i k j = false ∧ σ i k l = true ∧ σ j l k = false ∧ σ j l i = true ∧
  (σ i j m = false ∨ σ j k m = false ∨ σ k l m = false ∨ σ l i m = false)

/-! ### Finite encoding: sign vectors on the ten sorted triples -/

/-- Index (in `0..9`) of a sorted triple `i < j < k` (combinatorial number system). -/
def idx (i j k : Fin 5) : Nat :=
  (i.val + j.val * (j.val - 1) / 2 + k.val * (k.val - 1) * (k.val - 2) / 6) % 10

/-- The sorted triple with a given index; inverse of `idx` on sorted triples. -/
def tri : Nat → Fin 5 × Fin 5 × Fin 5
  | 0 => (0, 1, 2) | 1 => (0, 1, 3) | 2 => (0, 2, 3) | 3 => (1, 2, 3) | 4 => (0, 1, 4)
  | 5 => (0, 2, 4) | 6 => (1, 2, 4) | 7 => (0, 3, 4) | 8 => (1, 3, 4) | _ => (2, 3, 4)

theorem idx_lt (i j k : Fin 5) : idx i j k < 10 := Nat.mod_lt _ (by decide)

theorem tri_idx : ∀ i j k : Fin 5, i < j → j < k → tri (idx i j k) = (i, j, k) := by decide

/-- Extend a sign function known on sorted triples to all triples by alternation. -/
def extend (w : Fin 5 → Fin 5 → Fin 5 → Bool) (i j k : Fin 5) : Bool :=
  if i < j then (if j < k then w i j k else if i < k then !w i k j else w k i j)
  else (if i < k then !w j i k else if j < k then w j k i else !w k j i)

/-- The alternating sign function determined by a bit vector `v` on sorted-triple indices. -/
def ofBits (v : Nat → Bool) : Fin 5 → Fin 5 → Fin 5 → Bool :=
  extend fun i j k => v (idx i j k)

/-- The bit vector of an arbitrary sign function (its values on sorted triples). -/
def encode (σ : Fin 5 → Fin 5 → Fin 5 → Bool) (t : Nat) : Bool :=
  σ (tri t).1 (tri t).2.1 (tri t).2.2

/-- A bit vector from ten explicit bits. -/
def mk10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Nat → Bool
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4
  | 5 => b5 | 6 => b6 | 7 => b7 | 8 => b8 | 9 => b9 | _ => false

theorem mk10_encode_idx (σ : Fin 5 → Fin 5 → Fin 5 → Bool) (i j k : Fin 5) :
    mk10 (encode σ 0) (encode σ 1) (encode σ 2) (encode σ 3) (encode σ 4) (encode σ 5)
      (encode σ 6) (encode σ 7) (encode σ 8) (encode σ 9) (idx i j k) = encode σ (idx i j k) := by
  have h := idx_lt i j k
  generalize idx i j k = t at h ⊢
  interval_cases t <;> rfl

theorem ofBits_encode (σ : Fin 5 → Fin 5 → Fin 5 → Bool)
    (h1 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → σ j i k = !σ i j k)
    (h2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → σ i k j = !σ i j k)
    (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ofBits (encode σ) i j k = σ i j k := by
  simp only [ofBits, extend, encode]
  have hij' := lt_or_gt_of_ne hij
  have hik' := lt_or_gt_of_ne hik
  have hjk' := lt_or_gt_of_ne hjk
  split_ifs with a b c d e
  · rw [tri_idx i j k a b]
  · have : i < k := c
    have : k < j := by omega
    rw [tri_idx i k j (by assumption) (by assumption)]
    simp only [h2 i j k hij hik hjk, Bool.not_not]
  · have : k < i := by omega
    rw [tri_idx k i j (by assumption) a]
    simp only [h1 i k j hik hij hjk.symm, h2 i j k hij hik hjk, Bool.not_not]
  · have : j < i := by omega
    rw [tri_idx j i k (by assumption) d]
    simp only [h1 i j k hij hik hjk, Bool.not_not]
  · have : j < k := e
    have : k < i := by omega
    rw [tri_idx j k i (by assumption) (by assumption)]
    simp only [h1 k j i hjk.symm hik.symm hij.symm, h2 k i j hik.symm hjk.symm hij, Bool.not_not,
      h1 i k j hik hij hjk.symm, h2 i j k hij hik hjk]
  · have : k < j := by omega
    have : j < i := by omega
    rw [tri_idx k j i (by assumption) (by assumption)]
    simp only [h2 k i j hik.symm hjk.symm hij, Bool.not_not, h1 i k j hik hij hjk.symm,
      h2 i j k hij hik hjk]

theorem ofBits_mk10 (σ : Fin 5 → Fin 5 → Fin 5 → Bool) :
    ofBits (mk10 (encode σ 0) (encode σ 1) (encode σ 2) (encode σ 3) (encode σ 4) (encode σ 5)
      (encode σ 6) (encode σ 7) (encode σ 8) (encode σ 9)) = ofBits (encode σ) := by
  funext i j k
  simp only [ofBits, extend, mk10_encode_idx]

/-! ### Boolean checkers -/

/-- Forbidden sign pattern from the four-point cofactor identity. -/
def forb4 (σ : Fin 5 → Fin 5 → Fin 5 → Bool) (a b c d : Fin 5) : Bool :=
  (σ a b c == !σ a b d) && (σ a c d == !σ a b d) && (σ b c d == σ a b d)

/-- Forbidden sign pattern from the three-term Grassmann–Plücker identity. -/
def forb5 (σ : Fin 5 → Fin 5 → Fin 5 → Bool) (a b c d e : Fin 5) : Bool :=
  ((σ a b c == σ a d e) == (σ a b d != σ a c e)) && ((σ a b d != σ a c e) == (σ a b e == σ a c d))

/-- One instance of each constraint per 4-subset and per pivot (enough for alternating `σ`). -/
def consistentB (σ : Fin 5 → Fin 5 → Fin 5 → Bool) : Bool :=
  !forb4 σ 0 1 2 3 && !forb4 σ 0 1 2 4 && !forb4 σ 0 1 3 4 && !forb4 σ 0 2 3 4 &&
  !forb4 σ 1 2 3 4 && !forb5 σ 0 1 2 3 4 && !forb5 σ 1 0 2 3 4 && !forb5 σ 2 0 1 3 4 &&
  !forb5 σ 3 0 1 2 4 && !forb5 σ 4 0 1 2 3

def quadCertB (σ : Fin 5 → Fin 5 → Fin 5 → Bool) (i j k l m : Fin 5) : Bool :=
  σ i j k && σ i j l && σ j k l && σ j k i && σ k l i && σ k l j && σ l i j && σ l i k &&
  !σ i k j && σ i k l && !σ j l k && σ j l i &&
  (!σ i j m || !σ j k m || !σ k l m || !σ l i m)

def distinctB (i j k l m : Fin 5) : Bool :=
  i != j && i != k && i != l && i != m && j != k && j != l && j != m && k != l && k != m && l != m

/-- The index left over by four indices (meaningful when they are distinct). -/
def rest (i j k l : Fin 5) : Fin 5 :=
  ⟨(10 - (i.val + j.val + k.val + l.val)) % 5, Nat.mod_lt _ (by decide)⟩

def fin5 : List (Fin 5) := [0, 1, 2, 3, 4]

def search (σ : Fin 5 → Fin 5 → Fin 5 → Bool) : Bool :=
  fin5.any fun i => fin5.any fun j => fin5.any fun k => fin5.any fun l =>
    distinctB i j k l (rest i j k l) && quadCertB σ i j k l (rest i j k l)

def check (v : Nat → Bool) : Bool :=
  !consistentB (ofBits v) || search (ofBits v)

def allBools (f : Bool → Bool) : Bool := f true && f false

theorem allBools_true {f : Bool → Bool} (h : allBools f = true) (b : Bool) : f b = true := by
  simp only [allBools, Bool.and_eq_true] at h
  cases b
  · exact h.2
  · exact h.1

set_option maxRecDepth 100000 in
theorem core :
    (allBools fun b0 => allBools fun b1 => allBools fun b2 => allBools fun b3 =>
      allBools fun b4 => allBools fun b5 => allBools fun b6 => allBools fun b7 =>
      allBools fun b8 => allBools fun b9 => check (mk10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) = true := by
  decide

theorem check_mk10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) :
    check (mk10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) = true :=
  allBools_true (allBools_true (allBools_true (allBools_true (allBools_true (allBools_true
    (allBools_true (allBools_true (allBools_true (allBools_true core b0) b1) b2) b3) b4) b5)
    b6) b7) b8) b9

/-! ### Bridges between the Boolean checkers and the propositions -/

theorem forb4_false (σ : Fin 5 → Fin 5 → Fin 5 → Bool)
    (h1 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → σ j i k = !σ i j k)
    (h2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → σ i k j = !σ i j k) (a b c d : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h : ¬ (σ a b c = !σ a b d ∧ σ a c d = !σ a b d ∧ σ b c d = σ a b d)) :
    forb4 (ofBits (encode σ)) a b c d = false := by
  have e := ofBits_encode σ h1 h2
  rw [forb4, e a b c hab hac hbc, e a b d hab had hbd, e a c d hac had hcd, e b c d hbc hbd hcd]
  revert h
  generalize σ a b c = x
  generalize σ a b d = y
  generalize σ a c d = z
  generalize σ b c d = w
  revert x y z w
  decide

theorem forb5_false (σ : Fin 5 → Fin 5 → Fin 5 → Bool)
    (h1 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → σ j i k = !σ i j k)
    (h2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → σ i k j = !σ i j k) (a b c d e : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (h : ¬ ((σ a b c == σ a d e) = (σ a b d != σ a c e) ∧
      (σ a b d != σ a c e) = (σ a b e == σ a c d))) :
    forb5 (ofBits (encode σ)) a b c d e = false := by
  have e' := ofBits_encode σ h1 h2
  rw [forb5, e' a b c hab hac hbc, e' a d e had hae hde, e' a b d hab had hbd,
    e' a c e hac hae hce, e' a b e hab hae hbe, e' a c d hac had hcd]
  revert h
  generalize σ a b c = x
  generalize σ a d e = y
  generalize σ a b d = z
  generalize σ a c e = w
  generalize σ a b e = u
  generalize σ a c d = t
  revert x y z w u t
  decide

theorem consistentB_of (σ : Fin 5 → Fin 5 → Fin 5 → Bool) (hσ : Consistent σ) :
    consistentB (ofBits (encode σ)) = true := by
  obtain ⟨h1, h2, h4, h5⟩ := hσ
  simp only [consistentB, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  all_goals first
    | exact forb4_false σ h1 h2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (h4 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))
    | exact forb5_false σ h1 h2 _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (h5 _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))

theorem quadCert_of (σ : Fin 5 → Fin 5 → Fin 5 → Bool)
    (h1 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → σ j i k = !σ i j k)
    (h2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → σ i k j = !σ i j k)
    (i j k l m : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m) (hjk : j ≠ k)
    (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (h : quadCertB (ofBits (encode σ)) i j k l m = true) : QuadCert σ i j k l m := by
  have e := ofBits_encode σ h1 h2
  have := hij.symm; have := hik.symm; have := hil.symm; have := him.symm; have := hjk.symm
  have := hjl.symm; have := hjm.symm; have := hkl.symm; have := hkm.symm; have := hlm.symm
  simp (disch := assumption) only [quadCertB, e] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  unfold QuadCert
  tauto

/-- Every consistent abstract order type on five indices contains an empty convex
quadrilateral certificate. -/
theorem exists_quadCert (σ : Fin 5 → Fin 5 → Fin 5 → Bool) (hσ : Consistent σ) :
    ∃ i j k l m : Fin 5, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ i ≠ m ∧ j ≠ k ∧ j ≠ l ∧ j ≠ m ∧
      k ≠ l ∧ k ≠ m ∧ l ≠ m ∧ QuadCert σ i j k l m := by
  have hc : check (encode σ) = true := by
    have h := check_mk10 (encode σ 0) (encode σ 1) (encode σ 2) (encode σ 3) (encode σ 4)
      (encode σ 5) (encode σ 6) (encode σ 7) (encode σ 8) (encode σ 9)
    rwa [check, ofBits_mk10] at h
  have hs : search (ofBits (encode σ)) = true := by
    rw [check, consistentB_of σ hσ] at hc
    simpa using hc
  simp only [search, List.any_eq_true, Bool.and_eq_true] at hs
  obtain ⟨i, -, j, -, k, -, l, -, hd, hq⟩ := hs
  simp only [distinctB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hij, hik⟩, hil⟩, him⟩, hjk⟩, hjl⟩, hjm⟩, hkl⟩, hkm⟩, hlm⟩ := hd
  exact ⟨i, j, k, l, rest i j k l, hij, hik, hil, him, hjk, hjl, hjm, hkl, hkm, hlm,
    quadCert_of σ hσ.1 hσ.2.1 i j k l _ hij hik hil him hjk hjl hjm hkl hkm hlm hq⟩

end Horton
