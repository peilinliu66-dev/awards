import Mathlib

/-!
# A finite, ordered, two-colour Ramsey theorem for triples

Target: Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Namespace: `JSP198`.

The full finite proof was kernel-checked locally on the pinned toolchain.
The proof is entirely finite: exact subset selection, a two-colour pigeonhole
argument, a pair-canonical selection, pair Ramsey, triple-canonical selection,
and a final pigeonhole argument. No Ramsey theorem is imported or postulated.

The triple colouring need not be symmetric. Only strictly increasing triples
are constrained. The public terminal `finite_ramsey_triples_ordered_25` has
exactly the ordered-embedding interface needed by the geometry module.

Mathematical attribution: the classical finite Ramsey theorem. This file is a
formalization of a standard finite recursive proof, not a new mathematical result.

The recursive bounds are deliberately very large. They are marked irreducible
AFTER proving their recurrence equations, so elaboration does not try to
normalize their enormous numerical values. No bound needs to be evaluated.
-/

noncomputable section

namespace JSP198
namespace FiniteRamsey

universe u

/-! ## Explicit finite bounds -/

/-- Enough vertices to select `r` vertices whose pair-colour depends only on
    the smaller vertex. -/
def pairFanBound : ℕ → ℕ
  | 0 => 0
  | r + 1 => 2 * pairFanBound r + 1

theorem pairFanBound_zero : pairFanBound 0 = 0 := rfl

theorem pairFanBound_succ (r : ℕ) :
    pairFanBound (r + 1) = 2 * pairFanBound r + 1 := rfl

/-- In particular, `pairFanBound r = 2^r - 1`; the addition form avoids
    truncated subtraction. -/
theorem pairFanBound_add_one (r : ℕ) :
    pairFanBound r + 1 = 2 ^ r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [pairFanBound_succ, pow_succ]
      omega

/-- A deliberately non-optimal two-colour pair Ramsey bound. -/
def pairBound (k : ℕ) : ℕ := pairFanBound (2 * k)

theorem pairBound_eq (k : ℕ) :
    pairBound k = pairFanBound (2 * k) := rfl

/-- Enough vertices to select `r` vertices whose increasing-triple colour
    depends only on the first vertex. -/
def tripleFanBound : ℕ → ℕ
  | 0 => 0
  | r + 1 => pairBound (tripleFanBound r) + 1

theorem tripleFanBound_zero : tripleFanBound 0 = 0 := rfl

theorem tripleFanBound_succ (r : ℕ) :
    tripleFanBound (r + 1) = pairBound (tripleFanBound r) + 1 := rfl

theorem tripleFanBound_succ_eq_pow (r : ℕ) :
    tripleFanBound (r + 1) = 2 ^ (2 * tripleFanBound r) := by
  rw [tripleFanBound_succ, pairBound_eq, pairFanBound_add_one]

/-- An explicit bound for a monochromatic ordered `k`-vertex triple colouring. -/
def tripleBound (k : ℕ) : ℕ := tripleFanBound (2 * k)

theorem tripleBound_eq (k : ℕ) :
    tripleBound k = tripleFanBound (2 * k) := rfl

attribute [irreducible] pairFanBound pairBound tripleFanBound tripleBound

/-! ## Exact finite selection and the two-colour pigeonhole principle -/

section FiniteSelection

variable {α : Type u} [DecidableEq α]

/-- Select exactly `k` elements, proved directly by finite induction. -/
theorem subset_exact_card (U : Finset α) (k : ℕ) (hk : k ≤ U.card) :
    ∃ S : Finset α, S ⊆ U ∧ S.card = k := by
  classical
  induction k generalizing U with
  | zero =>
      exact ⟨∅, Finset.empty_subset U, rfl⟩
  | succ k ih =>
      have hpos : 0 < U.card := by omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      have herase : (U.erase a).card + 1 = U.card :=
        Finset.card_erase_add_one ha
      obtain ⟨S, hS, hScard⟩ := ih (U.erase a) (by omega)
      have haS : a ∉ S := by
        intro haS
        exact (Finset.mem_erase.mp (hS haS)).1 rfl
      refine ⟨insert a S, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with hxa | hxS
        · simpa only [hxa] using ha
        · exact (Finset.mem_erase.mp (hS hxS)).2
      · rw [Finset.card_insert_of_notMem haS, hScard]

/-- From `2*k` elements with arbitrary Boolean labels, select exactly `k`
    elements with the same label. This includes `k = 0`. -/
theorem bool_pigeonhole_exact (U : Finset α) (label : α → Bool)
    (k : ℕ) (hU : 2 * k ≤ U.card) :
    ∃ (S : Finset α) (b : Bool),
      S ⊆ U ∧ S.card = k ∧ ∀ x ∈ S, label x = b := by
  classical
  let F : Finset α := U.filter (fun x => label x = false)
  let T : Finset α := U.filter (fun x => label x = true)
  have hdisj : Disjoint F T := by
    apply Finset.disjoint_left.mpr
    intro x hxF hxT
    have hf : label x = false := (Finset.mem_filter.mp hxF).2
    have ht : label x = true := (Finset.mem_filter.mp hxT).2
    rw [hf] at ht
    cases ht
  have hunion : F ∪ T = U := by
    ext x
    cases hx : label x <;> simp [F, T, hx]
  have hsum : F.card + T.card = U.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  by_cases hF : k ≤ F.card
  · obtain ⟨S, hSF, hScard⟩ := subset_exact_card F k hF
    refine ⟨S, false, ?_, hScard, ?_⟩
    · intro x hx
      exact (Finset.mem_filter.mp (hSF hx)).1
    · intro x hx
      exact (Finset.mem_filter.mp (hSF hx)).2
  · have hT : k ≤ T.card := by omega
    obtain ⟨S, hST, hScard⟩ := subset_exact_card T k hT
    refine ⟨S, true, ?_, hScard, ?_⟩
    · intro x hx
      exact (Finset.mem_filter.mp (hST hx)).1
    · intro x hx
      exact (Finset.mem_filter.mp (hST hx)).2

end FiniteSelection

/-! ## Ordered reservoirs -/

section Ordered

variable {α : Type u} [LinearOrder α]

/-- Remove the minimum of a sufficiently large finite set. All remaining
    elements lie strictly above the removed vertex. -/
theorem minimum_and_tail (U : Finset α) (q : ℕ) (hU : q + 1 ≤ U.card) :
    ∃ (a : α) (V : Finset α),
      a ∈ U ∧ V ⊆ U ∧ q ≤ V.card ∧ ∀ x ∈ V, a < x := by
  classical
  have hne : U.Nonempty := Finset.card_pos.mp (by omega)
  let a : α := U.min' hne
  have ha : a ∈ U := U.min'_mem hne
  have he : (U.erase a).card + 1 = U.card :=
    Finset.card_erase_add_one ha
  refine ⟨a, U.erase a, ha, Finset.erase_subset a U, ?_, ?_⟩
  · omega
  · intro x hx
    have hxU : x ∈ U := (Finset.mem_erase.mp hx).2
    have hxa : x ≠ a := (Finset.mem_erase.mp hx).1
    have hle : a ≤ x := U.min'_le x hxU
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact (hxa heq.symm).elim

/-- Only increasing pairs matter. -/
def PairHomogeneous (C : α → α → Bool) (S : Finset α) (b : Bool) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x < y → C x y = b

/-- The colour of an increasing pair is determined by its first vertex. -/
def PairCanonical (C : α → α → Bool) (S : Finset α)
    (label : α → Bool) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x < y → C x y = label x

/-- Only increasing triples matter; no symmetry is required. -/
def TripleHomogeneous (C : α → α → α → Bool) (S : Finset α) (b : Bool) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → C x y z = b

/-- The colour of an increasing triple is determined by its first vertex. -/
def TripleCanonical (C : α → α → α → Bool) (S : Finset α)
    (label : α → Bool) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → C x y z = label x

/-! ## Pair Ramsey, proved from the unary pigeonhole principle -/

/-- Construct a first-vertex-canonical set by induction on its cardinality. -/
theorem pair_canonical (C : α → α → Bool) (r : ℕ) :
    ∀ U : Finset α, pairFanBound r ≤ U.card →
      ∃ S : Finset α, S ⊆ U ∧ S.card = r ∧
        ∃ label : α → Bool, PairCanonical C S label := by
  classical
  induction r with
  | zero =>
      intro U hU
      refine ⟨∅, Finset.empty_subset U, rfl, (fun _ => false), ?_⟩
      simp [PairCanonical]
  | succ r ih =>
      intro U hU
      have hcap : 2 * pairFanBound r + 1 ≤ U.card := by
        simpa only [pairFanBound_succ] using hU
      obtain ⟨a, V, haU, hVU, hVcard, hamin⟩ :=
        minimum_and_tail U (2 * pairFanBound r) hcap
      obtain ⟨T, b, hTV, hTcard, hTb⟩ :=
        bool_pigeonhole_exact V (C a) (pairFanBound r) hVcard
      obtain ⟨S, hST, hScard, label, hcanonical⟩ :=
        ih T (le_of_eq hTcard.symm)
      have ha_lt (x : α) (hx : x ∈ S) : a < x :=
        hamin x (hTV (hST hx))
      have haS : a ∉ S := by
        intro ha
        exact (lt_irrefl a) (ha_lt a ha)
      refine ⟨insert a S, ?_, ?_, (fun x => if x = a then b else label x), ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with hxa | hxS
        · simpa only [hxa] using haU
        · exact hVU (hTV (hST hxS))
      · rw [Finset.card_insert_of_notMem haS, hScard]
      · intro x hx y hy hxy
        by_cases hxa : x = a
        · subst x
          have hya : y ≠ a := ne_of_gt hxy
          have hyS : y ∈ S := (Finset.mem_insert.mp hy).resolve_left hya
          simpa using hTb y (hST hyS)
        · have hxS : x ∈ S := (Finset.mem_insert.mp hx).resolve_left hxa
          have hya : y ≠ a := ne_of_gt ((ha_lt x hxS).trans hxy)
          have hyS : y ∈ S := (Finset.mem_insert.mp hy).resolve_left hya
          simpa only [if_neg hxa] using hcanonical x hxS y hyS hxy

/-- The finite two-colour pair Ramsey theorem on any linearly ordered type. -/
theorem pair_homogeneous (U : Finset α) (C : α → α → Bool)
    (k : ℕ) (hU : pairBound k ≤ U.card) :
    ∃ S : Finset α, S ⊆ U ∧ S.card = k ∧
      ∃ b : Bool, PairHomogeneous C S b := by
  classical
  have hcap : pairFanBound (2 * k) ≤ U.card := by
    simpa only [pairBound_eq] using hU
  obtain ⟨T, hTU, hTcard, label, hcanonical⟩ :=
    pair_canonical C (2 * k) U hcap
  obtain ⟨S, b, hST, hScard, hSb⟩ :=
    bool_pigeonhole_exact T label k (by omega)
  refine ⟨S, (fun x hx => hTU (hST hx)), hScard, b, ?_⟩
  intro x hx y hy hxy
  exact (hcanonical x (hST hx) y (hST hy) hxy).trans (hSb x hx)

/-! ## Triple Ramsey, using the already proved pair theorem for links -/

/-- For the new minimum `a`, apply pair Ramsey to the link `C a` on the tail.
    The induction then runs inside that homogeneous tail. -/
theorem triple_canonical (C : α → α → α → Bool) (r : ℕ) :
    ∀ U : Finset α, tripleFanBound r ≤ U.card →
      ∃ S : Finset α, S ⊆ U ∧ S.card = r ∧
        ∃ label : α → Bool, TripleCanonical C S label := by
  classical
  induction r with
  | zero =>
      intro U hU
      refine ⟨∅, Finset.empty_subset U, rfl, (fun _ => false), ?_⟩
      simp [TripleCanonical]
  | succ r ih =>
      intro U hU
      have hcap : pairBound (tripleFanBound r) + 1 ≤ U.card := by
        simpa only [tripleFanBound_succ] using hU
      obtain ⟨a, V, haU, hVU, hVcard, hamin⟩ :=
        minimum_and_tail U (pairBound (tripleFanBound r)) hcap
      obtain ⟨T, hTV, hTcard, b, hTb⟩ :=
        pair_homogeneous V (C a) (tripleFanBound r) hVcard
      obtain ⟨S, hST, hScard, label, hcanonical⟩ :=
        ih T (le_of_eq hTcard.symm)
      have ha_lt (x : α) (hx : x ∈ S) : a < x :=
        hamin x (hTV (hST hx))
      have haS : a ∉ S := by
        intro ha
        exact (lt_irrefl a) (ha_lt a ha)
      refine ⟨insert a S, ?_, ?_, (fun x => if x = a then b else label x), ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with hxa | hxS
        · simpa only [hxa] using haU
        · exact hVU (hTV (hST hxS))
      · rw [Finset.card_insert_of_notMem haS, hScard]
      · intro x hx y hy z hz hxy hyz
        by_cases hxa : x = a
        · subst x
          have hya : y ≠ a := ne_of_gt hxy
          have hza : z ≠ a := ne_of_gt (hxy.trans hyz)
          have hyS : y ∈ S := (Finset.mem_insert.mp hy).resolve_left hya
          have hzS : z ∈ S := (Finset.mem_insert.mp hz).resolve_left hza
          simpa using hTb y (hST hyS) z (hST hzS) hyz
        · have hxS : x ∈ S := (Finset.mem_insert.mp hx).resolve_left hxa
          have hay : a < y := (ha_lt x hxS).trans hxy
          have haz : a < z := hay.trans hyz
          have hyS : y ∈ S :=
            (Finset.mem_insert.mp hy).resolve_left (ne_of_gt hay)
          have hzS : z ∈ S :=
            (Finset.mem_insert.mp hz).resolve_left (ne_of_gt haz)
          simpa only [if_neg hxa] using hcanonical x hxS y hyS z hzS hxy hyz

/-- The finite two-colour triple Ramsey theorem, before ordered enumeration. -/
theorem triple_homogeneous (U : Finset α) (C : α → α → α → Bool)
    (k : ℕ) (hU : tripleBound k ≤ U.card) :
    ∃ S : Finset α, S ⊆ U ∧ S.card = k ∧
      ∃ b : Bool, TripleHomogeneous C S b := by
  classical
  have hcap : tripleFanBound (2 * k) ≤ U.card := by
    simpa only [tripleBound_eq] using hU
  obtain ⟨T, hTU, hTcard, label, hcanonical⟩ :=
    triple_canonical C (2 * k) U hcap
  obtain ⟨S, b, hST, hScard, hSb⟩ :=
    bool_pigeonhole_exact T label k (by omega)
  refine ⟨S, (fun x hx => hTU (hST hx)), hScard, b, ?_⟩
  intro x hx y hy z hz hxy hyz
  exact (hcanonical x (hST hx) y (hST hy) z (hST hz) hxy hyz).trans (hSb x hx)

/-- Ordered enumeration of a homogeneous set, with membership in the original
    reservoir. The enumeration step uses only finite-set sorting in Mathlib. -/
theorem ordered_triples_on_finset (U : Finset α) (C : α → α → α → Bool)
    (k : ℕ) (hU : tripleBound k ≤ U.card) :
    ∃ f : Fin k → α, StrictMono f ∧ (∀ i, f i ∈ U) ∧
      ∃ b : Bool, ∀ i j l : Fin k, i < j → j < l →
        C (f i) (f j) (f l) = b := by
  classical
  obtain ⟨S, hSU, hScard, b, hhomogeneous⟩ := triple_homogeneous U C k hU
  let f : Fin k → α := S.orderEmbOfFin hScard
  have hmono : StrictMono f := (S.orderEmbOfFin hScard).strictMono
  have hmem (i : Fin k) : f i ∈ S := S.orderEmbOfFin_mem hScard i
  refine ⟨f, hmono, (fun i => hSU (hmem i)), b, ?_⟩
  intro i j l hij hjl
  exact hhomogeneous (f i) (hmem i) (f j) (hmem j) (f l) (hmem l)
    (hmono hij) (hmono hjl)

end Ordered
end FiniteRamsey

/-! ## Public terminals: no structural, probabilistic, or Ramsey hypotheses -/

/-- The bound-specific ordered theorem, valid for every natural target `k`.
    Values of `C` on triples that are not strictly increasing are irrelevant. -/
theorem finite_ramsey_triples_ordered_at_bound (k : ℕ)
    (C : Fin (FiniteRamsey.tripleBound k) →
      Fin (FiniteRamsey.tripleBound k) →
      Fin (FiniteRamsey.tripleBound k) → Bool) :
    ∃ f : Fin k → Fin (FiniteRamsey.tripleBound k), StrictMono f ∧
      ∃ b : Bool, ∀ i j l : Fin k, i < j → j < l →
        C (f i) (f j) (f l) = b := by
  classical
  obtain ⟨f, hf, _hmem, b, hb⟩ :=
    FiniteRamsey.ordered_triples_on_finset
      (Finset.univ : Finset (Fin (FiniteRamsey.tripleBound k))) C k (by simp)
  exact ⟨f, hf, b, hb⟩

/-- Finite three-uniform, two-colour Ramsey in the ordered-embedding interface. -/
theorem finite_ramsey_triples_ordered (k : ℕ) :
    ∃ N : ℕ, ∀ C : Fin N → Fin N → Fin N → Bool,
      ∃ f : Fin k → Fin N, StrictMono f ∧
        ∃ b : Bool, ∀ i j l : Fin k, i < j → j < l →
          C (f i) (f j) (f l) = b := by
  refine ⟨FiniteRamsey.tripleBound k, ?_⟩
  intro C
  exact finite_ramsey_triples_ordered_at_bound k C

/-- The exact 25-point interface requested by the geometry module. -/
theorem finite_ramsey_triples_ordered_25 :
    ∃ N : ℕ, ∀ C : Fin N → Fin N → Fin N → Bool,
      ∃ f : Fin 25 → Fin N, StrictMono f ∧
        ∃ b : Bool, ∀ i j k : Fin 25, i < j → j < k →
          C (f i) (f j) (f k) = b :=
  finite_ramsey_triples_ordered 25

#print axioms JSP198.FiniteRamsey.bool_pigeonhole_exact
#print axioms JSP198.FiniteRamsey.pair_homogeneous
#print axioms JSP198.FiniteRamsey.triple_homogeneous
#print axioms JSP198.finite_ramsey_triples_ordered
#print axioms JSP198.finite_ramsey_triples_ordered_25

end JSP198
