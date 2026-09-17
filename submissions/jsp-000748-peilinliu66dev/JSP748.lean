import Mathlib

/-!
# JSP-000748 / Erdős 900

Target toolchain: Lean 4.33.1.
Target Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474.

This complete source passed standalone Lean compilation (main_v6_compile.log).
The terminal declarations `erdos_900_fixed_c` and `erdos_900` retain the full
original quantifiers. The exact fixed-edge sample space, graph-specific DFS tree,
adaptive transcript bijection, hypergeometric moments, Chebyshev bound, rounding
limits, and both branches of the explicit coefficient are all implemented below.

No external random-graph theorem is used as an assumption. Both terminal
theorems report only propext, Classical.choice, and Quot.sound. Package build
evidence is recorded in verification/; this is not official prize verification.

Mathematical attribution: Ajtai--Komlós--Szemerédi (1981).
DFS proof method: Krivelevich--Sudakov, arXiv:1201.6529.
The companion proof gives the complete mathematical argument directly in G(n,m).
-/

noncomputable section

open scoped BigOperators Topology
open Filter Finset

namespace JSP748

/-! ## Exact uniform fixed-edge model -/

/-- Each element is an unordered pair of distinct labelled vertices. -/
def edgeUniverse (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard 2

/-- All simple labelled graphs with exactly `m` edges, each represented once. -/
def graphFamily (n m : ℕ) : Finset (Finset (Finset (Fin n))) :=
  (edgeUniverse n).powersetCard m

@[simp] theorem edgeUniverse_card (n : ℕ) :
    (edgeUniverse n).card = n.choose 2 := by
  simp [edgeUniverse]

@[simp] theorem graphFamily_card (n m : ℕ) :
    (graphFamily n m).card = (n.choose 2).choose m := by
  simp [graphFamily]

@[simp] theorem mem_edgeUniverse {n : ℕ} {e : Finset (Fin n)} :
    e ∈ edgeUniverse n ↔ e.card = 2 := by
  simp [edgeUniverse, Finset.mem_powersetCard]

@[simp] theorem mem_graphFamily {n m : ℕ} {A : Finset (Finset (Fin n))} :
    A ∈ graphFamily n m ↔ A ⊆ edgeUniverse n ∧ A.card = m := by
  simp [graphFamily, Finset.mem_powersetCard]

/-- The usual simple graph associated with an unordered edge set. -/
def toGraph {n : ℕ} (A : Finset (Finset (Fin n))) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ {u, v} ∈ A
  symm := ⟨by
    intro u v h
    exact ⟨Ne.symm h.1, by simpa [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

/-- Length means number of EDGES; `IsPath` excludes repeated vertices. -/
def HasPathAtLeast {n : ℕ} (A : Finset (Finset (Fin n))) (ell : ℝ) : Prop :=
  ∃ u v : Fin n, ∃ p : (toGraph A).Walk u v, p.IsPath ∧ ell ≤ (p.length : ℝ)

/-- The exact uniform probability, represented as a finite counting ratio.
For the finitely many impossible sizes `m > n.choose 2` the ratio is zero.
For every fixed positive `c`, `m = floor(c*n)` is possible eventually. -/
def pathProbability (n m : ℕ) (ell : ℝ) : ℝ := by
  classical
  exact (((graphFamily n m).filter (fun A => HasPathAtLeast A ell)).card : ℝ) /
    ((graphFamily n m).card : ℝ)

theorem pathProbability_nonneg (n m : ℕ) (ell : ℝ) :
    0 ≤ pathProbability n m ell := by
  classical
  unfold pathProbability
  positivity

theorem pathProbability_le_one (n m : ℕ) (ell : ℝ) :
    pathProbability n m ell ≤ 1 := by
  classical
  unfold pathProbability
  by_cases h : (graphFamily n m).card = 0
  · simp [h]
  · have hd : (0 : ℝ) < ((graphFamily n m).card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h
    apply (div_le_iff₀ hd).2
    simpa using
      (Nat.cast_le.mpr (Finset.card_filter_le (graphFamily n m)
        (fun A => HasPathAtLeast A ell)) :
        (((graphFamily n m).filter (fun A => HasPathAtLeast A ell)).card : ℝ) ≤
          ((graphFamily n m).card : ℝ))

/-! ## Full target; proved by `erdos_900` at the end of the file -/

def OriginalStatement : Prop :=
  ∃ f : ℝ → ℝ,
    (∀ c : ℝ, 1 / 2 < c → 0 < f c ∧ f c < 1) ∧
    Tendsto f (nhdsWithin (1 / 2) (Set.Ioi (1 / 2))) (𝓝 0) ∧
    Tendsto f atTop (𝓝 1) ∧
    ∀ c : ℝ, 1 / 2 < c →
      Tendsto
        (fun n : ℕ => pathProbability n ⌊c * (n : ℝ)⌋₊ (f c * (n : ℝ)))
        atTop (𝓝 1)

/-! ## Adaptive querying without replacement

A tree queries every coordinate once. Its next coordinate may depend on every
previous answer. The encoding below is a weight-preserving bijection, not an
independence assertion about the answers.
-/

namespace Reveal

variable {α : Type*} [DecidableEq α]

inductive Tree (α : Type*) [DecidableEq α] : Finset α → Type _ where
  | done : Tree α ∅
  | node {s : Finset α} (e : α) (he : e ∈ s)
      (no yes : Tree α (s.erase e)) : Tree α s

/-- Encode a subset by the answers along the adaptively selected coordinates. -/
def encode : {s : Finset α} → Tree α s → Finset α → List Bool
  | _, .done, _ => []
  | _, .node e _ no yes, A =>
      if e ∈ A then true :: encode yes (A.erase e)
      else false :: encode no A

/-- Decode a full answer word. Values on incorrectly sized words are immaterial. -/
def decode : {s : Finset α} → Tree α s → List Bool → Finset α
  | _, .done, _ => ∅
  | _, .node _ _ no _, [] => decode no []
  | _, .node _ _ no _, false :: bs => decode no bs
  | _, .node e _ _ yes, true :: bs => insert e (decode yes bs)

/-- Number of positive answers. -/
def ones : List Bool → ℕ
  | [] => 0
  | false :: bs => ones bs
  | true :: bs => ones bs + 1

@[simp] theorem ones_nil : ones [] = 0 := rfl
@[simp] theorem ones_false (bs : List Bool) : ones (false :: bs) = ones bs := rfl
@[simp] theorem ones_true (bs : List Bool) : ones (true :: bs) = ones bs + 1 := rfl

@[simp] theorem ones_append (a b : List Bool) :
    ones (a ++ b) = ones a + ones b := by
  induction a with
  | nil => simp [ones]
  | cons x xs ih => cases x <;> simp [ones, ih, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

theorem ones_le_length (bs : List Bool) : ones bs ≤ bs.length := by
  induction bs with
  | nil => simp [ones]
  | cons b bs ih => cases b <;> simp [ones] <;> omega

theorem ones_take_le (bs : List Bool) (t : ℕ) : ones (bs.take t) ≤ ones bs := by
  have h := ones_append (bs.take t) (bs.drop t)
  rw [List.take_append_drop] at h
  omega

theorem length_encode {s : Finset α} (T : Tree α s) (A : Finset α) :
    (encode T A).length = s.card := by
  induction T generalizing A with
  | done => simp [encode]
  | @node s e he no yes ihno ihyes =>
    have hs : (s.erase e).card + 1 = s.card := by
      rw [Finset.card_erase_of_mem he]
      have := Finset.card_pos.mpr ⟨e, he⟩
      omega
    by_cases h : e ∈ A
    · simpa [encode, h, ihyes] using hs
    · simpa [encode, h, ihno] using hs

theorem decode_subset {s : Finset α} (T : Tree α s) (bs : List Bool) :
    decode T bs ⊆ s := by
  induction T generalizing bs with
  | done => simp [decode]
  | @node s e he no yes ihno ihyes =>
    cases bs with
    | nil => exact (ihno []).trans (Finset.erase_subset _ _)
    | cons b bs =>
      cases b with
      | false => exact (ihno bs).trans (Finset.erase_subset _ _)
      | true =>
        apply Finset.insert_subset_iff.mpr
        exact ⟨he, (ihyes bs).trans (Finset.erase_subset _ _)⟩

theorem decode_encode {s : Finset α} (T : Tree α s) {A : Finset α}
    (hA : A ⊆ s) : decode T (encode T A) = A := by
  induction T generalizing A with
  | done =>
    have : A = ∅ := Finset.subset_empty.mp hA
    subst A
    rfl
  | @node s e he no yes ihno ihyes =>
    by_cases h : e ∈ A
    · have hsub : A.erase e ⊆ s.erase e := Finset.erase_subset_erase e hA
      simp only [encode, if_pos h, decode]
      rw [ihyes hsub, Finset.insert_erase h]
    · have hsub : A ⊆ s.erase e := by
        intro a ha
        exact Finset.mem_erase.mpr ⟨by intro haeq; subst a; exact h ha, hA ha⟩
      simp only [encode, if_neg h, decode]
      exact ihno hsub

theorem encode_injective_on {s : Finset α} (T : Tree α s)
    {A B : Finset α} (hA : A ⊆ s) (hB : B ⊆ s)
    (h : encode T A = encode T B) : A = B := by
  have hh := congrArg (decode T) h
  simpa [decode_encode T hA, decode_encode T hB] using hh

theorem encode_decode {s : Finset α} (T : Tree α s) {bs : List Bool}
    (hbs : bs.length = s.card) : encode T (decode T bs) = bs := by
  induction T generalizing bs with
  | done =>
    have : bs = [] := List.length_eq_zero_iff.mp (by simpa using hbs)
    subst bs
    rfl
  | @node s e he no yes ihno ihyes =>
    have hs : (s.erase e).card + 1 = s.card := by
      rw [Finset.card_erase_of_mem he]
      have := Finset.card_pos.mpr ⟨e, he⟩
      omega
    cases bs with
    | nil =>
      simp only [List.length_nil] at hbs
      omega
    | cons b bs =>
      have hlen : bs.length = (s.erase e).card := by
        simp only [List.length_cons] at hbs
        omega
      cases b with
      | false =>
        have hnot : e ∉ decode no bs := by
          intro hh
          exact (Finset.mem_erase.mp (decode_subset no bs hh)).1 rfl
        change encode (.node e he no yes) (decode no bs) = false :: bs
        rw [encode, if_neg hnot, ihno hlen]
      | true =>
        have hnot : e ∉ decode yes bs := by
          intro hh
          exact (Finset.mem_erase.mp (decode_subset yes bs hh)).1 rfl
        simp only [decode, encode, Finset.mem_insert_self, if_true]
        rw [Finset.erase_insert hnot, ihyes hlen]

theorem ones_encode {s : Finset α} (T : Tree α s) {A : Finset α}
    (hA : A ⊆ s) : ones (encode T A) = A.card := by
  induction T generalizing A with
  | done =>
    have : A = ∅ := Finset.subset_empty.mp hA
    subst A
    rfl
  | @node s e he no yes ihno ihyes =>
    by_cases h : e ∈ A
    · have hsub : A.erase e ⊆ s.erase e := Finset.erase_subset_erase e hA
      simp only [encode, if_pos h, ones]
      rw [ihyes hsub, Finset.card_erase_of_mem h]
      have := Finset.card_pos.mpr ⟨e, h⟩
      omega
    · have hsub : A ⊆ s.erase e := by
        intro a ha
        exact Finset.mem_erase.mpr ⟨by intro haeq; subst a; exact h ha, hA ha⟩
      simp only [encode, if_neg h, ones]
      exact ihno hsub

theorem card_decode {s : Finset α} (T : Tree α s) {bs : List Bool}
    (hbs : bs.length = s.card) : (decode T bs).card = ones bs := by
  have h := ones_encode T (decode_subset T bs)
  rw [encode_decode T hbs] at h
  exact h.symm

/-- The adaptive transcript map is a bijection on every fixed-weight slice. -/
def fixedWeightEquiv {s : Finset α} (T : Tree α s) (m : ℕ) :
    {A : Finset α // A ⊆ s ∧ A.card = m} ≃
    {bs : List Bool // bs.length = s.card ∧ ones bs = m} where
  toFun A := ⟨encode T A.1, length_encode T A.1, by
    rw [ones_encode T A.2.1, A.2.2]⟩
  invFun bs := ⟨decode T bs.1, decode_subset T bs.1, by
    rw [card_decode T bs.2.1, bs.2.2]⟩
  left_inv A := Subtype.ext (decode_encode T A.2.1)
  right_inv bs := Subtype.ext (encode_decode T bs.2.1)

/-- A finite set of all binary words of a prescribed length. -/
def binaryWords : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (binaryWords n).image (List.cons false) ∪
      (binaryWords n).image (List.cons true)

@[simp] theorem mem_binaryWords (bs : List Bool) (n : ℕ) :
    bs ∈ binaryWords n ↔ bs.length = n := by
  induction n generalizing bs with
  | zero => simp [binaryWords]
  | succ n ih =>
    cases bs with
    | nil => simp [binaryWords]
    | cons b bs =>
      cases b <;> simp [binaryWords, ih]

def weightWords (n m : ℕ) : Finset (List Bool) :=
  (binaryWords n).filter (fun bs => ones bs = m)

@[simp] theorem mem_weightWords {bs : List Bool} {n m : ℕ} :
    bs ∈ weightWords n m ↔ bs.length = n ∧ ones bs = m := by
  simp [weightWords]

theorem cons_images_disjoint (A B : Finset (List Bool)) :
    Disjoint (A.image (List.cons false)) (B.image (List.cons true)) := by
  apply Finset.disjoint_left.mpr
  intro bs hA hB
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hA
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hB
  have : false :: a = true :: b := ha.trans hb.symm
  cases this

theorem card_image_cons (A : Finset (List Bool)) (b : Bool) :
    (A.image (List.cons b)).card = A.card := by
  apply Finset.card_image_of_injective
  intro a a' h
  exact (List.cons.inj h).2

theorem weightWords_succ_zero (n : ℕ) :
    weightWords (n + 1) 0 = (weightWords n 0).image (List.cons false) := by
  ext bs
  cases bs with
  | nil => simp
  | cons b bs => cases b <;> simp [ones]

theorem weightWords_succ_succ (n m : ℕ) :
    weightWords (n + 1) (m + 1) =
      (weightWords n (m + 1)).image (List.cons false) ∪
      (weightWords n m).image (List.cons true) := by
  ext bs
  cases bs with
  | nil => simp
  | cons b bs => cases b <;> simp [ones]

@[simp] theorem weightWords_card (n m : ℕ) :
    (weightWords n m).card = n.choose m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero =>
      have hz : weightWords 0 0 = {[]} := by
        ext bs
        cases bs <;> simp [ones]
      rw [hz]
      simp
    | succ m => simp [weightWords, binaryWords, ones]
  | succ n ih =>
    cases m with
    | zero => rw [weightWords_succ_zero, card_image_cons, ih]; simp
    | succ m =>
      rw [weightWords_succ_succ,
        Finset.card_union_of_disjoint (cons_images_disjoint _ _),
        card_image_cons, card_image_cons, ih, ih]
      simp [Nat.choose_succ_succ, Nat.add_comm]

/-- Equality of event counts, for an arbitrary adaptive full-query tree. -/
theorem event_card {s : Finset α} (T : Tree α s) (m : ℕ)
    (P : List Bool → Prop) [DecidablePred P] :
    ((s.powersetCard m).filter (fun A => P (encode T A))).card =
      ((weightWords s.card m).filter P).card := by
  apply Finset.card_bij (fun A _ => encode T A)
  · intro A hA
    obtain ⟨hA, hP⟩ := Finset.mem_filter.mp hA
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hA
    exact Finset.mem_filter.mpr
      ⟨mem_weightWords.mpr ⟨length_encode T A, by
        rw [ones_encode T hsub, hcard]⟩, hP⟩
  · intro A hA B hB heq
    exact encode_injective_on T
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).1
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hB).1).1 heq
  · intro bs hbs
    obtain ⟨hbs, hP⟩ := Finset.mem_filter.mp hbs
    obtain ⟨hlen, hones⟩ := mem_weightWords.mp hbs
    refine ⟨decode T bs, ?_, encode_decode T hlen⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      exact ⟨decode_subset T bs, by rw [card_decode T hlen, hones]⟩
    · simpa [encode_decode T hlen] using hP

/-- Counting words by the weights in two disjoint blocks. -/
theorem two_block_card (L R r s : ℕ) :
    ((binaryWords (L + R)).filter
      (fun bs => ones (bs.take L) = r ∧ ones (bs.drop L) = s)).card =
      L.choose r * R.choose s := by
  have hcard :
      ((weightWords L r) ×ˢ (weightWords R s)).card =
      ((binaryWords (L + R)).filter
        (fun bs => ones (bs.take L) = r ∧ ones (bs.drop L) = s)).card := by
    apply Finset.card_bij (fun ab _ => ab.1 ++ ab.2)
    · rintro ⟨a, b⟩ hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      obtain ⟨halen, haones⟩ := mem_weightWords.mp ha
      obtain ⟨hblen, hbones⟩ := mem_weightWords.mp hb
      apply Finset.mem_filter.mpr
      refine ⟨(mem_binaryWords _ _).2 ?_, ?_⟩
      · simp [halen, hblen]
      · have ht : (a ++ b).take L = a := by
          simpa [halen] using List.take_left a b
        have hd : (a ++ b).drop L = b := by
          simpa [halen] using List.drop_left a b
        simpa [ht, hd] using And.intro haones hbones
    · rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      obtain ⟨ha', hb'⟩ := Finset.mem_product.mp hab'
      have halen := (mem_weightWords.mp ha).1
      have ha'len := (mem_weightWords.mp ha').1
      have hfst := congrArg (List.take L) heq
      have hsnd := congrArg (List.drop L) heq
      have ht : (a ++ b).take L = a := by
        simpa [halen] using List.take_left a b
      have ht' : (a' ++ b').take L = a' := by
        simpa [ha'len] using List.take_left a' b'
      have hd : (a ++ b).drop L = b := by
        simpa [halen] using List.drop_left a b
      have hd' : (a' ++ b').drop L = b' := by
        simpa [ha'len] using List.drop_left a' b'
      apply Prod.ext
      · simpa [ht, ht'] using hfst
      · simpa [hd, hd'] using hsnd
    · intro bs hbs
      obtain ⟨hlen, hp⟩ := Finset.mem_filter.mp hbs
      have hlen := (mem_binaryWords _ _).1 hlen
      refine ⟨(bs.take L, bs.drop L), ?_, List.take_append_drop L bs⟩
      apply Finset.mem_product.mpr
      constructor
      · apply mem_weightWords.mpr
        refine ⟨?_, hp.1⟩
        simp [List.length_take, hlen]
      · apply mem_weightWords.mpr
        refine ⟨?_, hp.2⟩
        simp [List.length_drop, hlen]
  simpa using hcard.symm

/-- The exact hypergeometric numerator for a fixed prefix and a fixed total weight. -/
theorem prefix_weight_card (N m t r : ℕ) (ht : t ≤ N) (hr : r ≤ m) :
    ((weightWords N m).filter (fun bs => ones (bs.take t) = r)).card =
      t.choose r * (N - t).choose (m - r) := by
  have hsets :
      (weightWords N m).filter (fun bs => ones (bs.take t) = r) =
      (binaryWords (t + (N - t))).filter
        (fun bs => ones (bs.take t) = r ∧ ones (bs.drop t) = m - r) := by
    ext bs
    have hsum : ones bs = ones (bs.take t) + ones (bs.drop t) := by
      rw [← ones_append, List.take_append_drop]
    have hN : t + (N - t) = N := by omega
    simp only [Finset.mem_filter, mem_weightWords, mem_binaryWords, hN]
    omega
  rw [hsets, two_block_card]

/-- Full adaptive prefix distribution, with no independence assumption. -/
theorem adaptive_prefix_count {s : Finset α} (T : Tree α s)
    (m t r : ℕ) (ht : t ≤ s.card) (hr : r ≤ m) :
    ((s.powersetCard m).filter
      (fun A => ones ((encode T A).take t) = r)).card =
      t.choose r * (s.card - t).choose (m - r) := by
  rw [event_card T m (fun bs => ones (bs.take t) = r)]
  exact prefix_weight_card s.card m t r ht hr

end Reveal

/-! ## Finite Chebyshev, with no measure-theoretic prerequisites -/

namespace FiniteProbability

variable {α : Type*} [DecidableEq α]

def probability (Ω : Finset α) (P : α → Prop) [DecidablePred P] : ℝ :=
  ((Ω.filter P).card : ℝ) / (Ω.card : ℝ)

def average (Ω : Finset α) (X : α → ℝ) : ℝ :=
  (∑ ω ∈ Ω, X ω) / (Ω.card : ℝ)

theorem chebyshev (Ω : Finset α) (hΩ : Ω.Nonempty)
    (X : α → ℝ) (μ a : ℝ) (ha : 0 < a) :
    probability Ω (fun ω => a ≤ |X ω - μ|) ≤
      average Ω (fun ω => (X ω - μ) ^ 2) / a ^ 2 := by
  classical
  let B := Ω.filter (fun ω => a ≤ |X ω - μ|)
  have hcard : (0 : ℝ) < (Ω.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hΩ
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hpoint (ω : α) (hω : ω ∈ B) : a ^ 2 ≤ (X ω - μ) ^ 2 := by
    have hw := (Finset.mem_filter.mp hω).2
    have habs := abs_nonneg (X ω - μ)
    have hs := sq_abs (X ω - μ)
    nlinarith
  have hsum : (B.card : ℝ) * a ^ 2 ≤ ∑ ω ∈ Ω, (X ω - μ) ^ 2 := by
    calc
      (B.card : ℝ) * a ^ 2 = ∑ _ω ∈ B, a ^ 2 := by simp
      _ ≤ ∑ ω ∈ B, (X ω - μ) ^ 2 := Finset.sum_le_sum hpoint
      _ ≤ ∑ ω ∈ Ω, (X ω - μ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro ω _ _
          exact sq_nonneg _
  unfold probability average
  change (B.card : ℝ) / (Ω.card : ℝ) ≤
    ((∑ ω ∈ Ω, (X ω - μ) ^ 2) / (Ω.card : ℝ)) / a ^ 2
  apply (le_div_iff₀ ha2).2
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right hcard).2 hsum

theorem lower_tail (Ω : Finset α) (hΩ : Ω.Nonempty)
    (X : α → ℝ) (μ z : ℝ) (hz : z < μ) :
    probability Ω (fun ω => X ω ≤ z) ≤
      average Ω (fun ω => (X ω - μ) ^ 2) / (μ - z) ^ 2 := by
  classical
  have hsub : Ω.filter (fun ω => X ω ≤ z) ⊆
      Ω.filter (fun ω => μ - z ≤ |X ω - μ|) := by
    intro ω hω
    obtain ⟨hmem, hx⟩ := Finset.mem_filter.mp hω
    apply Finset.mem_filter.mpr
    refine ⟨hmem, ?_⟩
    have hneg : X ω - μ ≤ 0 := by linarith
    rw [abs_of_nonpos hneg]
    linarith
  calc
    probability Ω (fun ω => X ω ≤ z) ≤
        probability Ω (fun ω => μ - z ≤ |X ω - μ|) := by
      unfold probability
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub))
        (Nat.cast_nonneg _)
    _ ≤ _ := chebyshev Ω hΩ X μ (μ - z) (sub_pos.mpr hz)

end FiniteProbability

/-! ## Hypergeometric first and second moments, derived by binary-word counting -/

namespace Reveal

/-- The first raw moment numerator of the number of positive prefix answers. -/
def M1 (N m t : ℕ) : ℝ :=
  ∑ bs ∈ weightWords N m, (ones (bs.take t) : ℝ)

/-- The second factorial moment numerator. The subtraction is in `ℝ`. -/
def M2 (N m t : ℕ) : ℝ :=
  ∑ bs ∈ weightWords N m,
    (ones (bs.take t) : ℝ) * ((ones (bs.take t) : ℝ) - 1)

@[simp] theorem M1_time_zero (N m : ℕ) : M1 N m 0 = 0 := by simp [M1, ones]
@[simp] theorem M2_time_zero (N m : ℕ) : M2 N m 0 = 0 := by simp [M2, ones]

@[simp] theorem M1_weight_zero (N t : ℕ) : M1 N 0 t = 0 := by
  apply Finset.sum_eq_zero
  intro bs hbs
  have hweight := (mem_weightWords.mp hbs).2
  have ht := ones_take_le bs t
  have : ones (bs.take t) = 0 := by omega
  simp [this]

@[simp] theorem M2_weight_zero (N t : ℕ) : M2 N 0 t = 0 := by
  apply Finset.sum_eq_zero
  intro bs hbs
  have hweight := (mem_weightWords.mp hbs).2
  have ht := ones_take_le bs t
  have : ones (bs.take t) = 0 := by omega
  simp [this]

@[simp] theorem M2_weight_one (N t : ℕ) : M2 N 1 t = 0 := by
  apply Finset.sum_eq_zero
  intro bs hbs
  have hweight := (mem_weightWords.mp hbs).2
  have ht := ones_take_le bs t
  have : ones (bs.take t) = 0 ∨ ones (bs.take t) = 1 := by omega
  rcases this with h | h <;> simp [h]

theorem sum_image_cons_real (A : Finset (List Bool)) (b : Bool)
    (F : List Bool → ℝ) :
    (∑ bs ∈ A.image (List.cons b), F bs) = ∑ bs ∈ A, F (b :: bs) := by
  apply Finset.sum_image
  intro a ha a' ha' h
  exact (List.cons.inj h).2

theorem M1_succ (N m t : ℕ) :
    M1 (N + 1) (m + 1) (t + 1) =
      M1 N (m + 1) t + M1 N m t + (N.choose m : ℝ) := by
  unfold M1
  rw [weightWords_succ_succ, Finset.sum_union (cons_images_disjoint _ _),
    sum_image_cons_real, sum_image_cons_real]
  simp only [List.take_succ_cons, ones_false, ones_true, Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, weightWords_card]
  ring

theorem M2_succ (N m t : ℕ) :
    M2 (N + 1) (m + 1) (t + 1) =
      M2 N (m + 1) t + M2 N m t + 2 * M1 N m t := by
  unfold M2
  rw [weightWords_succ_succ, Finset.sum_union (cons_images_disjoint _ _),
    sum_image_cons_real, sum_image_cons_real]
  simp only [List.take_succ_cons, ones_false, ones_true, Nat.cast_add, Nat.cast_one]
  have hsum :
      (∑ bs ∈ weightWords N m,
        ((ones (bs.take t) : ℝ) + 1) * (((ones (bs.take t) : ℝ) + 1) - 1)) =
      (∑ bs ∈ weightWords N m,
        (ones (bs.take t) : ℝ) * ((ones (bs.take t) : ℝ) - 1)) +
        2 * M1 N m t := by
    simp only [M1, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro bs hbs
    ring
  rw [hsum]
  ring

/-- Counting one marked positive answer in the prefix. -/
theorem M1_formula (N m t : ℕ) (ht : t ≤ N) :
    M1 N (m + 1) t = (t : ℝ) * ((N - 1).choose m : ℝ) := by
  induction N generalizing m t with
  | zero =>
    have : t = 0 := by omega
    subst t
    simp
  | succ N ih =>
    cases t with
    | zero => simp
    | succ t =>
      have htt : t ≤ N := by omega
      rw [M1_succ]
      cases N with
      | zero =>
        have : t = 0 := by omega
        subst t
        simp
      | succ N =>
        rw [ih m t htt]
        cases m with
        | zero => simp [Nat.cast_add, Nat.cast_one]
        | succ m =>
          rw [ih m t htt]
          simp only [Nat.add_sub_cancel, Nat.succ_sub_one,
            Nat.choose_succ_succ, Nat.cast_add, Nat.cast_one]
          ring

/-- Counting two ordered marked positive answers in the prefix. -/
theorem M2_formula (N m t : ℕ) (ht : t ≤ N) :
    M2 N (m + 2) t =
      (t : ℝ) * ((t : ℝ) - 1) * ((N - 2).choose m : ℝ) := by
  induction N generalizing m t with
  | zero =>
    have : t = 0 := by omega
    subst t
    simp
  | succ N ih =>
    cases t with
    | zero => simp
    | succ t =>
      have htt : t ≤ N := by omega
      rw [show m + 2 = (m + 1) + 1 by omega, M2_succ]
      cases N with
      | zero =>
        have : t = 0 := by omega
        subst t
        simp
      | succ N =>
        cases N with
        | zero =>
          have ht01 : t = 0 ∨ t = 1 := by omega
          rcases ht01 with rfl | rfl
          · simp
          · rw [M1_formula 1 m 1 (by omega)]
            have hm2a : M2 1 (m + 2) 1 = 0 := by
              apply Finset.sum_eq_zero
              intro bs hbs
              have hx := ones_le_length (bs.take 1)
              have hlen : (bs.take 1).length ≤ 1 := by simp [List.length_take]
              have hx01 : ones (bs.take 1) = 0 ∨ ones (bs.take 1) = 1 := by omega
              rcases hx01 with h | h <;> simp [h]
            have hm2b : M2 1 (m + 1) 1 = 0 := by
              apply Finset.sum_eq_zero
              intro bs hbs
              have hx := ones_le_length (bs.take 1)
              have hlen : (bs.take 1).length ≤ 1 := by simp [List.length_take]
              have hx01 : ones (bs.take 1) = 0 ∨ ones (bs.take 1) = 1 := by omega
              rcases hx01 with h | h <;> simp [h]
            rw [hm2a, hm2b]
            norm_num
        | succ N =>
          rw [ih m t htt, M1_formula (N + 2) m t htt]
          have hn2 : N + 1 + 1 - 2 = N := by omega
          have hn3 : N + 1 + 1 + 1 - 2 = N + 1 := by omega
          simp only [hn2, hn3]
          cases m with
          | zero =>
            norm_num [M2_weight_one]
            <;> ring
          | succ m =>
            rw [show m + 1 + 1 = m + 2 by omega, ih m t htt]
            simp only [hn2, hn3, Nat.succ_sub_one, Nat.choose_succ_succ, Nat.cast_add, Nat.cast_one]
            ring

/-- The normalized prefix mean in the fixed-weight model. -/
def prefixMean (N m t : ℕ) : ℝ := (m : ℝ) * t / N

theorem M1_normalized {N m t : ℕ} (hN : 0 < N) (hm : m ≤ N) (ht : t ≤ N) :
    M1 N m t / (N.choose m : ℝ) = prefixMean N m t := by
  have hC : (N.choose m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hm)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  cases m with
  | zero => simp [prefixMean]
  | succ m =>
    rw [M1_formula N m t ht]
    have hchoose : (N : ℝ) * ((N - 1).choose m : ℝ) =
        (N.choose (m + 1) : ℝ) * (m + 1 : ℕ) := by
      obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
      exact_mod_cast Nat.add_one_mul_choose_eq N' m
    unfold prefixMean
    field_simp [hC, hNR]
    nlinarith [congrArg (fun x : ℝ => (t : ℝ) * x) hchoose]

/-- The normalized second factorial moment, including zero and one total edges. -/
theorem M2_normalized {N m t : ℕ} (hN : 2 ≤ N) (hm : m ≤ N) (ht : t ≤ N) :
    M2 N m t / (N.choose m : ℝ) =
      (m : ℝ) * ((m : ℝ) - 1) * t * ((t : ℝ) - 1) /
        ((N : ℝ) * ((N : ℝ) - 1)) := by
  have hC : (N.choose m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hm)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNm : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  cases m with
  | zero => simp
  | succ m =>
    cases m with
    | zero => simp
    | succ m =>
      rw [show m + 1 + 1 = m + 2 by omega, M2_formula N m t ht]
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 2 := ⟨N - 2, by omega⟩
      have h1 : ((N' : ℝ) + 1) * (N'.choose m : ℝ) =
          ((N' + 1).choose (m + 1) : ℝ) * ((m : ℝ) + 1) := by
        exact_mod_cast Nat.add_one_mul_choose_eq N' m
      have h2 : ((N' : ℝ) + 2) * ((N' + 1).choose (m + 1) : ℝ) =
          ((N' + 2).choose (m + 2) : ℝ) * ((m : ℝ) + 2) := by
        exact_mod_cast Nat.add_one_mul_choose_eq (N' + 1) (m + 1)
      have h12 : ((N' : ℝ) + 2) * ((N' : ℝ) + 1) * (N'.choose m : ℝ) =
          ((N' + 2).choose (m + 2) : ℝ) * ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
        nlinarith [congrArg (fun x : ℝ => ((N' : ℝ) + 2) * x) h1,
          congrArg (fun x : ℝ => x * ((m : ℝ) + 1)) h2]
      have hC' : ((N' + 2).choose (m + 2) : ℝ) ≠ 0 := by
        simpa [Nat.add_assoc] using hC
      have hD : ((N' : ℝ) + 2) * ((N' : ℝ) + 2 - 1) ≠ 0 := by
        have := Nat.cast_nonneg (α := ℝ) N'
        nlinarith
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_ofNat]
      apply (div_eq_div_iff hC' hD).mpr
      nlinarith [congrArg (fun x : ℝ => x * (t : ℝ) * ((t : ℝ) - 1)) h12]

/-- The variance is computed from counting, not postulated as a distribution fact. -/
theorem prefix_variance_formula {N m t : ℕ} (hN : 2 ≤ N)
    (hm : m ≤ N) (ht : t ≤ N) :
    FiniteProbability.average (weightWords N m)
        (fun bs => ((ones (bs.take t) : ℝ) - prefixMean N m t) ^ 2) =
      prefixMean N m t * (1 - (m : ℝ) / N) * ((N : ℝ) - t) / ((N : ℝ) - 1) := by
  let μ := prefixMean N m t
  let C : ℝ := N.choose m
  have hC : C ≠ 0 := by
    dsimp [C]
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hm)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNm : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hs :
      (∑ bs ∈ weightWords N m, ((ones (bs.take t) : ℝ) - μ) ^ 2) =
      M2 N m t + (1 - 2 * μ) * M1 N m t + μ ^ 2 * C := by
    calc
      (∑ bs ∈ weightWords N m, ((ones (bs.take t) : ℝ) - μ) ^ 2) =
          ∑ bs ∈ weightWords N m,
            ((ones (bs.take t) : ℝ) * ((ones (bs.take t) : ℝ) - 1) +
              (1 - 2 * μ) * (ones (bs.take t) : ℝ) + μ ^ 2) := by
        apply Finset.sum_congr rfl
        intro bs hbs
        ring
      _ = M2 N m t + (1 - 2 * μ) * M1 N m t + μ ^ 2 * C := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul, weightWords_card, M1, M2, C]
        ring
  have hfirst := M1_normalized (by omega : 0 < N) hm ht
  have hsecond := M2_normalized hN hm ht
  unfold FiniteProbability.average
  rw [weightWords_card]
  change (∑ bs ∈ weightWords N m, ((ones (bs.take t) : ℝ) - μ) ^ 2) / C = _
  rw [hs]
  have hdecomp :
      (M2 N m t + (1 - 2 * μ) * M1 N m t + μ ^ 2 * C) / C =
      M2 N m t / C + (1 - 2 * μ) * (M1 N m t / C) + μ ^ 2 := by
    field_simp [hC]
    <;> ring
  rw [hdecomp]
  change M2 N m t / (N.choose m : ℝ) +
    (1 - 2 * prefixMean N m t) * (M1 N m t / (N.choose m : ℝ)) +
      (prefixMean N m t) ^ 2 = _
  rw [hfirst, hsecond]
  unfold prefixMean
  field_simp [hNR, hNm]
  ring

/-- A deliberately coarse bound suffices: variance is at most the total weight. -/
theorem prefix_variance_le {N m t : ℕ} (hN : 2 ≤ N)
    (hm : m ≤ N) (ht : t ≤ N) :
    FiniteProbability.average (weightWords N m)
        (fun bs => ((ones (bs.take t) : ℝ) - prefixMean N m t) ^ 2) ≤ m := by
  rw [prefix_variance_formula hN hm ht]
  by_cases ht0 : t = 0
  · subst t
    simp [prefixMean]
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNm : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
  have htR : (t : ℝ) ≤ N := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hp0 : (0 : ℝ) ≤ (m : ℝ) / N := div_nonneg (by positivity) hNR.le
  have hp1 : (m : ℝ) / N ≤ 1 := (div_le_one hNR).2 hmR
  have hmu0 : 0 ≤ prefixMean N m t := by unfold prefixMean; positivity
  have hmu1 : prefixMean N m t ≤ m := by
    unfold prefixMean
    apply (div_le_iff₀ hNR).2
    exact mul_le_mul_of_nonneg_left htR (by positivity)
  have hratio0 : 0 ≤ ((N : ℝ) - t) / ((N : ℝ) - 1) :=
    div_nonneg (sub_nonneg.mpr htR) hNm.le
  have hratio1 : ((N : ℝ) - t) / ((N : ℝ) - 1) ≤ 1 := by
    apply (div_le_one hNm).2
    linarith
  have hmid0 : 0 ≤ prefixMean N m t * (1 - (m : ℝ) / N) :=
    mul_nonneg hmu0 (sub_nonneg.mpr hp1)
  have hmid1 : prefixMean N m t * (1 - (m : ℝ) / N) ≤ prefixMean N m t := by
    nlinarith
  calc
    prefixMean N m t * (1 - (m : ℝ) / N) * ((N : ℝ) - t) / ((N : ℝ) - 1) =
        (prefixMean N m t * (1 - (m : ℝ) / N)) *
          (((N : ℝ) - t) / ((N : ℝ) - 1)) := by ring
    _ ≤ prefixMean N m t * (1 - (m : ℝ) / N) := by nlinarith
    _ ≤ prefixMean N m t := hmid1
    _ ≤ m := hmu1

/-- The lower-tail estimate for a uniformly chosen word with exactly `m` ones. -/
theorem prefix_lower_tail {N m t : ℕ} (hN : 2 ≤ N)
    (hm : m ≤ N) (ht : t ≤ N) {z : ℝ} (hz : z < prefixMean N m t) :
    FiniteProbability.probability (weightWords N m)
      (fun bs => (ones (bs.take t) : ℝ) ≤ z) ≤
        (m : ℝ) / (prefixMean N m t - z) ^ 2 := by
  have hΩ : (weightWords N m).Nonempty := by
    apply Finset.card_pos.mp
    rw [weightWords_card]
    exact Nat.choose_pos hm
  calc
    _ ≤ _ := FiniteProbability.lower_tail (weightWords N m) hΩ
      (fun bs => (ones (bs.take t) : ℝ)) (prefixMean N m t) z hz
    _ ≤ _ := div_le_div_of_nonneg_right (prefix_variance_le hN hm ht)
      (sq_nonneg _)

end Reveal

/-! ## Certified depth-first search, instantiated as an adaptive query tree -/

namespace Reveal

/-- A full query tree exists on every finite coordinate set. -/
theorem exists_tree {α : Type*} [DecidableEq α] (s : Finset α) :
    Nonempty (Tree α s) := by
  classical
  induction s using Finset.strongInductionOn
  rename_i s ih
  by_cases hs : s = ∅
  · subst s
    exact ⟨.done⟩
  · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    obtain ⟨T⟩ := ih (s.erase e) (Finset.erase_ssubset he)
    exact ⟨.node e he T T⟩

end Reveal

namespace DFS

abbrev Edge (n : ℕ) := Finset (Fin n)

/-- An unoriented chain; injectivity of vertices is stated separately. -/
def Chain {n : ℕ} (P : Finset (Edge n)) : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | u :: v :: tail => {u, v} ∈ P ∧ Chain P (v :: tail)

@[simp] theorem chain_nil {n : ℕ} (P : Finset (Edge n)) : Chain P [] := trivial
@[simp] theorem chain_singleton {n : ℕ} (P : Finset (Edge n)) (u : Fin n) :
    Chain P [u] := trivial

theorem chain_mono {n : ℕ} {P Q : Finset (Edge n)} (h : P ⊆ Q)
    {l : List (Fin n)} (hl : Chain P l) : Chain Q l := by
  induction l with
  | nil => trivial
  | cons u l ih =>
    cases l with
    | nil => trivial
    | cons v tail => exact ⟨h hl.1, ih hl.2⟩

theorem chain_tail {n : ℕ} {P : Finset (Edge n)} {u : Fin n}
    {l : List (Fin n)} (h : Chain P (u :: l)) : Chain P l := by
  cases l with
  | nil => trivial
  | cons v tail => exact h.2

/-- All chains with distinct vertices are shorter than `K` vertices. -/
def NoLong {n : ℕ} (P : Finset (Edge n)) (K : ℝ) : Prop :=
  ∀ l : List (Fin n), l.Nodup → Chain P l → (l.length : ℝ) < K

/-- The chain-to-walk bridge preserves the exact support and hence the edge count. -/
theorem chain_walk {n : ℕ} {P : Finset (Edge n)}
    {u : Fin n} {l : List (Fin n)} (hnodup : (u :: l).Nodup)
    (hchain : Chain P (u :: l)) :
    ∃ v : Fin n, ∃ p : (toGraph P).Walk u v,
      p.support = u :: l ∧ p.IsPath := by
  induction l generalizing u with
  | nil =>
    refine ⟨u, .nil, rfl, ?_⟩
    exact SimpleGraph.Walk.IsPath.nil
  | cons v tail ih =>
    have hnd := List.nodup_cons.mp hnodup
    obtain ⟨w, p, hp, hpath⟩ := ih hnd.2 hchain.2
    have huv : u ≠ v := by
      intro heq
      subst u
      exact hnd.1 (by simp)
    let hadj : (toGraph P).Adj u v := ⟨huv, hchain.1⟩
    refine ⟨w, .cons hadj p, ?_, ?_⟩
    · simp [SimpleGraph.Walk.support_cons, hp]
    · apply SimpleGraph.Walk.IsPath.mk'
      simpa [SimpleGraph.Walk.support_cons, hp] using hnodup

/-- Absence of an edge-length `K-1` path bounds every distinct-vertex chain. -/
theorem noLong_of_not_hasPath {n : ℕ} {P : Finset (Edge n)} {K : ℝ}
    (hK : 0 < K) (h : ¬ HasPathAtLeast P (K - 1)) : NoLong P K := by
  intro l hnd hch
  cases l with
  | nil => simpa using hK
  | cons u tail =>
    obtain ⟨v, p, hp, hpath⟩ := chain_walk hnd hch
    have hlen : p.length + 1 = (u :: tail).length := by
      simpa [hp] using p.length_support.symm
    by_contra hbad
    have hlarge : K ≤ ((u :: tail).length : ℝ) := le_of_not_gt hbad
    have hlenR : (p.length : ℝ) + 1 = ((u :: tail).length : ℝ) := by
      exact_mod_cast hlen
    apply h
    exact ⟨u, v, p, hpath, by linarith⟩

structure State (n : ℕ) where
  S : Finset (Fin n)
  T : Finset (Fin n)
  U : List (Fin n)
  Q : Finset (Edge n)
  P : Finset (Edge n)

/-- Every field is maintained by the constructors below; none is an assumed
random-graph theorem. The cardinal identity is a convenient partition certificate. -/
structure Valid {n : ℕ} (z : State n) : Prop where
  qsub : z.Q ⊆ edgeUniverse n
  psub : z.P ⊆ z.Q
  nodup : z.U.Nodup
  st : ∀ v ∈ z.S, v ∉ z.T
  su : ∀ v ∈ z.S, v ∉ z.U
  tu : ∀ v ∈ z.T, v ∉ z.U
  size : z.S.card + z.T.card + z.U.length = n
  chain : Chain z.P z.U
  cut : ∀ v ∈ z.S, ∀ w ∈ z.T, {v, w} ∈ z.Q
  seen : z.P.card ≤ z.S.card + z.U.length

def initial (n : ℕ) : State n := ⟨∅, univ, [], ∅, ∅⟩

theorem initial_valid (n : ℕ) : Valid (initial n) := by
  constructor <;> simp [initial, Chain]

def remaining {n : ℕ} (z : State n) : Finset (Edge n) := edgeUniverse n \ z.Q

def root {n : ℕ} (z : State n) (v : Fin n) : State n :=
  { z with T := z.T.erase v, U := [v] }

def pop {n : ℕ} (z : State n) (v : Fin n) (tail : List (Fin n)) : State n :=
  { z with S := insert v z.S, U := tail }

def answerNo {n : ℕ} (z : State n) (e : Edge n) : State n :=
  { z with Q := insert e z.Q }

def answerYes {n : ℕ} (z : State n) (v w : Fin n) : State n :=
  { z with
    T := z.T.erase w
    U := w :: z.U
    Q := insert {v, w} z.Q
    P := insert {v, w} z.P }

theorem remaining_insert {n : ℕ} (z : State n) (e : Edge n) :
    edgeUniverse n \ insert e z.Q = (remaining z).erase e := by
  ext x
  simp [remaining, and_left_comm, and_assoc, and_comm]

theorem remaining_no {n : ℕ} (z : State n) (e : Edge n) :
    remaining (answerNo z e) = (remaining z).erase e := remaining_insert z e

theorem remaining_yes {n : ℕ} (z : State n) (v w : Fin n) :
    remaining (answerYes z v w) = (remaining z).erase {v, w} :=
  remaining_insert z {v, w}

/-- Distinct pairs in the finished/unseen cut correspond to distinct queries. -/
theorem cut_count {n : ℕ} {z : State n} (h : Valid z) :
    z.S.card * z.T.card ≤ z.Q.card := by
  let F : Fin n × Fin n → Edge n := fun vw => {vw.1, vw.2}
  have hinj : Set.InjOn F ↑(z.S ×ˢ z.T) := by
    rintro ⟨v, w⟩ hvw ⟨v', w'⟩ hvw' heq
    obtain ⟨hv, hw⟩ := Finset.mem_product.mp hvw
    obtain ⟨hv', hw'⟩ := Finset.mem_product.mp hvw'
    change ({v, w} : Edge n) = {v', w'} at heq
    have hvpair : v = v' ∨ v = w' := by
      have : v ∈ ({v', w'} : Edge n) := by
        rw [← heq]
        simp [F]
      simpa using this
    have heqv : v = v' := by
      rcases hvpair with hvv | hvw
      · exact hvv
      · subst v
        exact (h.st w' hv hw').elim
    have hwpair : w = v' ∨ w = w' := by
      have : w ∈ ({v', w'} : Edge n) := by
        rw [← heq]
        simp [F]
      simpa using this
    have heqw : w = w' := by
      rcases hwpair with hwv | hww
      · subst w
        exact (h.st v' hv' hw).elim
      · exact hww
    exact Prod.ext heqv heqw
  have hsub : (z.S ×ˢ z.T).image F ⊆ z.Q := by
    intro e he
    obtain ⟨⟨v, w⟩, hvw, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hv, hw⟩ := Finset.mem_product.mp hvw
    exact h.cut v hv w hw
  calc
    z.S.card * z.T.card = (z.S ×ˢ z.T).card := (Finset.card_product _ _).symm
    _ = ((z.S ×ˢ z.T).image F).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ z.Q.card := Finset.card_le_card hsub

theorem root_valid {n : ℕ} {z : State n} (h : Valid z)
    (hU : z.U = []) {v : Fin n} (hv : v ∈ z.T) : Valid (root z v) := by
  have ht : (z.T.erase v).card + 1 = z.T.card := by
    rw [Finset.card_erase_of_mem hv]
    have := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  constructor
  · exact h.qsub
  · exact h.psub
  · simp [root]
  · intro w hw hwt
    exact h.st w hw (Finset.mem_erase.mp hwt).2
  · intro w hw hwU
    have : w = v := by simpa [root] using hwU
    subst w
    exact h.st v hw hv
  · intro w hw hwU
    have : w = v := by simpa [root] using hwU
    subst w
    exact (Finset.mem_erase.mp hw).1 rfl
  · have hs := h.size
    simp only [hU, List.length_nil] at hs
    simp only [root, List.length_singleton]
    omega
  · trivial
  · intro w hw x hx
    exact h.cut w hw x (Finset.mem_erase.mp hx).2
  · have hs := h.seen
    simp only [hU, List.length_nil, Nat.add_zero] at hs
    simp only [root, List.length_singleton]
    omega

theorem pop_valid {n : ℕ} {z : State n} (h : Valid z)
    {v : Fin n} {tail : List (Fin n)} (hU : z.U = v :: tail)
    (hall : ∀ w ∈ z.T, {v, w} ∈ z.Q) : Valid (pop z v tail) := by
  have hvS : v ∉ z.S := by
    intro hv
    exact h.su v hv (by simp [hU])
  have hvT : v ∉ z.T := by
    intro hv
    exact h.tu v hv (by simp [hU])
  have hnd : v ∉ tail ∧ tail.Nodup := by
    simpa [hU] using h.nodup
  have hSc : (insert v z.S).card = z.S.card + 1 := Finset.card_insert_of_notMem hvS
  constructor
  · exact h.qsub
  · exact h.psub
  · exact hnd.2
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hvT
    · exact h.st w hw
  · intro w hw hwt
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hnd.1 hwt
    · exact h.su w hw (by simpa only [hU, List.mem_cons] using Or.inr (show w ∈ tail from hwt))
  · intro w hw hwt
    exact h.tu w hw (by simpa only [hU, List.mem_cons] using Or.inr (show w ∈ tail from hwt))
  · have hs := h.size
    simp only [hU, List.length_cons] at hs
    simp only [pop, hSc]
    omega
  · change Chain z.P tail
    apply chain_tail
    simpa [hU] using h.chain
  · intro w hw x hx
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hall x hx
    · exact h.cut w hw x hx
  · have hs := h.seen
    simp only [hU, List.length_cons] at hs
    simp only [pop, hSc]
    omega

theorem no_valid {n : ℕ} {z : State n} (h : Valid z)
    {e : Edge n} (he : e ∈ edgeUniverse n) : Valid (answerNo z e) := by
  constructor
  · exact Finset.insert_subset_iff.mpr ⟨he, h.qsub⟩
  · exact h.psub.trans (Finset.subset_insert _ _)
  · exact h.nodup
  · exact h.st
  · exact h.su
  · exact h.tu
  · exact h.size
  · exact h.chain
  · intro v hv w hw
    exact Finset.mem_insert_of_mem (h.cut v hv w hw)
  · exact h.seen

theorem yes_valid {n : ℕ} {z : State n} (h : Valid z)
    {v w : Fin n} {tail : List (Fin n)} (hU : z.U = v :: tail)
    (hw : w ∈ z.T) (hfresh : {v, w} ∉ z.Q) : Valid (answerYes z v w) := by
  have hwU : w ∉ z.U := h.tu w hw
  have hwS : w ∉ z.S := by intro hs; exact h.st w hs hw
  have hvw : v ≠ w := by
    intro heq
    subst w
    exact hwU (by simp [hU])
  have he : ({v, w} : Edge n) ∈ edgeUniverse n := by
    apply mem_edgeUniverse.mpr
    simp [hvw]
  have hfreshP : {v, w} ∉ z.P := by
    intro heP
    exact hfresh (h.psub heP)
  have hTc : (z.T.erase w).card + 1 = z.T.card := by
    rw [Finset.card_erase_of_mem hw]
    have := Finset.card_pos.mpr ⟨w, hw⟩
    omega
  have hPc : (insert {v, w} z.P).card = z.P.card + 1 :=
    Finset.card_insert_of_notMem hfreshP
  constructor
  · exact Finset.insert_subset_iff.mpr ⟨he, h.qsub⟩
  · exact Finset.insert_subset_insert _ h.psub
  · simpa [answerYes] using List.nodup_cons.mpr ⟨hwU, h.nodup⟩
  · intro x hx hxt
    exact h.st x hx (Finset.mem_erase.mp hxt).2
  · intro x hx hxU
    rcases List.mem_cons.mp hxU with rfl | hxU
    · exact hwS hx
    · exact h.su x hx hxU
  · intro x hx hxU
    rcases List.mem_cons.mp hxU with rfl | hxU
    · exact (Finset.mem_erase.mp hx).1 rfl
    · exact h.tu x (Finset.mem_erase.mp hx).2 hxU
  · have hs := h.size
    simp only [answerYes, List.length_cons]
    omega
  · change Chain (insert {v, w} z.P) (w :: z.U)
    rw [hU]
    constructor
    · simp [Finset.pair_comm]
    · apply chain_mono (Finset.subset_insert _ _)
      simpa [hU] using h.chain
  · intro x hx y hy
    exact Finset.mem_insert_of_mem (h.cut x hx y (Finset.mem_erase.mp hy).2)
  · have hs := h.seen
    simp only [answerYes, List.length_cons, hPc]
    omega

/-- The only parameters in this certificate are elementary real inequalities.
The DFS query tree satisfying the conclusion is constructed in the proof. -/
structure NumericCertificate (n q r : ℕ) (K X : ℝ) : Prop where
  kpos : 0 < K
  rpos : 0 < r
  room : (r : ℝ) + K ≤ n
  crossing : ∀ u : ℝ, 0 ≤ u → u < K →
    (q : ℝ) < (r : ℝ) * ((n : ℝ) - r - u)
  terminal : ∀ s u : ℝ, 0 ≤ s → 0 ≤ u → s < r → u < K →
    s * ((n : ℝ) - s - u) ≤ q → s + u < X

/-- A DFS strategy is built by well-founded recursion. Free root/pop operations
and fresh yes/no queries all decrease `q-Q.card + 2*T.card + U.length`.
On every graph without a long path, its first `q` answers have fewer than `X` ones. -/
theorem exists_tree_from_state {n q r : ℕ} {K X : ℝ}
    (hc : NumericCertificate n q r K X) (z : State n) (hz : Valid z)
    (hqz : z.Q.card ≤ q) (hsz : z.S.card ≤ r) :
    ∃ R : Reveal.Tree (Edge n) (remaining z),
      ∀ A : Finset (Edge n), A ⊆ remaining z → NoLong (z.P ∪ A) K →
        (z.P.card : ℝ) +
          (Reveal.ones ((Reveal.encode R A).take (q - z.Q.card)) : ℝ) < X := by
  classical
  generalize hmeasure : q - z.Q.card + 2 * z.T.card + z.U.length = w
  induction w using Nat.strong_induction_on generalizing z with
  | h w ih =>
    have hlength (A : Finset (Edge n)) (hbad : NoLong (z.P ∪ A) K) :
        (z.U.length : ℝ) < K :=
      hbad z.U hz.nodup (chain_mono (Finset.subset_union_left) hz.chain)
    have hsizeR : (z.S.card : ℝ) + z.T.card + z.U.length = n := by
      exact_mod_cast hz.size
    have hcutR : (z.S.card : ℝ) * z.T.card ≤ z.Q.card := by
      exact_mod_cast cut_count hz
    by_cases hsr : z.S.card = r
    · obtain ⟨R⟩ := Reveal.exists_tree (remaining z)
      refine ⟨R, ?_⟩
      intro A hA hbad
      have hu := hlength A hbad
      have hh := hc.crossing (z.U.length : ℝ) (by positivity) hu
      have hqq : (z.Q.card : ℝ) ≤ q := by exact_mod_cast hqz
      have hss : (z.S.card : ℝ) = r := by exact_mod_cast hsr
      have htval : (z.T.card : ℝ) = (n : ℝ) - r - z.U.length := by linarith
      rw [hss, htval] at hcutR
      linarith
    have hslt : z.S.card < r := by omega
    by_cases hqq : z.Q.card = q
    · obtain ⟨R⟩ := Reveal.exists_tree (remaining z)
      refine ⟨R, ?_⟩
      intro A hA hbad
      have hu := hlength A hbad
      have hseen : (z.P.card : ℝ) ≤ z.S.card + z.U.length := by
        exact_mod_cast hz.seen
      have hsc : (z.S.card : ℝ) < r := by exact_mod_cast hslt
      have hcut : (z.S.card : ℝ) * ((n : ℝ) - z.S.card - z.U.length) ≤ q := by
        have hqR : (z.Q.card : ℝ) = q := by exact_mod_cast hqq
        have htval : (n : ℝ) - z.S.card - z.U.length = (z.T.card : ℝ) := by
          linarith
        rw [htval]
        simpa [hqR] using hcutR
      have ht := hc.terminal (z.S.card : ℝ) (z.U.length : ℝ)
        (by positivity) (by positivity) hsc hu hcut
      simpa [hqq, Reveal.ones] using lt_of_le_of_lt hseen ht
    have hqlt : z.Q.card < q := by omega
    cases hU : z.U with
    | nil =>
      have hT : z.T.Nonempty := by
        by_contra hnone
        have hTe : z.T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
        have hsn : z.S.card = n := by simpa [hU, hTe] using hz.size
        have hrn : (r : ℝ) < n := by linarith [hc.room, hc.kpos]
        have hsrR : (z.S.card : ℝ) < r := by exact_mod_cast hslt
        have hsnR : (z.S.card : ℝ) = n := by exact_mod_cast hsn
        linarith
      obtain ⟨v, hv⟩ := hT
      have hnew := root_valid hz hU hv
      have htc : (z.T.erase v).card + 1 = z.T.card := by
        rw [Finset.card_erase_of_mem hv]
        have := Finset.card_pos.mpr ⟨v, hv⟩
        omega
      have hwlt : q - (root z v).Q.card + 2 * (root z v).T.card +
          (root z v).U.length < w := by
        simp only [root, List.length_singleton]
        have : z.U.length = 0 := by simp [hU]
        omega
      obtain ⟨R, hR⟩ := ih _ hwlt (root z v) hnew hqz hsz rfl
      exact ⟨R, hR⟩
    | cons v tail =>
      by_cases hex : ∃ w ∈ z.T, ({v, w} : Edge n) ∉ z.Q
      · obtain ⟨v', hv', hfresh⟩ := hex
        let e : Edge n := {v, v'}
        have hvv' : v ≠ v' := by
          intro heq
          subst v'
          exact hz.tu v hv' (by simp [hU])
        have heE : e ∈ edgeUniverse n := by
          apply mem_edgeUniverse.mpr
          simp [e, hvv']
        have heR : e ∈ remaining z := Finset.mem_sdiff.mpr ⟨heE, hfresh⟩
        have heP : e ∉ z.P := by intro hp; exact hfresh (hz.psub hp)
        have hQcard : (insert e z.Q).card = z.Q.card + 1 :=
          Finset.card_insert_of_notMem hfresh
        have hPcard : (insert e z.P).card = z.P.card + 1 :=
          Finset.card_insert_of_notMem heP
        have hTcard : (z.T.erase v').card + 1 = z.T.card := by
          rw [Finset.card_erase_of_mem hv']
          have := Finset.card_pos.mpr ⟨v', hv'⟩
          omega
        have hno := no_valid hz heE
        have hyes := yes_valid hz hU hv' hfresh
        have hwn : q - (answerNo z e).Q.card + 2 * (answerNo z e).T.card +
            (answerNo z e).U.length < w := by
          simp only [answerNo, hQcard]
          omega
        have hwy : q - (answerYes z v v').Q.card +
            2 * (answerYes z v v').T.card + (answerYes z v v').U.length < w := by
          change q - (insert e z.Q).card + 2 * (z.T.erase v').card +
            (v' :: z.U).length < w
          rw [hQcard, List.length_cons]
          omega
        have hqno : (answerNo z e).Q.card ≤ q := by
          change (insert e z.Q).card ≤ q
          rw [hQcard]
          omega
        have hqyes : (answerYes z v v').Q.card ≤ q := hqno
        have hRn0 := ih _ hwn (answerNo z e) hno hqno hsz rfl
        have hRy0 := ih _ hwy (answerYes z v v') hyes hqyes hsz rfl
        have hnex : ∃ Rn : Reveal.Tree (Edge n) ((remaining z).erase e),
            ∀ A : Finset (Edge n), A ⊆ (remaining z).erase e →
              NoLong (z.P ∪ A) K →
              (z.P.card : ℝ) +
                (Reveal.ones ((Reveal.encode Rn A).take (q - (z.Q.card + 1))) : ℝ) < X := by
          rw [remaining_no] at hRn0
          simpa only [answerNo, hQcard] using hRn0
        have hyex : ∃ Ry : Reveal.Tree (Edge n) ((remaining z).erase e),
            ∀ A : Finset (Edge n), A ⊆ (remaining z).erase e →
              NoLong (insert e z.P ∪ A) K →
              ((z.P.card + 1 : ℕ) : ℝ) +
                (Reveal.ones ((Reveal.encode Ry A).take (q - (z.Q.card + 1))) : ℝ) < X := by
          rw [remaining_yes] at hRy0
          simpa only [answerYes, e, hQcard, hPcard] using hRy0
        obtain ⟨Rn, hRn⟩ := hnex
        obtain ⟨Ry, hRy⟩ := hyex
        refine ⟨.node e heR Rn Ry, ?_⟩
        intro A hA hbad
        have hbudget : q - z.Q.card = (q - (z.Q.card + 1)) + 1 := by omega
        by_cases hea : e ∈ A
        · have hsub : A.erase e ⊆ (remaining z).erase e :=
            Finset.erase_subset_erase e hA
          have hG : insert e z.P ∪ A.erase e = z.P ∪ A := by
            ext x
            by_cases hxe : x = e <;> simp [hxe, hea]
          have hh := hRy (A.erase e) hsub (by simpa [hG] using hbad)
          simp only [Reveal.encode, if_pos hea, hbudget, List.take_succ_cons,
            Reveal.ones, Nat.cast_add, Nat.cast_one]
          push_cast at hh
          linarith
        · have hsub : A ⊆ (remaining z).erase e := by
            intro x hx
            exact Finset.mem_erase.mpr ⟨by intro hxe; subst x; exact hea hx, hA hx⟩
          have hh := hRn A hsub hbad
          simpa [Reveal.encode, hea, hbudget, Reveal.ones] using hh
      · have hall : ∀ w ∈ z.T, {v, w} ∈ z.Q := by
          intro w hw
          by_contra he
          exact hex ⟨w, hw, he⟩
        have hp := pop_valid hz hU hall
        have hvS : v ∉ z.S := by
          intro hv
          exact hz.su v hv (by simp [hU])
        have hScard : (insert v z.S).card = z.S.card + 1 :=
          Finset.card_insert_of_notMem hvS
        have hsnew : (pop z v tail).S.card ≤ r := by
          simp only [pop, hScard]
          omega
        have hwlt : q - (pop z v tail).Q.card +
            2 * (pop z v tail).T.card + (pop z v tail).U.length < w := by
          simp only [pop]
          have hlen : z.U.length = tail.length + 1 := by simp [hU]
          omega
        obtain ⟨R, hR⟩ := ih _ hwlt (pop z v tail) hp hqz hsnew rfl
        exact ⟨R, hR⟩

/-- The graph-specific adaptive transcript bound, with every DFS invariant proved. -/
theorem exists_transcript_tree {n q r : ℕ} {K X : ℝ}
    (hc : NumericCertificate n q r K X) :
    ∃ R : Reveal.Tree (Edge n) (edgeUniverse n),
      ∀ A : Finset (Edge n), A ⊆ edgeUniverse n → NoLong A K →
        (Reveal.ones ((Reveal.encode R A).take q) : ℝ) < X := by
  have hR := exists_tree_from_state hc (initial n) (initial_valid n)
    (by simp [initial]) (by simp [initial])
  have hrem : remaining (initial n) = edgeUniverse n := by simp [remaining, initial]
  rw [hrem] at hR
  simpa only [initial, Finset.empty_union, Finset.card_empty, Nat.sub_zero,
    Nat.cast_zero, zero_add] using hR

end DFS

/-! ## Deterministic numerical consequences of the DFS invariants

These algebraic certificates are instantiated below and supplied to the
graph-specific DFS construction; they are not final-theorem assumptions.
-/

/-- Crossing one third of the finished vertices requires too many queries if
all stacks have fewer than one sixteenth of the vertices. -/
theorem small_crossing_impossible {n r u q : ℝ}
    (hn : 0 < n) (hrlo : n / 4 ≤ r) (hrhi : r ≤ n / 3)
    (hu : u ≤ n / 16) (hcut : r * (n - r - u) ≤ q)
    (hq : q ≤ n ^ 2 / 16) : False := by
  have hr0 : 0 ≤ r := by linarith
  have ht : n / 2 ≤ n - r - u := by linarith
  have hp : n ^ 2 / 8 ≤ r * (n - r - u) := by
    calc
      n ^ 2 / 8 = (n / 4) * (n / 2) := by ring
      _ ≤ r * (n - r - u) :=
        mul_le_mul hrlo ht (by positivity) hr0
  have hsq : 0 < n ^ 2 := sq_pos_of_pos hn
  linarith

/-- The supercritical DFS calculation, in normalized real variables. -/
theorem small_stack_bound {b n s u q : ℝ}
    (hb : 0 < b) (hbhi : b ≤ 1 / 4) (hn : 0 < n)
    (hs0 : 0 ≤ s) (hshi : s ≤ n / 3)
    (hseen : (b - b ^ 2) * n ≤ s + u)
    (hcut : s * (n - s - u) ≤ q)
    (hq : q ≤ b * (1 - 4 * b) * n ^ 2) :
    b ^ 2 * n ≤ u := by
  by_contra hu
  have hult : u < b ^ 2 * n := lt_of_not_ge hu
  have hb2 : b ^ 2 ≤ b / 4 := by nlinarith
  have hb2hi : b ^ 2 ≤ 1 / 16 := by nlinarith
  let d := (b - 2 * b ^ 2) * n
  have hd0 : 0 < d := by
    dsimp [d]
    apply mul_pos
    · nlinarith
    · exact hn
  have hds : d ≤ s := by dsimp [d]; nlinarith
  have hdb : d ≤ b * n := by
    dsimp [d]
    exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg b]) hn.le
  have hbn : b * n ≤ n / 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hbhi hn.le]
  have hb2n : b ^ 2 * n ≤ n / 16 := by
    nlinarith [mul_le_mul_of_nonneg_right hb2hi hn.le]
  have hfac : 0 ≤ n - b ^ 2 * n - s - d := by linarith
  have hmono : d * (n - d - b ^ 2 * n) ≤ s * (n - s - b ^ 2 * n) := by
    have hm := mul_nonneg (sub_nonneg.mpr hds) hfac
    nlinarith
  have hucomp : s * (n - s - b ^ 2 * n) ≤ s * (n - s - u) := by
    apply mul_le_mul_of_nonneg_left _ hs0
    linarith
  have hpoly : 0 < 1 + 3 * b - 2 * b ^ 2 := by nlinarith
  have hgap : 0 < b ^ 2 * (1 + 3 * b - 2 * b ^ 2) * n ^ 2 := by
    exact mul_pos (mul_pos (sq_pos_of_pos hb) hpoly) (sq_pos_of_pos hn)
  have hid :
      d * (n - d - b ^ 2 * n) - b * (1 - 4 * b) * n ^ 2 =
        b ^ 2 * (1 + 3 * b - 2 * b ^ 2) * n ^ 2 := by
    dsimp [d]
    ring
  linarith

/-- The near-spanning analogue of the crossing calculation. -/
theorem large_crossing_impossible {δ n r u q : ℝ}
    (hδ : 0 < δ) (hn : 0 < n)
    (hrlo : δ * n / 4 ≤ r) (hrhi : r ≤ δ * n / 2)
    (hu : u ≤ (1 - δ) * n)
    (hcut : r * (n - r - u) ≤ q)
    (hq : q ≤ δ ^ 2 * n ^ 2 / 16) : False := by
  have hd : 0 < δ * n := mul_pos hδ hn
  have hr0 : 0 ≤ r := by linarith
  have ht : δ * n / 2 ≤ n - r - u := by nlinarith
  have hp : δ ^ 2 * n ^ 2 / 8 ≤ r * (n - r - u) := by
    calc
      δ ^ 2 * n ^ 2 / 8 = (δ * n / 4) * (δ * n / 2) := by ring
      _ ≤ r * (n - r - u) :=
        mul_le_mul hrlo ht (by positivity) hr0
  have hprod : 0 < δ ^ 2 * n ^ 2 :=
    mul_pos (sq_pos_of_pos hδ) (sq_pos_of_pos hn)
  linarith

theorem large_seen_lt {δ n r s u x : ℝ}
    (hδ : 0 < δ) (hn : 0 < n) (hr : r ≤ δ * n / 2)
    (hs : s < r) (hu : u < (1 - δ) * n) (hx : x ≤ s + u) :
    x < n := by
  have hd : 0 < δ * n := mul_pos hδ hn
  nlinarith

/-! ## An explicit coefficient satisfying both endpoint requirements -/

def b (c : ℝ) : ℝ := (2 * c - 1) / (8 * c)
def a (c : ℝ) : ℝ := b c * (1 - 4 * b c)
def smallCoefficient (c : ℝ) : ℝ := (b c) ^ 2 / 2
def largeCoefficient (c : ℝ) : ℝ := 1 - 8 / Real.sqrt c
def coefficient (c : ℝ) : ℝ := max (smallCoefficient c) (largeCoefficient c)

theorem b_pos {c : ℝ} (hc : 1 / 2 < c) : 0 < b c := by
  unfold b
  apply div_pos <;> linarith

theorem b_lt_quarter {c : ℝ} (hc : 1 / 2 < c) : b c < 1 / 4 := by
  have hd : 0 < 8 * c := by linarith
  unfold b
  apply (div_lt_iff₀ hd).2
  linarith

theorem a_pos {c : ℝ} (hc : 1 / 2 < c) : 0 < a c := by
  unfold a
  apply mul_pos (b_pos hc)
  have := b_lt_quarter hc
  linarith

theorem a_le_sixteenth (c : ℝ) : a c ≤ 1 / 16 := by
  unfold a
  nlinarith [sq_nonneg (b c - 1 / 8)]

theorem b_inverse_form {c : ℝ} (hc : c ≠ 0) :
    b c = 1 / 4 - (1 / 8) * c⁻¹ := by
  unfold b
  field_simp [hc]
  <;> ring

theorem mean_identity {c : ℝ} (hc : 1 / 2 < c) :
    2 * c * a c = b c := by
  have hc0 : c ≠ 0 := ne_of_gt (by linarith : 0 < c)
  unfold a b
  field_simp [hc0]
  <;> ring

theorem coefficient_pos {c : ℝ} (hc : 1 / 2 < c) : 0 < coefficient c := by
  have h : 0 < smallCoefficient c := by
    unfold smallCoefficient
    exact div_pos (sq_pos_of_pos (b_pos hc)) (by norm_num)
  exact h.trans_le (le_max_left _ _)

theorem coefficient_lt_one {c : ℝ} (hc : 1 / 2 < c) : coefficient c < 1 := by
  unfold coefficient
  apply max_lt_iff.mpr
  constructor
  · have hb := b_pos hc
    have hbhi := b_lt_quarter hc
    unfold smallCoefficient
    nlinarith
  · have hc0 : 0 < c := by linarith
    have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
    have hd : 0 < 8 / Real.sqrt c := div_pos (by norm_num) hs
    unfold largeCoefficient
    linarith

theorem large_positive_implies_gt64 {c : ℝ} (hc : 1 / 2 < c)
    (h : 0 < largeCoefficient c) : 64 < c := by
  have hc0 : 0 < c := by linarith
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
  have hd : 8 / Real.sqrt c < 1 := by unfold largeCoefficient at h; linarith
  have h8 : 8 < Real.sqrt c := by
    have := (div_lt_iff₀ hs).1 hd
    simpa using this
  have hsq := Real.sq_sqrt hc0.le
  nlinarith

theorem b_tendsto_half : Tendsto b (𝓝 (1 / 2 : ℝ)) (𝓝 0) := by
  change Tendsto (fun c : ℝ => (2 * c - 1) / (8 * c)) _ _
  have hnum : Tendsto (fun c : ℝ => 2 * c - 1)
      (𝓝 (1 / 2 : ℝ)) (𝓝 (2 * (1 / 2 : ℝ) - 1)) :=
    (tendsto_const_nhds.mul tendsto_id).sub tendsto_const_nhds
  have hden : Tendsto (fun c : ℝ => 8 * c)
      (𝓝 (1 / 2 : ℝ)) (𝓝 (8 * (1 / 2 : ℝ))) :=
    tendsto_const_nhds.mul tendsto_id
  convert hnum.div hden (by norm_num : (8 : ℝ) * (1 / 2) ≠ 0) using 1 <;>
    first | rfl | norm_num

theorem coefficient_tendsto_half :
    Tendsto coefficient (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2))) (𝓝 0) := by
  have hsmall : Tendsto smallCoefficient (𝓝 (1 / 2 : ℝ)) (𝓝 0) := by
    change Tendsto (fun c => (b c) ^ 2 / 2) _ _
    simpa [smallCoefficient] using
      (b_tendsto_half.pow 2).div_const (2 : ℝ)
  have hsqrt : Tendsto Real.sqrt (𝓝 (1 / 2 : ℝ)) (𝓝 (Real.sqrt (1 / 2 : ℝ))) :=
    Real.continuous_sqrt.continuousAt.tendsto
  have hspos : 0 < Real.sqrt (1 / 2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hlarge : Tendsto largeCoefficient (𝓝 (1 / 2 : ℝ))
      (𝓝 (1 - 8 / Real.sqrt (1 / 2 : ℝ))) := by
    exact tendsto_const_nhds.sub
      (tendsto_const_nhds.div hsqrt (ne_of_gt hspos))
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hslt : Real.sqrt (1 / 2 : ℝ) < 8 := by nlinarith
  have hneg : 1 - 8 / Real.sqrt (1 / 2 : ℝ) ≤ 0 := by
    have hd : (1 : ℝ) < 8 / Real.sqrt (1 / 2 : ℝ) :=
      (lt_div_iff₀ hspos).2 (by simpa using hslt)
    linarith
  have hh := hsmall.max hlarge
  have hfull : Tendsto coefficient (𝓝 (1 / 2 : ℝ)) (𝓝 0) := by
    change Tendsto (fun c => max (smallCoefficient c) (largeCoefficient c)) _ _
    simpa only [max_eq_left hneg] using hh
  exact hfull.mono_left nhdsWithin_le_nhds

theorem b_tendsto_infty : Tendsto b atTop (𝓝 (1 / 4 : ℝ)) := by
  have hinv : Tendsto (fun c : ℝ => c⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hmodel : Tendsto (fun c : ℝ => 1 / 4 - (1 / 8) * c⁻¹)
      atTop (𝓝 (1 / 4 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
  apply hmodel.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  exact (b_inverse_form (ne_of_gt hc)).symm

theorem coefficient_tendsto_infty : Tendsto coefficient atTop (𝓝 (1 : ℝ)) := by
  have hsmall : Tendsto smallCoefficient atTop (𝓝 (1 / 32 : ℝ)) := by
    change Tendsto (fun c => (b c) ^ 2 / 2) _ _
    convert (b_tendsto_infty.pow 2).div_const (2 : ℝ) using 1 <;>
      norm_num [smallCoefficient]
  have hs : Tendsto Real.sqrt atTop atTop := Real.tendsto_sqrt_atTop
  have hinv : Tendsto (fun c : ℝ => (Real.sqrt c)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hs
  have hlarge : Tendsto largeCoefficient atTop (𝓝 (1 : ℝ)) := by
    change Tendsto (fun c => 1 - 8 / Real.sqrt c) _ _
    simpa [largeCoefficient, div_eq_mul_inv] using
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
  have hh := hsmall.max hlarge
  change Tendsto (fun c => max (smallCoefficient c) (largeCoefficient c)) _ _
  norm_num at hh ⊢
  exact hh

/-- All deterministic analytic properties of the chosen coefficient.
This theorem intentionally makes no claim about random graphs. -/
theorem coefficient_properties :
    (∀ c : ℝ, 1 / 2 < c → 0 < coefficient c ∧ coefficient c < 1) ∧
    Tendsto coefficient (nhdsWithin (1 / 2) (Set.Ioi (1 / 2))) (𝓝 0) ∧
    Tendsto coefficient atTop (𝓝 1) := by
  exact ⟨fun _ hc => ⟨coefficient_pos hc, coefficient_lt_one hc⟩,
    coefficient_tendsto_half, coefficient_tendsto_infty⟩

#print axioms Reveal.fixedWeightEquiv
#print axioms Reveal.adaptive_prefix_count
#print axioms FiniteProbability.chebyshev
#print axioms small_stack_bound
#print axioms large_crossing_impossible
#print axioms coefficient_properties

/-! ## From the certified DFS tree to the actual uniform graph probability -/

theorem hasPath_mono {n : ℕ} {A : Finset (Finset (Fin n))} {x y : ℝ}
    (hxy : x ≤ y) (hy : HasPathAtLeast A y) : HasPathAtLeast A x := by
  obtain ⟨u, v, p, hp, hlen⟩ := hy
  exact ⟨u, v, p, hp, hxy.trans hlen⟩

namespace FiniteProbability

theorem probability_complement {α : Type*} [DecidableEq α]
    (Ω : Finset α) (hΩ : Ω.Nonempty) (P : α → Prop) [DecidablePred P] :
    probability Ω (fun a => ¬ P a) = 1 - probability Ω P := by
  classical
  have hc : (Ω.filter P).card + (Ω.filter (fun a => ¬ P a)).card = Ω.card := by
    clear hΩ
    induction Ω using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      by_cases hp : P a <;> simp [Finset.filter_insert, ha, hp] <;> omega
  have hC : (Ω.card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Finset.card_pos.mpr hΩ)
  have hcR : ((Ω.filter P).card : ℝ) + ((Ω.filter (fun a => ¬ P a)).card : ℝ) =
      (Ω.card : ℝ) := by exact_mod_cast hc
  unfold probability
  field_simp [hC]
  linarith

end FiniteProbability

/-- A finite theorem about the exact uniform `m`-edge model.
The hypotheses are numerical, and the graph exploration and its law are proved above. -/
theorem finite_path_failure_bound {n m q r : ℕ} {K X ell : ℝ}
    (hc : DFS.NumericCertificate n q r K X)
    (hE : 2 ≤ n.choose 2) (hm : m ≤ n.choose 2) (hq : q ≤ n.choose 2)
    (hmean : X < Reveal.prefixMean (n.choose 2) m q) (hell : ell ≤ K - 1) :
    1 - pathProbability n m ell ≤
      (m : ℝ) / (Reveal.prefixMean (n.choose 2) m q - X) ^ 2 := by
  classical
  obtain ⟨R, hR⟩ := DFS.exists_transcript_tree hc
  have hΩ : (graphFamily n m).Nonempty := by
    apply Finset.card_pos.mp
    rw [graphFamily_card]
    exact Nat.choose_pos hm
  have hsub :
      (graphFamily n m).filter (fun A => ¬ HasPathAtLeast A ell) ⊆
      (graphFamily n m).filter
        (fun A => (Reveal.ones ((Reveal.encode R A).take q) : ℝ) ≤ X) := by
    intro A hA
    obtain ⟨hmem, hbad⟩ := Finset.mem_filter.mp hA
    have hsubset := (mem_graphFamily.mp hmem).1
    have hbad' : ¬ HasPathAtLeast A (K - 1) := by
      intro hpath
      exact hbad (hasPath_mono hell hpath)
    have hno := DFS.noLong_of_not_hasPath hc.kpos hbad'
    exact Finset.mem_filter.mpr ⟨hmem, (hR A hsubset hno).le⟩
  have hevent := Reveal.event_card R m
    (fun bs => (Reveal.ones (bs.take q) : ℝ) ≤ X)
  have hp :
      FiniteProbability.probability (graphFamily n m)
        (fun A => (Reveal.ones ((Reveal.encode R A).take q) : ℝ) ≤ X) =
      FiniteProbability.probability (Reveal.weightWords (n.choose 2) m)
        (fun bs => (Reveal.ones (bs.take q) : ℝ) ≤ X) := by
    unfold FiniteProbability.probability
    simp only [graphFamily, hevent, edgeUniverse_card,
      Finset.card_powersetCard, Reveal.weightWords_card]
  calc
    1 - pathProbability n m ell =
        FiniteProbability.probability (graphFamily n m)
          (fun A => ¬ HasPathAtLeast A ell) := by
      rw [FiniteProbability.probability_complement (graphFamily n m) hΩ]
      rfl
    _ ≤ FiniteProbability.probability (graphFamily n m)
        (fun A => (Reveal.ones ((Reveal.encode R A).take q) : ℝ) ≤ X) := by
      unfold FiniteProbability.probability
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub))
        (Nat.cast_nonneg _)
    _ = _ := hp
    _ ≤ _ := Reveal.prefix_lower_tail hE hm hq hmean

/-! ## Floors, fixed-edge asymptotics, and a reusable numerical limit theorem -/

namespace Limits

def edgeCount (n : ℕ) : ℕ := n.choose 2
def edgeNumber (c : ℝ) (n : ℕ) : ℕ := ⌊c * (n : ℝ)⌋₊
def queryNumber (d : ℝ) (n : ℕ) : ℕ := ⌊d * (n : ℝ) ^ 2⌋₊
def mean (c d : ℝ) (n : ℕ) : ℝ :=
  Reveal.prefixMean (edgeCount n) (edgeNumber c n) (queryNumber d n)

theorem inv_nat_limit : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := by
  simpa [one_div, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))

theorem floor_scaled_limit (d : ℝ) (hd : 0 ≤ d) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => (⌊d * (n : ℝ) ^ k⌋₊ : ℝ) / (n : ℝ) ^ k)
      atTop (𝓝 d) := by
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ k) atTop (𝓝 0) := by
    simpa [div_pow, Nat.ne_of_gt hk] using inv_nat_limit.pow k
  have hl : Tendsto (fun n : ℕ => d - (1 : ℝ) / (n : ℝ) ^ k)
      atTop (𝓝 d) := by
    simpa using tendsto_const_nhds.sub hi
  have hlow : ∀ᶠ n : ℕ in atTop,
      d - 1 / (n : ℝ) ^ k ≤ (⌊d * (n : ℝ) ^ k⌋₊ : ℝ) / (n : ℝ) ^ k := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hpow : (0 : ℝ) < (n : ℝ) ^ k := pow_pos hnR k
    have hf := Nat.lt_floor_add_one (d * (n : ℝ) ^ k)
    calc
      d - 1 / (n : ℝ) ^ k = (d * (n : ℝ) ^ k - 1) / (n : ℝ) ^ k := by
        field_simp [ne_of_gt hpow] <;> ring
      _ ≤ (⌊d * (n : ℝ) ^ k⌋₊ : ℝ) / (n : ℝ) ^ k :=
        div_le_div_of_nonneg_right (by linarith) hpow.le
  have hhigh : ∀ᶠ n : ℕ in atTop,
      (⌊d * (n : ℝ) ^ k⌋₊ : ℝ) / (n : ℝ) ^ k ≤ d := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply (div_le_iff₀ (pow_pos hnR k)).2
    exact Nat.floor_le (mul_nonneg hd (pow_nonneg hnR.le k))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds hlow hhigh

theorem edge_number_limit (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => (edgeNumber c n : ℝ) / n) atTop (𝓝 c) := by
  simpa [edgeNumber] using floor_scaled_limit c hc 1 (by omega)

theorem query_number_limit (d : ℝ) (hd : 0 ≤ d) :
    Tendsto (fun n : ℕ => (queryNumber d n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 d) := floor_scaled_limit d hd 2 (by omega)

theorem edge_count_real {n : ℕ} (hn : 1 ≤ n) :
    (edgeCount n : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hnat : (k + 1) * k = (k + 1).choose 2 * 2 := by
    simpa using Nat.add_one_mul_choose_eq k 1
  have h : ((k : ℝ) + 1) * k = ((k + 1).choose 2 : ℝ) * 2 := by
    exact_mod_cast hnat
  unfold edgeCount
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

theorem edge_count_limit :
    Tendsto (fun n : ℕ => (edgeCount n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have h : Tendsto (fun n : ℕ => (1 / 2 : ℝ) - (1 / 2 : ℝ) * (1 / (n : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul inv_nat_limit)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [edge_count_real hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hn0] <;> ring

theorem eventually_admissible (c d : ℝ) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hdhi : d < 1 / 2) :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ edgeCount n ∧ edgeNumber c n ≤ edgeCount n ∧
        queryNumber d n ≤ edgeCount n := by
  have hm2 : Tendsto (fun n : ℕ => (edgeNumber c n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have h := (edge_number_limit c hc).mul inv_nat_limit
    convert h using 1
    · ext n
      simp only [pow_two, div_eq_mul_inv, mul_inv_rev]
      ring
    · simp
  have hmp : ∀ᶠ n : ℕ in atTop,
      0 < (edgeCount n : ℝ) / (n : ℝ) ^ 2 -
        (edgeNumber c n : ℝ) / (n : ℝ) ^ 2 :=
    (edge_count_limit.sub hm2).eventually (Ioi_mem_nhds (by norm_num))
  have hqp : ∀ᶠ n : ℕ in atTop,
      0 < (edgeCount n : ℝ) / (n : ℝ) ^ 2 -
        (queryNumber d n : ℝ) / (n : ℝ) ^ 2 :=
    (edge_count_limit.sub (query_number_limit d hd)).eventually
      (Ioi_mem_nhds (by linarith))
  filter_upwards [eventually_ge_atTop (3 : ℕ), hmp, hqp] with n hn hm hq
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have he := edge_count_real (show 1 ≤ n by omega)
  have hE : (2 : ℝ) ≤ edgeCount n := by
    nlinarith [sq_nonneg ((n : ℝ) - 3)]
  have hmR : (edgeNumber c n : ℝ) ≤ edgeCount n := by
    apply le_of_lt
    apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hnpos)).1
    linarith
  have hqR : (queryNumber d n : ℝ) ≤ edgeCount n := by
    apply le_of_lt
    apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hnpos)).1
    linarith
  exact ⟨by exact_mod_cast hE, by exact_mod_cast hmR, by exact_mod_cast hqR⟩

theorem mean_normalized_limit (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Tendsto (fun n : ℕ => mean c d n / n) atTop (𝓝 (2 * c * d)) := by
  have h := ((edge_number_limit c hc).mul (query_number_limit d hd)).div
    edge_count_limit (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hh : Tendsto
      (fun n : ℕ => ((edgeNumber c n : ℝ) / n) *
        ((queryNumber d n : ℝ) / (n : ℝ) ^ 2) /
          ((edgeCount n : ℝ) / (n : ℝ) ^ 2)) atTop (𝓝 (2 * c * d)) := by
    convert h using 1
    · rfl
    · ring
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold mean Reveal.prefixMean
  by_cases hE : (edgeCount n : ℝ) = 0
  · simp [hE]
  · field_simp [hn0, hE] <;> ring

/-- Passing from finitely certified DFS inequalities to a limiting graph theorem.
All graph/probability work is discharged by `finite_path_failure_bound` above. -/
theorem probability_limit_of_certificates
    (c d κ χ ell : ℝ) (r : ℕ → ℕ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hdhi : d < 1 / 2)
    (hgap : χ < 2 * c * d) (hell : ell < κ)
    (hcert : ∀ᶠ n : ℕ in atTop,
      DFS.NumericCertificate n (queryNumber d n) (r n)
        (κ * (n : ℝ)) (χ * (n : ℝ))) :
    Tendsto (fun n : ℕ => pathProbability n (edgeNumber c n) (ell * (n : ℝ)))
      atTop (𝓝 1) := by
  let gap : ℕ → ℝ := fun n => mean c d n - χ * (n : ℝ)
  have hgaplim : Tendsto (fun n : ℕ => gap n / n)
      atTop (𝓝 (2 * c * d - χ)) := by
    have h := (mean_normalized_limit c d hc hd).sub
      (tendsto_const_nhds (x := χ))
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    dsimp [gap]
    field_simp [hn0] <;> ring
  have hgap0 : 0 < 2 * c * d - χ := by linarith
  have hgapE : ∀ᶠ n : ℕ in atTop, 0 < gap n / n :=
    hgaplim.eventually (Ioi_mem_nhds hgap0)
  have herrmodel := ((edge_number_limit c hc).div (hgaplim.pow 2)
    (ne_of_gt (sq_pos_of_pos hgap0))).mul inv_nat_limit
  have herr : Tendsto (fun n : ℕ => (edgeNumber c n : ℝ) / (gap n) ^ 2)
      atTop (𝓝 0) := by
    have hh : Tendsto
        (fun n : ℕ => ((edgeNumber c n : ℝ) / n) /
          (gap n / n) ^ 2 * (1 / (n : ℝ))) atTop (𝓝 0) := by
      simpa using herrmodel
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    by_cases hg : gap n = 0
    · simp [hg]
    · field_simp [hn0, hg] <;> ring
  have hellE : ∀ᶠ n : ℕ in atTop, ell * (n : ℝ) ≤ κ * (n : ℝ) - 1 := by
    have hlpos : 0 < κ - ell := by linarith
    have hh : ∀ᶠ n : ℕ in atTop, 1 / (κ - ell) ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop (1 / (κ - ell)))
    filter_upwards [hh] with n hn
    have hmul := (div_le_iff₀ hlpos).1 hn
    nlinarith
  have hlower : ∀ᶠ n : ℕ in atTop,
      1 - (edgeNumber c n : ℝ) / (gap n) ^ 2 ≤
        pathProbability n (edgeNumber c n) (ell * (n : ℝ)) := by
    filter_upwards [hcert, eventually_admissible c d hc hd hdhi,
      hgapE, hellE, eventually_ge_atTop (1 : ℕ)] with n hcn had hgn hlen hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hg : 0 < gap n := (div_pos_iff_of_pos_right hnR).1 hgn
    have hmean : χ * (n : ℝ) < Reveal.prefixMean (n.choose 2)
        (edgeNumber c n) (queryNumber d n) := by
      change χ * (n : ℝ) < mean c d n
      dsimp [gap] at hg
      linarith
    have hf := finite_path_failure_bound hcn had.1 had.2.1 had.2.2 hmean hlen
    change 1 - pathProbability n (edgeNumber c n) (ell * (n : ℝ)) ≤
      (edgeNumber c n : ℝ) / (gap n) ^ 2 at hf
    linarith
  have hlowlim : Tendsto (fun n : ℕ => 1 - (edgeNumber c n : ℝ) / (gap n) ^ 2)
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub herr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowlim tendsto_const_nhds
    hlower (Filter.Eventually.of_forall fun n => pathProbability_le_one _ _ _)

end Limits

/-! ## Numerical certificates covering every `c > 1/2` -/

theorem small_numeric_certificate {c : ℝ} (hc : 1 / 2 < c) {n : ℕ}
    (hn : 12 ≤ n) :
    DFS.NumericCertificate n (Limits.queryNumber (a c) n) ⌊(n : ℝ) / 3⌋₊
      ((b c) ^ 2 * (n : ℝ)) ((b c - (b c) ^ 2) * (n : ℝ)) := by
  have hnR : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hb := b_pos hc
  have hbhi := (b_lt_quarter hc).le
  have hb2 : (b c) ^ 2 ≤ 1 / 16 := by nlinarith
  have hrf : (⌊(n : ℝ) / 3⌋₊ : ℝ) ≤ (n : ℝ) / 3 :=
    Nat.floor_le (by positivity)
  have hrl : (n : ℝ) / 4 ≤ (⌊(n : ℝ) / 3⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one ((n : ℝ) / 3)
    linarith
  have hqp : (Limits.queryNumber (a c) n : ℝ) ≤ a c * (n : ℝ) ^ 2 :=
    Nat.floor_le (mul_nonneg (a_pos hc).le (sq_nonneg _))
  have hq16 : (Limits.queryNumber (a c) n : ℝ) ≤ (n : ℝ) ^ 2 / 16 := by
    have := mul_le_mul_of_nonneg_right (a_le_sixteenth c) (sq_nonneg (n : ℝ))
    nlinarith
  have hKu : (b c) ^ 2 * (n : ℝ) ≤ (n : ℝ) / 16 := by
    nlinarith [mul_le_mul_of_nonneg_right hb2 hn0.le]
  constructor
  · exact mul_pos (sq_pos_of_pos hb) hn0
  · have : (0 : ℝ) < (⌊(n : ℝ) / 3⌋₊ : ℝ) := by linarith
    exact_mod_cast this
  · linarith
  · intro u hu0 hu
    by_contra hnot
    have hcut := le_of_not_gt hnot
    exact small_crossing_impossible hn0 hrl hrf (by linarith) hcut hq16
  · intro s u hs0 hu0 hs hu hcut
    by_contra hbad
    have hseen := le_of_not_gt hbad
    have hsu := small_stack_bound hb hbhi hn0 hs0 (by linarith)
      hseen hcut (by simpa [a] using hqp)
    linarith

theorem small_probability_limit {c : ℝ} (hc : 1 / 2 < c) :
    Tendsto (fun n : ℕ => pathProbability n ⌊c * (n : ℝ)⌋₊
      (smallCoefficient c * (n : ℝ))) atTop (𝓝 1) := by
  apply Limits.probability_limit_of_certificates c (a c) ((b c) ^ 2)
    (b c - (b c) ^ 2) (smallCoefficient c) (fun n => ⌊(n : ℝ) / 3⌋₊)
  · linarith
  · exact (a_pos hc).le
  · linarith [a_le_sixteenth c]
  · rw [mean_identity hc]
    have := sq_pos_of_pos (b_pos hc)
    linarith
  · unfold smallCoefficient
    have := sq_pos_of_pos (b_pos hc)
    linarith
  · filter_upwards [eventually_ge_atTop (12 : ℕ)] with n hn
    exact small_numeric_certificate hc hn

/-- The large-density branch is derived from the same query-count argument. -/
def delta (c : ℝ) : ℝ := 4 / Real.sqrt c

theorem delta_properties {c : ℝ} (hc : 64 < c) :
    0 < delta c ∧ delta c < 1 / 2 ∧
      (delta c) ^ 2 / 16 = 1 / c ∧ largeCoefficient c = 1 - 2 * delta c := by
  have hc0 : 0 < c := by linarith
  have hs0 : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
  have hs2 : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc0.le
  have hs8 : 8 < Real.sqrt c := by nlinarith
  refine ⟨div_pos (by norm_num) hs0, ?_, ?_, ?_⟩
  · unfold delta
    apply (div_lt_iff₀ hs0).2
    linarith
  · unfold delta
    field_simp [ne_of_gt hs0, ne_of_gt hc0]
    nlinarith [hs2]
  · unfold largeCoefficient delta
    ring

theorem large_numeric_certificate {c : ℝ} (hc : 64 < c) {n : ℕ}
    (hn : 0 < n) (hnlarge : 4 ≤ delta c * (n : ℝ)) :
    DFS.NumericCertificate n (Limits.queryNumber (1 / c) n)
      ⌊delta c * (n : ℝ) / 2⌋₊
      ((1 - delta c) * (n : ℝ)) (1 * (n : ℝ)) := by
  obtain ⟨hdpos, hdhi, hdelta, hlarge⟩ := delta_properties hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrhi : (⌊delta c * (n : ℝ) / 2⌋₊ : ℝ) ≤ delta c * (n : ℝ) / 2 :=
    Nat.floor_le (by positivity)
  have hrlo : delta c * (n : ℝ) / 4 ≤
      (⌊delta c * (n : ℝ) / 2⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (delta c * (n : ℝ) / 2)
    linarith
  have hq : (Limits.queryNumber (1 / c) n : ℝ) ≤
      (delta c) ^ 2 * (n : ℝ) ^ 2 / 16 := by
    have hcpos : 0 < c := by linarith
    have hf := Nat.floor_le (mul_nonneg
      (show (0 : ℝ) ≤ 1 / c by positivity)
      (sq_nonneg (n : ℝ)))
    change (⌊(1 / c) * (n : ℝ) ^ 2⌋₊ : ℝ) ≤ _
    rw [← hdelta]
    rw [← hdelta] at hf
    nlinarith
  constructor
  · exact mul_pos (by linarith) hnR
  · have : (0 : ℝ) < (⌊delta c * (n : ℝ) / 2⌋₊ : ℝ) := by
      nlinarith [mul_pos hdpos hnR]
    exact_mod_cast this
  · nlinarith [mul_pos hdpos hnR]
  · intro u hu0 hu
    by_contra hbad
    exact large_crossing_impossible hdpos hnR hrlo hrhi hu.le
      (le_of_not_gt hbad) hq
  · intro s u hs0 hu0 hs hu hcut
    simpa using large_seen_lt hdpos hnR hrhi hs hu (le_refl (s + u))

theorem large_probability_limit {c : ℝ} (hc : 64 < c) :
    Tendsto (fun n : ℕ => pathProbability n ⌊c * (n : ℝ)⌋₊
      (largeCoefficient c * (n : ℝ))) atTop (𝓝 1) := by
  obtain ⟨hdpos, hdhi, hdelta, hlarge⟩ := delta_properties hc
  have hc0 : 0 < c := by linarith
  apply Limits.probability_limit_of_certificates c (1 / c) (1 - delta c)
    1 (largeCoefficient c) (fun n => ⌊delta c * (n : ℝ) / 2⌋₊)
  · exact hc0.le
  · positivity
  · apply (div_lt_iff₀ hc0).2
    linarith
  · have h : 2 * c * (1 / c) = (2 : ℝ) := by
      field_simp [ne_of_gt hc0]
    linarith
  · rw [hlarge]
    linarith
  · have hh : ∀ᶠ n : ℕ in atTop, 4 / delta c ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop (4 / delta c))
    filter_upwards [hh, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    apply large_numeric_certificate hc (by omega)
    have := (div_le_iff₀ hdpos).1 hn
    nlinarith

/-- For every fixed `c > 1/2`, the explicit coefficient works in `G(n,floor(c*n))`.
No key random-graph assertion occurs among this theorem's hypotheses. -/
theorem erdos_900_fixed_c {c : ℝ} (hc : 1 / 2 < c) :
    Tendsto (fun n : ℕ => pathProbability n ⌊c * (n : ℝ)⌋₊
      (coefficient c * (n : ℝ))) atTop (𝓝 1) := by
  by_cases h : largeCoefficient c ≤ smallCoefficient c
  · simpa [coefficient, max_eq_left h] using small_probability_limit hc
  · have hgt : smallCoefficient c < largeCoefficient c := lt_of_not_ge h
    have hsmall : 0 < smallCoefficient c := by
      unfold smallCoefficient
      exact div_pos (sq_pos_of_pos (b_pos hc)) (by norm_num)
    have hc64 := large_positive_implies_gt64 hc (hsmall.trans hgt)
    simpa [coefficient, max_eq_right hgt.le] using large_probability_limit hc64

/-- The original full statement, with edge-length convention and floor rounding. -/
theorem erdos_900 : OriginalStatement := by
  refine ⟨coefficient, ?_, coefficient_tendsto_half, coefficient_tendsto_infty, ?_⟩
  · intro c hc
    exact ⟨coefficient_pos hc, coefficient_lt_one hc⟩
  · intro c hc
    exact erdos_900_fixed_c hc

#print axioms erdos_900_fixed_c
#print axioms erdos_900

end JSP748
