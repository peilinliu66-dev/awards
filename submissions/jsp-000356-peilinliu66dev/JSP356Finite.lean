/-
JSP-000356 / Erdos problem 437: finite combinatorial core.

Target: Lean 4.33.1, Mathlib
0df444a360eaa60ab8c11dca51a86af692955474.

Attribution: Bui--Pratt--Zaharescu (2024), and Tao's exposition
of 9 August 2024.  The fixed-degree prime-product specialization
below is an elementary reformulation, not a claim of a new solution.

This module proves all-parameter finite lower bounds and their square-prefix
interpretation. JSP356Asymptotic.lean proves the full real-cutoff endpoint.
The complete project has been checked locally with the pinned Lean toolchain;
see verification/ for build evidence.
-/
import Mathlib

open Finset
open scoped Classical

namespace JSP356

noncomputable section

/-- Product of the selected positive integers up to the cutoff t. -/
def prefixProduct (A : Finset ℕ) (t : ℕ) : ℕ :=
  ∏ a ∈ A.filter (fun a => a ≤ t), a

/-- Only nonempty prefixes are counted: a cutoff must belong to A. -/
def squareCuts (A : Finset ℕ) : Finset ℕ :=
  A.filter (fun t => IsSquare (prefixProduct A t))

/-- This is the full lower-bound question, not a finite special case. -/
def OriginalLowerQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧
      (N : ℝ) ^ (1 - ε) < ((squareCuts A).card : ℝ)

/-- The density-zero upper statement, included in the mathematical proof. -/
def DensityZeroUpperQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ, A ⊆ Icc 1 N →
      ((squareCuts A).card : ℝ) < ε * (N : ℝ)

lemma square_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, IsSquare (f i)) : IsSquare (∏ i ∈ s, f i) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨1, by simp⟩
  | @insert a s ha ih =>
      intro h
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

lemma square_of_even_factorization {n : ℕ} (hn : n ≠ 0)
    (he : ∀ p : ℕ, 2 ∣ n.factorization p) : IsSquare n := by
  classical
  let b : ℕ := ∏ p ∈ n.factorization.support, p ^ (n.factorization p / 2)
  refine ⟨b, ?_⟩
  calc
    n = ∏ p ∈ n.factorization.support, p ^ n.factorization p :=
      (Nat.prod_factorization_pow_eq_self hn).symm
    _ = ∏ p ∈ n.factorization.support, (p ^ (n.factorization p / 2)) ^ 2 := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul, Nat.div_mul_cancel (he p)]
    _ = b * b := by
      rw [Finset.prod_pow]
      change b ^ 2 = b * b
      ring

lemma zmod_two_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A finite prime-support set is all that matters; primality of P itself
is not needed in this linear-algebra lemma. -/
theorem square_subproduct
    (P B : Finset ℕ)
    (hpos : ∀ b ∈ B, b ≠ 0)
    (hsupp : ∀ b ∈ B, ∀ p : ℕ, p ∉ P → b.factorization p = 0)
    (hcard : P.card < B.card) :
    ∃ T : Finset ℕ, T ⊆ B ∧ T.Nonempty ∧ IsSquare (∏ b ∈ T, b) := by
  classical
  let F : (B → ZMod 2) →ₗ[ZMod 2] (P → ZMod 2) :=
    { toFun := fun c p => ∑ b : B, c b * (b.val.factorization p.val : ZMod 2)
      map_add' := by
        intro c d
        ext p
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro z c
        ext p
        simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }
  have hdim : Module.finrank (ZMod 2) (P → ZMod 2) <
      Module.finrank (ZMod 2) (B → ZMod 2) := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hcard
  have hker : F.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  have hex : ∃ c : B → ZMod 2, c ∈ F.ker ∧ c ≠ 0 := by
    by_contra h
    apply hker
    apply le_antisymm
    · intro c hc
      have hc0 : c = 0 := by
        by_contra hc0
        exact h ⟨c, hc, hc0⟩
      simpa [hc0]
    · exact bot_le
  obtain ⟨c, hc, hc0⟩ := hex
  let S : Finset B := Finset.univ.filter (fun b => c b = 1)
  have hS : S.Nonempty := by
    by_contra hS
    apply hc0
    funext b
    rcases zmod_two_cases (c b) with h0 | h1
    · exact h0
    · exact False.elim (hS ⟨b, by simp [S, h1]⟩)
  have hsum (p : P) :
      ∑ b ∈ S, (b.val.factorization p.val : ZMod 2) = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp hc) p
    change (∑ b : B, c b * (b.val.factorization p.val : ZMod 2)) = 0 at h
    calc
      (∑ b ∈ S, (b.val.factorization p.val : ZMod 2)) =
          ∑ b : B, c b * (b.val.factorization p.val : ZMod 2) := by
        rw [show S = Finset.univ.filter (fun b : B => c b = 1) from rfl,
          Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro b hb
        rcases zmod_two_cases (c b) with h0 | h1
        · simp [h0]
        · simp [h1]
      _ = 0 := h
  have hnonzero : (∏ b ∈ S, b.val) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    exact hpos b.val b.property
  have hsquare : IsSquare (∏ b ∈ S, b.val) := by
    apply square_of_even_factorization hnonzero
    intro p
    rw [Nat.factorization_prod_apply
      (fun b (_ : b ∈ S) => hpos b.val b.property)]
    by_cases hp : p ∈ P
    · have hcast : ((∑ b ∈ S, b.val.factorization p : ℕ) : ZMod 2) = 0 := by
        simpa only [Nat.cast_sum] using hsum ⟨p, hp⟩
      exact (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp hcast
    · have hz : (∑ b ∈ S, b.val.factorization p) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        exact hsupp b.val b.property p hp
      simp [hz]
  let T : Finset ℕ := S.image Subtype.val
  refine ⟨T, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    exact b'.property
  · exact hS.image Subtype.val
  · have hprod : (∏ b ∈ T, b) = ∏ b ∈ S, b.val := by
      dsimp [T]
      rw [Finset.prod_image]
      intro b hb d hd hbd
      exact Subtype.ext hbd
    simpa only [hprod] using hsquare

/-- Ordered nonempty square-product blocks give that many genuine square
prefixes.  This is the bridge that prevents counting arbitrary square
subsets in place of the original ordered-prefix problem. -/
theorem ordered_square_blocks
    {q N : ℕ} (T : Fin q → Finset ℕ)
    (hne : ∀ i, (T i).Nonempty)
    (hsq : ∀ i, IsSquare (∏ a ∈ T i, a))
    (horder : ∀ i j : Fin q, i < j →
      ∀ a ∈ T i, ∀ b ∈ T j, a < b)
    (hbound : ∀ i, ∀ a ∈ T i, a ∈ Icc 1 N) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ q ≤ (squareCuts A).card := by
  classical
  let A : Finset ℕ := Finset.univ.biUnion T
  let last : Fin q → ℕ := fun i => (T i).max' (hne i)
  have hlast (i : Fin q) : last i ∈ T i := (T i).max'_mem (hne i)
  have hlast_le (i : Fin q) (a : ℕ) (ha : a ∈ T i) : a ≤ last i :=
    (T i).le_max' a ha
  have hA : A ⊆ Icc 1 N := by
    intro a ha
    obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
    exact hbound i a hai
  have hlastmono : StrictMono last := by
    intro i j hij
    exact horder i j hij (last i) (hlast i) (last j) (hlast j)
  have hdis (i j : Fin q) (hij : i ≠ j) : Disjoint (T i) (T j) := by
    apply Finset.disjoint_left.mpr
    intro a hai haj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (lt_irrefl a) (horder i j hlt a hai a haj)
    · exact (lt_irrefl a) (horder j i hgt a haj a hai)
  have hpref (i : Fin q) :
      A.filter (fun a => a ≤ last i) =
        (Finset.univ.filter (fun j : Fin q => j ≤ i)).biUnion T := by
    ext a
    constructor
    · intro ha
      obtain ⟨haA, hai⟩ := Finset.mem_filter.mp ha
      obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp haA
      have hji : j ≤ i := by
        by_contra hji
        have hij : i < j := lt_of_not_ge hji
        have : last i < a := horder i j hij (last i) (hlast i) a haj
        omega
      exact Finset.mem_biUnion.mpr ⟨j, by simp [hji], haj⟩
    · intro ha
      obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp ha
      have hji : j ≤ i := (Finset.mem_filter.mp hj).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, haj⟩, ?_⟩
      rcases lt_or_eq_of_le hji with hlt | rfl
      · exact (horder j i hlt a haj (last i) (hlast i)).le
      · exact hlast_le _ a haj
  have hprefsquare (i : Fin q) : IsSquare (prefixProduct A (last i)) := by
    unfold prefixProduct
    rw [hpref i, Finset.prod_biUnion]
    · exact square_prod _ (fun j => ∏ a ∈ T j, a) (fun j hj => hsq j)
    · intro j hj k hk hjk
      exact hdis j k hjk
  have hcut (i : Fin q) : last i ∈ squareCuts A := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hlast i⟩,
      hprefsquare i⟩
  refine ⟨A, hA, ?_⟩
  calc
    q = (Finset.univ.image last).card := by
      rw [Finset.card_image_of_injective _ hlastmono.injective]
      simp
    _ ≤ (squareCuts A).card := by
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact hcut i

/-- Each group of |P|+1 ordered elements yields one square-product block. -/
theorem packing_bound
    (P S : Finset ℕ) (N : ℕ)
    (hbound : S ⊆ Icc 1 N)
    (hsupp : ∀ b ∈ S, ∀ p : ℕ, p ∉ P → b.factorization p = 0) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧
      S.card / (P.card + 1) ≤ (squareCuts A).card := by
  classical
  let d := P.card + 1
  let q := S.card / d
  let e : Fin S.card ↪o ℕ := S.orderEmbOfFin rfl
  have hd : 0 < d := by dsimp [d]; omega
  have hqd : q * d ≤ S.card := Nat.div_mul_le_self _ _
  have hidx (i : Fin q) (j : Fin d) : i.val * d + j.val < S.card := by
    have hi : i.val + 1 ≤ q := i.isLt
    have hmul := Nat.mul_le_mul_right d hi
    have hj := j.isLt
    nlinarith
  let ix (i : Fin q) (j : Fin d) : Fin S.card :=
    ⟨i.val * d + j.val, hidx i j⟩
  let B (i : Fin q) : Finset ℕ :=
    Finset.univ.image (fun j : Fin d => e (ix i j))
  have hBsub (i : Fin q) : B i ⊆ S := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact S.orderEmbOfFin_mem rfl (ix i j)
  have hBcard (i : Fin q) : (B i).card = d := by
    have hinj : Function.Injective (fun j : Fin d => e (ix i j)) := by
      intro j k hjk
      have h := congrArg Fin.val (e.injective hjk)
      apply Fin.ext
      dsimp [ix] at h
      omega
    dsimp [B]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hBord (i j : Fin q) (hij : i < j) :
      ∀ a ∈ B i, ∀ b ∈ B j, a < b := by
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    apply e.strictMono
    change i.val * d + u.val < j.val * d + v.val
    have hij' : i.val + 1 ≤ j.val := hij
    have hm := Nat.mul_le_mul_right d hij'
    have hu' := u.isLt
    nlinarith [Nat.zero_le v.val]
  have hblock (i : Fin q) :
      ∃ T : Finset ℕ, T ⊆ B i ∧ T.Nonempty ∧ IsSquare (∏ b ∈ T, b) := by
    apply square_subproduct P (B i)
    · intro b hb
      have h := (Finset.mem_Icc.mp (hbound (hBsub i hb))).1
      omega
    · intro b hb p hp
      exact hsupp b (hBsub i hb) p hp
    · rw [hBcard i]
      dsimp [d]
      omega
  choose T hTsub hTne hTsq using hblock
  apply ordered_square_blocks T hTne hTsq
  · intro i j hij a ha b hb
    exact hBord i j hij a (hTsub i ha) b (hTsub j hb)
  · intro i a ha
    exact hbound (hBsub i (hTsub i ha))

lemma prime_dvd_product {p : ℕ} (hp : p.Prime) (S : Finset ℕ) :
    p ∣ (∏ q ∈ S, q) ↔ ∃ q ∈ S, p ∣ q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Nat.dvd_one, hp.ne_one]
  | @insert a S ha ih =>
      simp [Finset.prod_insert ha, hp.dvd_mul, ih]

lemma prime_product_injective
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {S T : Finset ℕ} (hS : S ⊆ P) (hT : T ⊆ P)
    (hprod : (∏ p ∈ S, p) = ∏ p ∈ T, p) : S = T := by
  classical
  have sub (U V : Finset ℕ) (hU : U ⊆ P) (hV : V ⊆ P)
      (heq : (∏ p ∈ U, p) = ∏ p ∈ V, p) : U ⊆ V := by
    intro p hp
    have pp : p.Prime := hP p (hU hp)
    have hd : p ∣ (∏ q ∈ V, q) := by
      rw [← heq]
      exact Finset.dvd_prod_of_mem (fun q => q) hp
    obtain ⟨q, hq, hpq⟩ := (prime_dvd_product pp V).mp hd
    have hpq' : p = q :=
      (Nat.prime_dvd_prime_iff_eq pp (hP q (hV hq))).mp hpq
    simpa only [hpq'] using hq
  exact Finset.Subset.antisymm (sub S T hS hT hprod) (sub T S hT hS hprod.symm)

def primeProducts (P : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (P.powersetCard k).image (fun S => ∏ p ∈ S, p)

lemma card_primeProducts (P : Finset ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (primeProducts P k).card = P.card.choose k := by
  classical
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) (P.powersetCard k) := by
    intro S hS T hT hprod
    exact prime_product_injective P hP
      (Finset.mem_powersetCard.mp hS).1 (Finset.mem_powersetCard.mp hT).1 hprod
  unfold primeProducts
  rw [Finset.card_image_iff.mpr hinj, Finset.card_powersetCard]

lemma primeProducts_bound
    (P : Finset ℕ) (y k : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPy : ∀ p ∈ P, p ≤ y) :
    primeProducts P k ⊆ Icc 1 (y ^ k) := by
  classical
  intro n hn
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hSP, hScard⟩ := Finset.mem_powersetCard.mp hS
  apply Finset.mem_Icc.mpr
  constructor
  · have hz : (∏ p ∈ S, p) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro p hp
      exact (hP p (hSP hp)).ne_zero
    omega
  · calc
      (∏ p ∈ S, p) ≤ ∏ _p ∈ S, y := by
        gcongr with p hp
        exact hPy p (hSP hp)
      _ = y ^ k := by simp [hScard]

lemma primeProducts_support
    (P : Finset ℕ) (k : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∀ n ∈ primeProducts P k, ∀ p : ℕ, p ∉ P → n.factorization p = 0 := by
  classical
  intro n hn p hp
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hn
  have hSP : S ⊆ P := (Finset.mem_powersetCard.mp hS).1
  rw [Nat.factorization_prod_apply
    (fun q hq => (hP q (hSP hq)).ne_zero)]
  apply Finset.sum_eq_zero
  intro q hq
  have hqP := hSP hq
  have hqp : q ≠ p := by
    intro h
    subst q
    exact hp hqP
  simp [(hP q hqP).factorization, Finsupp.single_apply, hqp, hqp.symm]

/-- Exact all-parameter finite lower bound.  No prime-number theorem,
smooth-number asymptotics, or conditional number-theory hypothesis. -/
theorem finite_lower_bound (N y k : ℕ) (hpow : y ^ k ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧
      (Nat.primeCounting y).choose k / (Nat.primeCounting y + 1)
        ≤ (squareCuts A).card := by
  classical
  let P := Nat.primesLE y
  let S := primeProducts P k
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesLE hp
  have hPy : ∀ p ∈ P, p ≤ y := by
    intro p hp
    exact Nat.le_of_mem_primesLE hp
  have hbound : S ⊆ Icc 1 N := by
    intro n hn
    have h := Finset.mem_Icc.mp (primeProducts_bound P y k hP hPy hn)
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.trans hpow⟩
  obtain ⟨A, hA, hcard⟩ := packing_bound P S N hbound (primeProducts_support P k hP)
  refine ⟨A, hA, ?_⟩
  simpa only [S, card_primeProducts P k hP,
    P, Nat.primesLE_card_eq_primeCounting] using hcard

/-- Finite sequence version: values are strictly increasing, and each
counted index is a nonempty initial product in the sense of the original
question.  The theorem below identifies this count exactly. -/
def sequenceSquareCuts {m : ℕ} (a : Fin m → ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i =>
    IsSquare (∏ j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i), a j))

lemma prefixProduct_orderEmb (A : Finset ℕ) (i : Fin A.card) :
    prefixProduct A (A.orderEmbOfFin rfl i) =
      ∏ j ∈ Finset.univ.filter (fun j : Fin A.card => j ≤ i), A.orderEmbOfFin rfl j := by
  classical
  let e : Fin A.card ↪o ℕ := A.orderEmbOfFin rfl
  have himage : Finset.univ.image e = A := A.image_orderEmbOfFin_univ rfl
  have hfilter : A.filter (fun n => n ≤ e i) =
      (Finset.univ.filter (fun j : Fin A.card => j ≤ i)).image e := by
    calc
      A.filter (fun n => n ≤ e i) =
          (Finset.univ.image e).filter (fun n => n ≤ e i) := by rw [himage]
      _ = (Finset.univ.filter (fun j : Fin A.card => j ≤ i)).image e := by
        rw [Finset.filter_image]
        congr 1
        ext j
        simp
  change prefixProduct A (e i) = _
  unfold prefixProduct
  rw [hfilter, Finset.prod_image]
  intro j hj k hk hjk
  exact e.injective hjk

lemma card_sequenceSquareCuts_orderEmb (A : Finset ℕ) :
    (sequenceSquareCuts (A.orderEmbOfFin rfl)).card = (squareCuts A).card := by
  classical
  let e : Fin A.card ↪o ℕ := A.orderEmbOfFin rfl
  have himage : Finset.univ.image e = A := A.image_orderEmbOfFin_univ rfl
  have heq : (sequenceSquareCuts e).image e = squareCuts A := by
    unfold sequenceSquareCuts squareCuts
    calc
      (Finset.univ.filter (fun i => IsSquare
          (∏ j ∈ Finset.univ.filter (fun j : Fin A.card => j ≤ i), e j))).image e =
          (Finset.univ.filter (fun i => IsSquare (prefixProduct A (e i)))).image e := by
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [prefixProduct_orderEmb]
      _ = (Finset.univ.image e).filter (fun t => IsSquare (prefixProduct A t)) := by
        rw [Finset.filter_image]
      _ = A.filter (fun t => IsSquare (prefixProduct A t)) := by rw [himage]
  rw [← heq, Finset.card_image_of_injective _ e.injective]

/-- The finite lower bound, stated with an actual increasing sequence.
The remaining real-asymptotic layer must be proved before claiming
OriginalLowerQuestion as a Lean theorem. -/
theorem finite_lower_bound_sequence (N y k : ℕ) (hpow : y ^ k ≤ N) :
    ∃ m : ℕ, ∃ a : Fin m → ℕ,
      StrictMono a ∧ (∀ i, 1 ≤ a i ∧ a i ≤ N) ∧
      (Nat.primeCounting y).choose k / (Nat.primeCounting y + 1)
        ≤ (sequenceSquareCuts a).card := by
  classical
  obtain ⟨A, hA, hcount⟩ := finite_lower_bound N y k hpow
  refine ⟨A.card, A.orderEmbOfFin rfl, (A.orderEmbOfFin rfl).strictMono, ?_, ?_⟩
  · intro i
    exact Finset.mem_Icc.mp (hA (A.orderEmbOfFin_mem rfl i))
  · simpa only [card_sequenceSquareCuts_orderEmb] using hcount


/-- Loss of at most one when passing from a real quotient to Nat division. -/
lemma real_quotient_sub_one_lt_nat_div (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) - 1 < ((a / b : ℕ) : ℝ) := by
  have hmod := Nat.mod_lt a hb
  have heq := Nat.div_add_mod a b
  have hnat : a < (a / b + 1) * b := by nlinarith
  have hreal : (a : ℝ) < (((a / b : ℕ) : ℝ) + 1) * (b : ℝ) := by
    exact_mod_cast hnat
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdiv : (a : ℝ) / (b : ℝ) < ((a / b : ℕ) : ℝ) + 1 :=
    (div_lt_iff₀ hbR).mpr hreal
  linarith

/-- A real-valued version ready for the asymptotic layer.  The subtraction
inside r+1-k remains Nat subtraction, exactly as in Nat.pow_le_choose. -/
theorem real_finite_lower_bound (N y k : ℕ) (hpow : y ^ k ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧
      (((Nat.primeCounting y + 1 - k : ℕ) : ℝ) ^ k) /
          ((k.factorial : ℝ) * (Nat.primeCounting y + 1 : ℕ)) - 1
        < ((squareCuts A).card : ℝ) := by
  obtain ⟨A, hA, hcard⟩ := finite_lower_bound N y k hpow
  let r := Nat.primeCounting y
  have hchoose : (((r + 1 - k : ℕ) : ℝ) ^ k) / (k.factorial : ℝ) ≤
      (r.choose k : ℝ) := Nat.pow_le_choose k r
  have hdiv := real_quotient_sub_one_lt_nat_div (r.choose k) (r + 1)
    (Nat.succ_pos r)
  have hcardR : (((r.choose k / (r + 1) : ℕ)) : ℝ) ≤
      ((squareCuts A).card : ℝ) := by exact_mod_cast hcard
  refine ⟨A, hA, ?_⟩
  change (((r + 1 - k : ℕ) : ℝ) ^ k) /
      ((k.factorial : ℝ) * (r + 1 : ℕ)) - 1 < _
  calc
    (((r + 1 - k : ℕ) : ℝ) ^ k) /
          ((k.factorial : ℝ) * (r + 1 : ℕ)) - 1 =
        ((((r + 1 - k : ℕ) : ℝ) ^ k) / (k.factorial : ℝ)) /
          (r + 1 : ℕ) - 1 := by rw [div_div]
    _ ≤ (r.choose k : ℝ) / (r + 1 : ℕ) - 1 := by
      exact sub_le_sub_right
        (div_le_div_of_nonneg_right hchoose (by positivity)) 1
    _ < (((r.choose k / (r + 1) : ℕ)) : ℝ) := hdiv
    _ ≤ ((squareCuts A).card : ℝ) := hcardR

/-- Available in the stipulated Mathlib revision; no PNT is required. -/
theorem chebyshev_input (y : ℕ) :
    ((y : ℝ) * Real.log 2 - Real.log ((y : ℝ) + 1)) / Real.log (y : ℝ)
      ≤ (Nat.primeCounting y : ℝ) :=
  Chebyshev.pi_ge y

end
end JSP356
