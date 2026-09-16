import Mathlib

/-!
# An elementary finite upper bound for Erdos problem 437 (JSP-000356)

Target toolchain: Lean 4.33.1.
Target Mathlib commit: 0df444a360eaa60ab8c11dca51a86af692955474.

For an ordered family of `K` nonempty finite sets of positive integers at most `N`,
each with square product, we prove, for every positive integer `H`,

    K <= N / H + 2 ^ H * (Nat.sqrt N + 1).

We then give an explicit uniform density bound and a little-o corollary.

The argument uses only finite sets, natural-number factorization, squarefree
factorization, and elementary inequalities. All square assertions use Mathlib's
standard `IsSquare` predicate. The finite upper bound does not assume a
squarefree-kernel API or a prime-number estimate.

This module is locally checked with the pinned Lean toolchain.
JSP356UpperBridge.lean connects the blocks to the original square prefixes.
-/

open scoped BigOperators
open Finset

namespace Erdos437Upper

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

noncomputable section

/-! ## 1. Elementary factorization lemmas -/

/-- Every exponent in the factorization of a square is even, including at zero. -/
theorem factorization_even_of_isSquare {n : ℕ} (hn : IsSquare n) (p : ℕ) :
    Even (n.factorization p) := by
  rcases hn with ⟨b, rfl⟩
  by_cases hb : b = 0
  · subst b
    exact ⟨0, by simp⟩
  · refine ⟨b.factorization p, ?_⟩
    simp only [Nat.factorization_mul hb hb, Finsupp.add_apply]

/-- A prime appearing in the squarefree factor appears to odd exponent. -/
theorem factorization_sq_mul_squarefree
    {d b p : ℕ} (hd : 0 < d) (hb : 0 < b)
    (hsf : Squarefree d) (hp : Nat.Prime p) (hpd : p ∣ d) :
    (b ^ 2 * d).factorization p =
      b.factorization p + b.factorization p + 1 := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hfac : d.factorization p = 1 :=
    Nat.factorization_eq_one_of_squarefree hsf hp hpd
  rw [Nat.factorization_mul (pow_ne_zero 2 hb0) hd0,
    Finsupp.add_apply, hfac, pow_two,
    Nat.factorization_mul hb0 hb0, Finsupp.add_apply]

/-- The converse direction, useful when cancelling two square prefix products. -/
theorem isSquare_of_factorization_even {n : ℕ}
    (hn : 0 < n) (he : ∀ p : ℕ, Even (n.factorization p)) :
    IsSquare n := by
  obtain ⟨d, b, hd, hb, hdb, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hd1 : d = 1 := by
    by_contra hd1
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
    have hodd := factorization_sq_mul_squarefree hd hb hsf hp hpd
    rw [hdb] at hodd
    rcases he p with ⟨u, hu⟩
    omega
  refine ⟨b, ?_⟩
  simpa only [hd1, mul_one, pow_two] using hdb.symm

/-- Cancel a positive square factor from a positive square product. -/
theorem isSquare_right_of_mul
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hsa : IsSquare a) (hsab : IsSquare (a * b)) :
    IsSquare b := by
  apply isSquare_of_factorization_even hb
  intro p
  rcases factorization_even_of_isSquare hsa p with ⟨u, hu⟩
  rcases factorization_even_of_isSquare hsab p with ⟨v, hv⟩
  rw [Nat.factorization_mul (ne_of_gt ha) (ne_of_gt hb),
    Finsupp.add_apply] at hv
  refine ⟨b.factorization p / 2, ?_⟩
  omega

/-! ## 2. Short intervals and squarefree factors -/

/-- Two distinct multiples of `p` cannot lie in an interval of span less than `p`. -/
theorem eq_of_dvd_of_short_interval
    {lo hi H p x y : ℕ}
    (hspan : hi - lo < H) (hpH : H < p)
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi)
    (hpx : p ∣ x) (hpy : p ∣ y) :
    x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have hdvd : p ∣ y - x := Nat.dvd_sub hpy hpx
    have hle : p ≤ y - x :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt hxy) hdvd
    omega
  · exact hxy
  · have hdvd : p ∣ x - y := Nat.dvd_sub hpx hpy
    have hle : p ≤ x - y :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt hyx) hdvd
    omega

/-- In a short square-product block, each large-prime exponent of each member is even. -/
theorem short_block_large_prime_even
    {B : Finset ℕ} {lo hi H a p : ℕ}
    (hpos : ∀ x ∈ B, 0 < x)
    (hmem : ∀ x ∈ B, lo ≤ x ∧ x ≤ hi)
    (hspan : hi - lo < H)
    (hsq : IsSquare (B.prod id))
    (ha : a ∈ B) (hpH : H < p) :
    Even (a.factorization p) := by
  classical
  by_cases hpa : p ∣ a
  · have hzero : ∀ x ∈ B, x ≠ a → x.factorization p = 0 := by
      intro x hx hxa
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpx
      exact hxa (eq_of_dvd_of_short_interval hspan hpH
        (hmem x hx) (hmem a ha) hpx hpa)
    have hsum : (∑ x ∈ B, x.factorization p) = a.factorization p :=
      Finset.sum_eq_single_of_mem a ha hzero
    have hfac : (B.prod id).factorization p = a.factorization p := by
      change (∏ x ∈ B, x).factorization p = a.factorization p
      rw [Nat.factorization_prod_apply
        (fun x hx => (ne_of_gt (hpos x hx)))]
      exact hsum
    have he := factorization_even_of_isSquare hsq p
    rwa [hfac] at he
  · rw [Nat.factorization_eq_zero_of_not_dvd hpa]
    exact ⟨0, rfl⟩

/-- An explicit finite superset of all possible short-block members.

The first coordinate is an arbitrary subset of `{1,...,H}`; there is no need
to restrict it to primes when proving an upper bound on the cardinality.
-/
def squareCandidates (N H : ℕ) : Finset ℕ :=
  (((Finset.Icc 1 H).powerset).product
    (Finset.range (Nat.sqrt N + 1))).image
    (fun z : Finset ℕ × ℕ => z.2 ^ 2 * z.1.prod id)

theorem card_squareCandidates_le (N H : ℕ) :
    (squareCandidates N H).card ≤ 2 ^ H * (Nat.sqrt N + 1) := by
  classical
  unfold squareCandidates
  calc
    _ ≤ (((Finset.Icc 1 H).powerset).product
        (Finset.range (Nat.sqrt N + 1))).card := Finset.card_image_le
    _ = 2 ^ H * (Nat.sqrt N + 1) := by simp

/-- Every member of a short square-product block belongs to `squareCandidates`. -/
theorem mem_squareCandidates_of_short_block
    {N H lo hi a : ℕ} {B : Finset ℕ}
    (hpos : ∀ x ∈ B, 0 < x)
    (hbound : ∀ x ∈ B, x ≤ N)
    (hmem : ∀ x ∈ B, lo ≤ x ∧ x ≤ hi)
    (hspan : hi - lo < H)
    (hsq : IsSquare (B.prod id)) (ha : a ∈ B) :
    a ∈ squareCandidates N H := by
  classical
  obtain ⟨d, b, hd, hb, hdb, hsf⟩ :=
    Nat.sq_mul_squarefree_of_pos (hpos a ha)
  have hdsub : d.primeFactors ⊆ Finset.Icc 1 H := by
    intro p hp
    have hprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    have hp_le : p ≤ H := by
      by_contra hp_le
      have he : Even (a.factorization p) :=
        short_block_large_prime_even hpos hmem hspan hsq ha (by omega)
      have hodd := factorization_sq_mul_squarefree hd hb hsf hprime hpd
      rw [hdb] at hodd
      rcases he with ⟨u, hu⟩
      omega
    exact Finset.mem_Icc.mpr ⟨by have := hprime.two_le; omega, hp_le⟩
  have hb2 : b ^ 2 ≤ N := by
    have hd1 : 1 ≤ d := hd
    calc
      b ^ 2 = b ^ 2 * 1 := (mul_one _).symm
      _ ≤ b ^ 2 * d := Nat.mul_le_mul_left _ hd1
      _ = a := hdb
      _ ≤ N := hbound a ha
  have hbsqrt : b ≤ Nat.sqrt N := Nat.le_sqrt'.mpr hb2
  have hprod : d.primeFactors.prod id = d := by
    simpa only [id_eq] using Nat.prod_primeFactors_of_squarefree hsf
  unfold squareCandidates
  apply Finset.mem_image.mpr
  refine ⟨(d.primeFactors, b), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr hdsub, Finset.mem_range.mpr (by omega)⟩
  · change b ^ 2 * d.primeFactors.prod id = a
    rw [hprod]
    exact hdb

/-! ## 3. The finite ordered block interface -/

/-- `K` nonempty, mutually ordered square-product blocks in `{1,...,N}`.

`ordered` is stronger than pairwise disjointness: every element of an earlier
block is smaller than every element of a later block. This is precisely what
successive intervals between square prefix products provide.
-/
structure OrderedSquareBlocks (N K : ℕ) where
  block : Fin K → Finset ℕ
  nonempty : ∀ i, (block i).Nonempty
  positive : ∀ i a, a ∈ block i → 0 < a
  bounded : ∀ i a, a ∈ block i → a ≤ N
  ordered : ∀ i j, i < j → ∀ a ∈ block i, ∀ b ∈ block j, a < b
  square : ∀ i, IsSquare ((block i).prod id)

namespace OrderedSquareBlocks

variable {N K : ℕ}

def lo (F : OrderedSquareBlocks N K) (i : Fin K) : ℕ :=
  (F.block i).min' (F.nonempty i)

def hi (F : OrderedSquareBlocks N K) (i : Fin K) : ℕ :=
  (F.block i).max' (F.nonempty i)

def span (F : OrderedSquareBlocks N K) (i : Fin K) : ℕ := F.hi i - F.lo i

theorem lo_mem (F : OrderedSquareBlocks N K) (i : Fin K) :
    F.lo i ∈ F.block i := Finset.min'_mem _ _

theorem hi_mem (F : OrderedSquareBlocks N K) (i : Fin K) :
    F.hi i ∈ F.block i := Finset.max'_mem _ _

theorem mem_bounds (F : OrderedSquareBlocks N K)
    (i : Fin K) {a : ℕ} (ha : a ∈ F.block i) :
    F.lo i ≤ a ∧ a ≤ F.hi i := by
  exact ⟨Finset.min'_le _ a ha, Finset.le_max' _ a ha⟩

theorem lo_pos (F : OrderedSquareBlocks N K) (i : Fin K) :
    0 < F.lo i := F.positive i _ (F.lo_mem i)

theorem hi_le (F : OrderedSquareBlocks N K) (i : Fin K) :
    F.hi i ≤ N := F.bounded i _ (F.hi_mem i)

theorem lo_le_hi (F : OrderedSquareBlocks N K) (i : Fin K) :
    F.lo i ≤ F.hi i := (F.mem_bounds i (F.hi_mem i)).1

theorem hi_lt_lo (F : OrderedSquareBlocks N K)
    {i j : Fin K} (hij : i < j) :
    F.hi i < F.lo j :=
  F.ordered i j hij _ (F.hi_mem i) _ (F.lo_mem j)

theorem lo_strictMono (F : OrderedSquareBlocks N K) : StrictMono F.lo := by
  intro i j hij
  exact F.ordered i j hij _ (F.lo_mem i) _ (F.lo_mem j)

/-- Long blocks consume disjoint sets of `H` integer positions in `{1,...,N}`. -/
theorem long_blocks_mul_le (F : OrderedSquareBlocks N K) (H : ℕ) :
    ((Finset.univ.filter (fun i : Fin K => H ≤ F.span i)).card) * H ≤ N := by
  classical
  let L : Finset (Fin K) := Finset.univ.filter (fun i => H ≤ F.span i)
  let domain : Finset (Fin K × ℕ) := L.product (Finset.range H)
  let f : Fin K × ℕ → ℕ := fun z => F.lo z.1 + z.2
  have hmap : Set.MapsTo f domain (Finset.Icc 1 N) := by
    intro z hz
    rcases z with ⟨i, r⟩
    have hzr := Finset.mem_product.mp hz
    have hlong : H ≤ F.hi i - F.lo i := by
      change H ≤ F.span i
      exact (Finset.mem_filter.mp (show i ∈ L from hzr.1)).2
    have hr : r < H := Finset.mem_range.mp hzr.2
    have hlo := F.lo_pos i
    have hhi := F.hi_le i
    have hlohi := F.lo_le_hi i
    change F.lo i + r ∈ Finset.Icc 1 N
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  have hinj : Set.InjOn f (domain : Set (Fin K × ℕ)) := by
    intro z hz w hw heq
    rcases z with ⟨i, r⟩
    rcases w with ⟨j, s⟩
    have hzr := Finset.mem_product.mp hz
    have hws := Finset.mem_product.mp hw
    have hiLong : H ≤ F.hi i - F.lo i := by
      change H ≤ F.span i
      exact (Finset.mem_filter.mp (show i ∈ L from hzr.1)).2
    have hjLong : H ≤ F.hi j - F.lo j := by
      change H ≤ F.span j
      exact (Finset.mem_filter.mp (show j ∈ L from hws.1)).2
    have hr : r < H := Finset.mem_range.mp hzr.2
    have hs : s < H := Finset.mem_range.mp hws.2
    change F.lo i + r = F.lo j + s at heq
    rcases lt_trichotomy i j with hij | hij | hji
    · have hsep := F.hi_lt_lo hij
      have hlohi := F.lo_le_hi i
      omega
    · subst j
      have hrs : r = s := by omega
      subst s
      rfl
    · have hsep := F.hi_lt_lo hji
      have hlohi := F.lo_le_hi j
      omega
  have hc : domain.card ≤ (Finset.Icc 1 N).card :=
    Finset.card_le_card_of_injOn f hmap hinj
  change (L.product (Finset.range H)).card ≤ (Finset.Icc 1 N).card at hc
  change L.card * H ≤ N
  calc
    L.card * H = L.card * (Finset.range H).card :=
      congrArg (fun t : ℕ => L.card * t) (Finset.card_range H).symm
    _ = (L.product (Finset.range H)).card :=
      (Finset.card_product L (Finset.range H)).symm
    _ ≤ (Finset.Icc 1 N).card := hc
    _ = N := by
      simp only [Nat.card_Icc, Nat.add_sub_cancel]

/-- Short blocks have distinct representatives in the explicit finite candidate set. -/
theorem short_blocks_le (F : OrderedSquareBlocks N K) (H : ℕ) :
    (Finset.univ.filter (fun i : Fin K => F.span i < H)).card ≤
      2 ^ H * (Nat.sqrt N + 1) := by
  classical
  let S : Finset (Fin K) := Finset.univ.filter (fun i => F.span i < H)
  have hmap : Set.MapsTo F.lo S (squareCandidates N H) := by
    intro i hi
    have hshort : F.hi i - F.lo i < H := by
      change F.span i < H
      exact (Finset.mem_filter.mp (show i ∈ S from hi)).2
    exact mem_squareCandidates_of_short_block
      (F.positive i) (F.bounded i) (fun a ha => F.mem_bounds i ha)
      hshort (F.square i) (F.lo_mem i)
  have hinj : Set.InjOn F.lo (S : Set (Fin K)) := by
    intro i hi j hj hij
    exact F.lo_strictMono.injective hij
  exact (Finset.card_le_card_of_injOn F.lo hmap hinj).trans
    (card_squareCandidates_le N H)

/-- The principal finite upper bound. It includes `N = 0` and the empty family. -/
theorem finite_upper_bound (F : OrderedSquareBlocks N K)
    (H : ℕ) (hH : 0 < H) :
    K ≤ N / H + 2 ^ H * (Nat.sqrt N + 1) := by
  classical
  let L : Finset (Fin K) := Finset.univ.filter (fun i => H ≤ F.span i)
  let S : Finset (Fin K) := Finset.univ.filter (fun i => F.span i < H)
  have hL : L.card ≤ N / H := by
    apply (Nat.le_div_iff_mul_le hH).mpr
    exact F.long_blocks_mul_le H
  have hS : S.card ≤ 2 ^ H * (Nat.sqrt N + 1) := F.short_blocks_le H
  have hpartition : L.card + S.card = K := by
    simpa only [L, S, not_le, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (fun i : Fin K => H ≤ F.span i))
  omega

/-- A division-free version, useful for casts and subsequent quantitative estimates. -/
theorem finite_upper_bound_mul (F : OrderedSquareBlocks N K)
    (H : ℕ) (hH : 0 < H) :
    H * K ≤ N + H * (2 ^ H * (Nat.sqrt N + 1)) := by
  have h := Nat.mul_le_mul_left H (F.finite_upper_bound H hH)
  have hdiv : H * (N / H) ≤ N := by
    have heq := Nat.mod_add_div N H
    omega
  calc
    H * K ≤ H * (N / H + 2 ^ H * (Nat.sqrt N + 1)) := h
    _ = H * (N / H) + H * (2 ^ H * (Nat.sqrt N + 1)) := by ring
    _ ≤ N + H * (2 ^ H * (Nat.sqrt N + 1)) := Nat.add_le_add_right hdiv _

/-- Explicit uniform density estimate: once `N >= (4*Q*2^(2*Q))^2`, `Q*K <= N`. -/
theorem density_bound (F : OrderedSquareBlocks N K)
    (Q : ℕ) (hQ : 0 < Q)
    (hN : (4 * Q * 2 ^ (2 * Q)) ^ 2 ≤ N) :
    Q * K ≤ N := by
  let C : ℕ := 2 ^ (2 * Q)
  let s : ℕ := Nat.sqrt N
  have hC : 0 < C := by
    dsimp only [C]
    exact pow_pos (by decide : 0 < (2 : ℕ)) _
  have hA : 4 * Q * C ≤ s := by
    apply Nat.le_sqrt'.mpr
    exact hN
  have hs1 : 1 ≤ s := by
    have hQC : 0 < Q * C := Nat.mul_pos hQ hC
    nlinarith only [hQC, hA]
  have hs2 : s * s ≤ N := Nat.sqrt_le N
  have hterm : (2 * Q) * (C * (s + 1)) ≤ N := by
    calc
      (2 * Q) * (C * (s + 1)) ≤ (2 * Q) * (C * (2 * s)) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_left
        omega
      _ = (4 * Q * C) * s := by ring
      _ ≤ s * s := Nat.mul_le_mul_right s hA
      _ ≤ N := hs2
  have hmain := F.finite_upper_bound_mul (2 * Q) (by omega)
  have hmain' : (2 * Q) * K ≤ N + (2 * Q) * (C * (s + 1)) := hmain
  nlinarith only [hmain', hterm]

end OrderedSquareBlocks

/-! ## 4. Uniform epsilon statement and little-o -/

/-- Uniform in the particular block family; this is the epsilon form of the upper bound. -/
theorem uniform_epsilon_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N K : ℕ, N₀ ≤ N →
      ∀ F : OrderedSquareBlocks N K, (K : ℝ) ≤ ε * (N : ℝ) := by
  obtain ⟨Q, hQgt⟩ := exists_nat_gt (1 / ε)
  have hQ : 0 < Q := by
    have hpos : (0 : ℝ) < (Q : ℝ) :=
      lt_trans (one_div_pos.mpr hε) hQgt
    exact_mod_cast hpos
  have hεQ : 1 ≤ ε * (Q : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hQgt
    nlinarith only [h]
  refine ⟨(4 * Q * 2 ^ (2 * Q)) ^ 2, ?_⟩
  intro N K hN F
  have hnat : Q * K ≤ N := F.density_bound Q hQ hN
  have hreal : (Q : ℝ) * (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnat
  calc
    (K : ℝ) = 1 * (K : ℝ) := (one_mul _).symm
    _ ≤ (ε * (Q : ℝ)) * (K : ℝ) :=
      mul_le_mul_of_nonneg_right hεQ (Nat.cast_nonneg K)
    _ = ε * ((Q : ℝ) * (K : ℝ)) := by ring
    _ ≤ ε * (N : ℝ) := mul_le_mul_of_nonneg_left hreal hε.le

/-- Any choice of admissible block counts is little-o of `N`. -/
theorem block_counts_isLittleO (k : ℕ → ℕ)
    (hk : ∀ N, Nonempty (OrderedSquareBlocks N (k N))) :
    (fun N : ℕ => (k N : ℝ)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := uniform_epsilon_bound ε hε
  filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
  obtain ⟨F⟩ := hk N
  have h := hN₀ N (k N) hN F
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (k N) : (0 : ℝ) ≤ (k N : ℝ)),
    abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))] using h

end
end Erdos437Upper
