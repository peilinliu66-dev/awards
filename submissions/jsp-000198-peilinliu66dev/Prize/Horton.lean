/-
Copyright (c) 2026 JSP-000198 formalization contributors.
Released under the MIT license; see Prize/LICENSE_MIT.
Adapted from tester-lean/jsp-000198-horton-lean,
commit 313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0.
Mathematical construction: J. D. Horton.
Local port to Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/

import Prize.Horton.Construction
import Prize.Horton.GeneralPosition
import Prize.Horton.NoEmptySeven

/-!
# Horton's theorem: arbitrarily large sets with no empty convex seven-gon

This formalizes the k ≥ 7 part of JSP-000198 / Erdős problem 216, following
J. D. Horton's recursive construction. It does not establish the finite
pentagon or hexagon thresholds grouped into the same catalog entry.
-/

namespace Prize.Horton

open Prize.Geometry

/-- Passing to an initial segment in increasing horizontal order preserves
the absence of empty polygons. Points removed to its right cannot fill a hole. -/
theorem IsHorton.prefix_emptyConvex_card_le_six {depth N : ℕ} {p : ℕ → Point}
    (hh : IsHorton depth p) (hx : ∀ i, (p i).1 = i) (hN : N ≤ 2 ^ depth)
    {V : Finset Point} (he : EmptyConvex (p '' Set.Iio N) (V : Set Point)) :
    V.card ≤ 6 := by
  have hinj : Function.Injective p := by
    intro i j hij
    have hxij := congrArg Prod.fst hij
    rw [hx i, hx j] at hxij
    exact_mod_cast hxij
  have hsub : p '' Set.Iio N ⊆ p '' Set.Iio (2 ^ depth) :=
    Set.image_mono (fun _ hi => lt_of_lt_of_le hi hN)
  have hhalf : Convex ℝ {x : Point | x.1 < (N : ℝ)} :=
    (convex_Iio (N : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  have hverts : (V : Set Point) ⊆ {x : Point | x.1 < (N : ℝ)} := by
    intro x hxV
    obtain ⟨i, hi, rfl⟩ := he.subset hxV
    change (p i).1 < (N : ℝ)
    rw [hx i]
    exact_mod_cast hi
  have hhull := convexHull_min hverts hhalf
  apply hh.emptyConvex_card_le_six hinj.injOn
  refine ⟨he.subset.trans hsub, he.convexIndependent, ?_⟩
  intro x hxP hxHull
  obtain ⟨i, hi, rfl⟩ := hxP
  have hxi : (p i).1 < (N : ℝ) := hhull (interior_subset hxHull)
  rw [hx i] at hxi
  have hiN : i < N := by exact_mod_cast hxi
  exact he.empty _ (Set.mem_image_of_mem p hiN) hxHull

/-- For every prescribed cardinality there is an integer-coordinate point set
in general position with no empty convex seven-gon. -/
theorem horton_no_empty_seven (N : ℕ) :
    ∃ P : Finset Point, P.card = N ∧ GeneralPosition (P : Set Point) ∧
      ¬HasEmptyKGon 7 P ∧
      (∀ q ∈ P, ∃ x y : ℤ, q = ((x : ℝ), (y : ℝ))) := by
  classical
  obtain ⟨p, hh, hx, hy⟩ := exists_horton_integer N
  let P := (Finset.range N).image p
  have hP : (P : Set Point) = p '' Set.Iio N := by
    ext q
    simp [P]
  have hinj : Function.Injective p := by
    intro i j hij
    have heq := congrArg Prod.fst hij
    rw [hx i, hx j] at heq
    exact_mod_cast heq
  have hN : N ≤ 2 ^ N := Nat.le_of_lt Nat.lt_two_pow_self
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · simp [P, Finset.card_image_of_injective _ hinj]
  · rw [hP]
    exact hh.generalPosition.mono (Set.image_mono (fun _ hi => lt_of_lt_of_le hi hN))
  · rintro ⟨V, hV, he⟩
    rw [hP] at he
    have hc := hh.prefix_emptyConvex_card_le_six hx hN he
    omega
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨z, hz⟩ := hy i
    refine ⟨Int.ofNat i, z, ?_⟩
    apply Prod.ext
    · simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using hx i
    · exact hz

/-- The same configurations exclude every larger empty convex polygon. -/
theorem horton_no_empty_k_gon (N k : ℕ) (hk : 7 ≤ k) :
    ∃ P : Finset Point, P.card = N ∧ GeneralPosition (P : Set Point) ∧
      ¬HasEmptyKGon k P ∧
      (∀ q ∈ P, ∃ x y : ℤ, q = ((x : ℝ), (y : ℝ))) := by
  obtain ⟨P, hcard, hgp, hno, hint⟩ := horton_no_empty_seven N
  exact ⟨P, hcard, hgp, fun hp => hno (hp.of_le hk), hint⟩

theorem no_finite_threshold {k : ℕ} (hk : 7 ≤ k) : ∀ N, ¬ForcesEmptyKGon N k := by
  intro N hN
  obtain ⟨P, hcard, hgp, hno, _⟩ := horton_no_empty_k_gon N k hk
  exact hno (hN P (by omega) hgp)

end Prize.Horton

#print axioms Prize.Horton.horton_no_empty_k_gon
#print axioms Prize.Horton.no_finite_threshold
