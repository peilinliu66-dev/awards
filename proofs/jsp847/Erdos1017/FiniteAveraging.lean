/-
Copyright (c) 2026. Released under the Apache License 2.0.

Original finite averaging helper for the Erdős 1017 dense partition adapter.
UNCOMPILED: complete source bodies, no claim of kernel verification.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.ByContra

namespace Erdos1017

open scoped BigOperators

/-- At least one member of a finite nonempty family is at least its average.
The multiplied formulation avoids division and is valid over natural numbers. -/
theorem exists_card_mul_ge_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℕ) :
    ∃ i, (∑ j, w j) ≤ Fintype.card ι * w i := by
  classical
  by_contra! h
  have hsum :
      (∑ i : ι, Fintype.card ι * w i) <
        ∑ _i : ι, (∑ j : ι, w j) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (by
      intro i _
      exact h i)
  have hfalse : Fintype.card ι * (∑ i : ι, w i) <
      Fintype.card ι * (∑ i : ι, w i) := by
    simpa only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Nat.nsmul_eq_mul] using hsum
  exact (lt_irrefl _) hfalse

section Translation

variable {A : Type*} [AddGroup A] [Fintype A] [DecidableEq A]

/-- A fixed right translation permutes a finite additive group. -/
theorem sum_right_translate (w : A → ℕ) (b : A) :
    (∑ a : A, w (a + b)) = ∑ a : A, w a := by
  exact Fintype.sum_equiv (Equiv.addRight b) _ _ (fun _ => rfl)

/-- Each color is sampled exactly `T.card` times by the translates of `T`. -/
theorem sum_translate_weight (T : Finset A) (w : A → ℕ) :
    (∑ a : A, ∑ b ∈ T, w (a + b)) =
      T.card * ∑ a : A, w a := by
  classical
  calc
    (∑ a : A, ∑ b ∈ T, w (a + b)) =
        ∑ b ∈ T, ∑ a : A, w (a + b) := Finset.sum_comm
    _ = ∑ _b ∈ T, ∑ a : A, w a := by
      apply Finset.sum_congr rfl
      intro b _
      exact sum_right_translate w b
    _ = T.card * ∑ a : A, w a := by simp

/-- Some translate retains the expected proportion of the total weight. -/
theorem exists_translate_weight (T : Finset A) (w : A → ℕ) :
    ∃ a : A, T.card * (∑ b : A, w b) ≤
      Fintype.card A * (∑ b ∈ T, w (a + b)) := by
  obtain ⟨a, ha⟩ := exists_card_mul_ge_sum
    (fun a : A => ∑ b ∈ T, w (a + b))
  refine ⟨a, ?_⟩
  rwa [sum_translate_weight] at ha

/-- A fixed-size set of colors retaining at least its share of the edge mass.
No ordering of the color classes is needed. -/
theorem exists_weighted_color_subset (w : A → ℕ) (k : ℕ)
    (hk : k ≤ Fintype.card A) :
    ∃ C : Finset A, C.card = k ∧
      k * (∑ a : A, w a) ≤ Fintype.card A * ∑ a ∈ C, w a := by
  classical
  obtain ⟨T, _, hT⟩ := Finset.exists_subset_card_eq
    (show k ≤ (Finset.univ : Finset A).card by simpa using hk)
  obtain ⟨a, ha⟩ := exists_translate_weight T w
  let C := T.image (fun b => a + b)
  have hcard : C.card = T.card := by
    exact Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h)
  have hsum : (∑ c ∈ C, w c) = ∑ b ∈ T, w (a + b) := by
    dsimp [C]
    rw [Finset.sum_image]
    intro b _ c _ h
    exact add_left_cancel h
  refine ⟨C, hcard.trans hT, ?_⟩
  rw [hsum, ← hT]
  exact ha

/-- Equivalent discarded-mass budget, still entirely integral. -/
theorem exists_color_subset_discard_budget (w : A → ℕ) (k : ℕ)
    (hk : k ≤ Fintype.card A) :
    ∃ C : Finset A, C.card = k ∧
      Fintype.card A * (∑ a ∈ Finset.univ \ C, w a) ≤
        (Fintype.card A - k) * (∑ a : A, w a) := by
  classical
  obtain ⟨C, hC, hmass⟩ := exists_weighted_color_subset w k hk
  refine ⟨C, hC, ?_⟩
  have hsplit :
      (∑ a ∈ C, w a) + (∑ a ∈ Finset.univ \ C, w a) =
        ∑ a : A, w a := by
    have hcompl : (Finset.univ : Finset A) \ C = Cᶜ := by
      ext a
      simp
    rw [hcompl]
    exact Finset.sum_add_sum_compl C w
  have hsplit_mul :
      Fintype.card A * (∑ a ∈ C, w a) +
        Fintype.card A * (∑ a ∈ Finset.univ \ C, w a) =
      Fintype.card A * (∑ a : A, w a) := by
    rw [← Nat.mul_add, hsplit]
  have hsub_mul :
      (Fintype.card A - k) * (∑ a : A, w a) +
        k * (∑ a : A, w a) =
      Fintype.card A * (∑ a : A, w a) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hk]
  omega

end Translation

section Colors

variable {V A : Type*} [AddCancelCommMonoid A]

/-- Label-sum coloring is symmetric. -/
theorem sumColor_symm (label : V → A) (u v : V) :
    label u + label v = label v + label u := add_comm _ _

/-- At a fixed endpoint, label-sum colors distinguish all other endpoints.
An injective labeling by `ZMod x` therefore colors a graph on `x` vertices
with `x` matching classes, without invoking Vizing's theorem. -/
theorem sumColor_right_injective (label : V → A)
    (hinj : Function.Injective label) (u : V) :
    Function.Injective (fun v => label u + label v) := by
  intro v w h
  exact hinj (add_left_cancel h)

/-- The same matching property when the shared endpoint occurs on opposite
sides of the two unordered edges. -/
theorem sumColor_common_endpoint (label : V → A)
    (hinj : Function.Injective label) {u v w : V}
    (h : label u + label v = label w + label u) : v = w := by
  exact sumColor_right_injective label hinj u (h.trans (add_comm _ _))

end Colors

end Erdos1017
