/-
Copyright (c) 2026 JSP-000198 formalization contributors.
Released under the MIT license; see Prize/LICENSE_MIT.
Adapted from tester-lean/jsp-000198-horton-lean,
commit 313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0.
Mathematical construction: J. D. Horton.
Local port to Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/

import Mathlib.Analysis.Convex.Independent
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# Empty convex polygons in the real plane

The statements use mathlib's `Collinear`, `ConvexIndependent`, `convexHull`,
and topological `interior`. Emptiness is defined by the polygon's interior,
as in the original mathematical problem.
-/

namespace Prize.Geometry

abbrev Point := ℝ × ℝ

/-- Twice the signed area of the ordered triangle `a b c`. -/
def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

@[simp] theorem orient_self_left (a b : Point) : orient a a b = 0 := by
  simp [orient]

@[simp] theorem orient_self_right (a b : Point) : orient a b b = 0 := by
  unfold orient
  ring

@[simp] theorem orient_self_outer (a b : Point) : orient a b a = 0 := by
  simp [orient]

theorem orient_swap (a b c : Point) : orient b a c = -orient a b c := by
  unfold orient
  ring

theorem orient_cycle (a b c : Point) : orient b c a = orient a b c := by
  unfold orient
  ring

theorem orient_swap_right (a b c : Point) : orient a c b = -orient a b c := by
  unfold orient
  ring

theorem orient_add (a b c x : Point) :
    orient a b x + orient b c x + orient c a x = orient a b c := by
  unfold orient
  ring

theorem orient_eq_zero_of_collinear {a b c : Point}
    (h : Collinear ℝ ({a, b, c} : Set Point)) : orient a b c = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (k := ℝ)
    (show a ∈ ({a, b, c} : Set Point) by simp)).mp h
  obtain ⟨s, rfl⟩ := hv b (by simp)
  obtain ⟨t, rfl⟩ := hv c (by simp)
  simp only [orient, vadd_eq_add, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem not_collinear_of_orient_ne_zero {a b c : Point}
    (h : orient a b c ≠ 0) : ¬Collinear ℝ ({a, b, c} : Set Point) :=
  fun hc => h (orient_eq_zero_of_collinear hc)

/-- Consistent positive orientations put a point in the triangle's convex hull. -/
theorem mem_triangle_of_orient_pos {a b c x : Point}
    (habc : 0 < orient a b c) (habx : 0 < orient a b x)
    (hbcx : 0 < orient b c x) (hcax : 0 < orient c a x) :
    x ∈ convexHull ℝ ({a, b, c} : Set Point) := by
  let w : Fin 3 → ℝ := ![orient b c x / orient a b c,
    orient c a x / orient a b c, orient a b x / orient a b c]
  let v : Fin 3 → Point := ![a, b, c]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i hi
    fin_cases i
    · exact le_of_lt (div_pos hbcx habc)
    · exact le_of_lt (div_pos hcax habc)
    · exact le_of_lt (div_pos habx habc)
  have hsum : ∑ i : Fin 3, w i = 1 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, w,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    have h := orient_add a b c x
    field_simp
    linarith
  have hv : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      v i ∈ convexHull ℝ ({a, b, c} : Set Point) := by
    intro i hi
    apply subset_convexHull
    fin_cases i <;> simp [v]
  have hc := (convex_convexHull ℝ ({a, b, c} : Set Point)).sum_mem hw hsum hv
  have hrepr : (∑ i : Fin 3, w i • v i) = x := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, w, v,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    all_goals
      field_simp
      unfold orient
      ring
  exact hrepr ▸ hc

/-- Strict orientation inequalities put a point in the actual topological
interior of the triangle, not merely its closed convex hull. -/
theorem mem_interior_triangle_of_orient_pos {a b c x : Point}
    (habc : 0 < orient a b c) (habx : 0 < orient a b x)
    (hbcx : 0 < orient b c x) (hcax : 0 < orient c a x) :
    x ∈ interior (convexHull ℝ ({a, b, c} : Set Point)) := by
  let U : Set Point := {y | 0 < orient a b y ∧ 0 < orient b c y ∧ 0 < orient c a y}
  have hcont (u v : Point) : Continuous (fun y : Point => orient u v y) := by
    unfold orient
    fun_prop
  have hopen : IsOpen U := (isOpen_lt continuous_const (hcont a b)).inter
    ((isOpen_lt continuous_const (hcont b c)).inter (isOpen_lt continuous_const (hcont c a)))
  have hsub : U ⊆ convexHull ℝ ({a, b, c} : Set Point) := by
    intro y hy
    exact mem_triangle_of_orient_pos habc hy.1 hy.2.1 hy.2.2
  apply interior_mono hsub
  rw [hopen.interior_eq]
  exact ⟨habx, hbcx, hcax⟩

/-- No three distinct points of the set lie on a line. -/
def GeneralPosition (P : Set Point) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P,
    a ≠ b → a ≠ c → b ≠ c → ¬Collinear ℝ ({a, b, c} : Set Point)

theorem GeneralPosition.mono {P Q : Set Point} (h : GeneralPosition P)
    (hQP : Q ⊆ P) : GeneralPosition Q := by
  intro a ha b hb c hc hab hac hbc
  exact h a (hQP ha) b (hQP hb) c (hQP hc) hab hac hbc

/-- `S` is the vertex set of a convex polygon empty relative to `P`.
The cardinality is imposed separately in `HasEmptyKGon`. -/
structure EmptyConvex (P S : Set Point) : Prop where
  subset : S ⊆ P
  convexIndependent : ConvexIndependent ℝ ((↑) : S → Point)
  empty : ∀ x ∈ P, x ∈ interior (convexHull ℝ S) → x ∈ S

theorem EmptyConvex.vertices_subset {P S T : Set Point}
    (h : EmptyConvex P S) (hTS : T ⊆ S) : EmptyConvex P T := by
  refine ⟨hTS.trans h.subset, h.convexIndependent.mono hTS, ?_⟩
  intro x hx hxT
  have hxS := h.empty x hx (interior_mono (convexHull_mono hTS) hxT)
  exact (convexIndependent_set_iff_inter_convexHull_subset.mp
    h.convexIndependent) T hTS ⟨hxS, interior_subset hxT⟩

theorem EmptyConvex.ambient_subset {P Q S : Set Point}
    (h : EmptyConvex P S) (hQP : Q ⊆ P) (hSQ : S ⊆ Q) : EmptyConvex Q S :=
  ⟨hSQ, h.convexIndependent, fun x hx => h.empty x (hQP hx)⟩

theorem EmptyConvex.triangle_empty {P S : Set Point} (h : EmptyConvex P S)
    {a b c x : Point} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hx : x ∈ P) (htri : x ∈ interior (convexHull ℝ ({a, b, c} : Set Point))) :
    x ∈ ({a, b, c} : Set Point) := by
  have ht : ({a, b, c} : Set Point) ⊆ S := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  exact (h.vertices_subset ht).empty x hx htri

def HasEmptyKGon (k : ℕ) (P : Finset Point) : Prop :=
  ∃ S : Finset Point, S.card = k ∧ EmptyConvex (P : Set Point) (S : Set Point)

theorem HasEmptyKGon.of_le {k m : ℕ} {P : Finset Point}
    (h : HasEmptyKGon m P) (hkm : k ≤ m) : HasEmptyKGon k P := by
  obtain ⟨S, hS, hSP⟩ := h
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (hS ▸ hkm)
  exact ⟨T, hT, hSP.vertices_subset hTS⟩

/-- The threshold property is phrased for all finite sets of at least `N` points. -/
def ForcesEmptyKGon (N k : ℕ) : Prop :=
  ∀ P : Finset Point, N ≤ P.card → GeneralPosition (P : Set Point) → HasEmptyKGon k P

def IsHoleNumber (k N : ℕ) : Prop :=
  ForcesEmptyKGon N k ∧ ∀ M < N, ¬ForcesEmptyKGon M k

end Prize.Geometry
