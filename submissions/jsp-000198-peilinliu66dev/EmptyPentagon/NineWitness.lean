/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/NineWitness.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Forces
import EmptyPentagon.Certificate
import EmptyPentagon.TriangleInterior

noncomputable section
namespace Horton

/-- The nine integer points used as a witness against empty convex pentagons. -/
def ninePoints : Fin 9 → ℤ × ℤ :=
  ![(-28, 22), (-13, -9), (-5, -37), (-4, 3), (-1, -4), (-1, 14), (4, 0), (14, -7), (35, 13)]

/-- Integer orientation determinant, the exact counterpart of `orient`. -/
def orientZ (a b c : ℤ × ℤ) : ℤ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- `p` lies strictly inside the counterclockwise integer triangle `a b c`. -/
abbrev StrictInsideZ (a b c p : ℤ × ℤ) : Prop :=
  0 < orientZ a b c ∧ 0 < orientZ a b p ∧ 0 < orientZ b c p ∧ 0 < orientZ c a p

/-- Some member of `I` lies strictly inside a triangle spanned by three other members. -/
abbrev HasInnerVertex (I : Finset (Fin 9)) : Prop :=
  ∃ p ∈ I, ∃ a ∈ I, ∃ b ∈ I, ∃ c ∈ I, p ≠ a ∧ p ≠ b ∧ p ≠ c ∧
    StrictInsideZ (ninePoints a) (ninePoints b) (ninePoints c) (ninePoints p)

/-- Some index outside `I` lies strictly inside a triangle spanned by three members of `I`. -/
abbrev HasInnerPoint (I : Finset (Fin 9)) : Prop :=
  ∃ p, p ∉ I ∧ ∃ a ∈ I, ∃ b ∈ I, ∃ c ∈ I,
    StrictInsideZ (ninePoints a) (ninePoints b) (ninePoints c) (ninePoints p)

/-- The witness points embedded in the real plane. -/
def nineReal (i : Fin 9) : Point := ((ninePoints i).1, (ninePoints i).2)

/-- The real orientation of embedded witness points is the cast integer orientation. -/
theorem orient_nineReal (i j k : Fin 9) :
    orient (nineReal i) (nineReal j) (nineReal k) =
      (orientZ (ninePoints i) (ninePoints j) (ninePoints k) : ℝ) := by
  simp only [orient, orientZ, nineReal]
  push_cast
  ring

/-- The nine integer points are pairwise distinct. -/
theorem ninePoints_injective : Function.Injective ninePoints := by
  intro i j hij
  revert i j
  decide +kernel

/-- The embedded witness points are pairwise distinct. -/
theorem nineReal_injective : Function.Injective nineReal := by
  intro i j hij
  apply ninePoints_injective
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hij
  simp only [nineReal] at h1 h2
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- No three of the nine integer points are collinear. -/
theorem orientZ_ninePoints_ne_zero : ∀ i j k : Fin 9, i ≠ j → i ≠ k → j ≠ k →
    orientZ (ninePoints i) (ninePoints j) (ninePoints k) ≠ 0 := by
  decide +kernel

/-- Every five-element index set is certified non-empty or non-convex. -/
theorem five_subset_certificate : ∀ I : Finset (Fin 9), I.card = 5 →
    HasInnerVertex I ∨ HasInnerPoint I := by
  decide +kernel

/-- Harborth's bound is sharp: some nine points in general position have no empty convex
pentagon. -/
theorem not_forcesEmptyKGon_five_nine : ¬ ForcesEmptyKGon 5 9 := by
  intro h
  set S : Finset Point := Finset.univ.image nineReal with hS
  have hmem : ∀ i, nineReal i ∈ S := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hcard : S.card = 9 := by
    rw [hS, Finset.card_image_of_injective _ nineReal_injective, Finset.card_univ,
      Fintype.card_fin]
  have hgen : GeneralPosition S := by
    intro a ha b hb c hc hab hac hbc
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hc
    rw [orient_nineReal]
    exact_mod_cast orientZ_ninePoints_ne_zero i j k (ne_of_apply_ne _ hab)
      (ne_of_apply_ne _ hac) (ne_of_apply_ne _ hbc)
  obtain ⟨V, hV5, hVS, hconv, hempty⟩ := h S hcard hgen
  set I : Finset (Fin 9) := Finset.univ.filter (fun i => nineReal i ∈ V) with hI
  have hIV : ∀ i, i ∈ I ↔ nineReal i ∈ V := by
    intro i
    simp [hI]
  have himage : I.image nineReal = V := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (hIV i).mp hi
    · intro hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hVS hx)
      exact Finset.mem_image_of_mem _ ((hIV i).mpr hx)
  have hI5 : I.card = 5 := by
    rw [← hV5, ← himage, Finset.card_image_of_injective _ nineReal_injective]
  have hpos : ∀ i j k : Fin 9, 0 < orientZ (ninePoints i) (ninePoints j) (ninePoints k) →
      0 < orient (nineReal i) (nineReal j) (nineReal k) := by
    intro i j k hijk
    rw [orient_nineReal]
    exact_mod_cast hijk
  rcases five_subset_certificate I hI5 with
    ⟨p, hp, a, ha, b, hb, c, hc, hpa, hpb, hpc, h1, h2, h3, h4⟩ |
    ⟨p, hp, a, ha, b, hb, c, hc, h1, h2, h3, h4⟩
  · exact not_convexIndependent_of_mem_convexHull_triple V (nineReal a) (nineReal b)
      (nineReal c) (nineReal p) ((hIV a).mp ha) ((hIV b).mp hb) ((hIV c).mp hc) ((hIV p).mp hp)
      (nineReal_injective.ne hpa) (nineReal_injective.ne hpb) (nineReal_injective.ne hpc)
      (interior_subset (mem_interior_triangle_of_orient_pos _ _ _ _ (hpos a b c h1)
        (hpos a b p h2) (hpos b c p h3) (hpos c a p h4))) hconv
  · refine hempty (nineReal p) (hmem p) (fun hpV => hp ((hIV p).mpr hpV)) ?_
    refine interior_mono (convexHull_mono ?_)
      (mem_interior_triangle_of_orient_pos _ _ _ _ (hpos a b c h1) (hpos a b p h2)
        (hpos b c p h3) (hpos c a p h4))
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact (hIV a).mp ha
    · exact (hIV b).mp hb
    · exact (hIV c).mp hc

end Horton
