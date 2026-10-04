import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic

/-!
# Coordinate symmetrization: finite set geometry

Initially prepared 2026-10-04; compiled foundation, see the build evidence.

This file contains only the elementary geometric first layer of the finite
Anderson proof. No volume theorem or Gaussian comparison is assumed here,
and no final Erdős theorem is declared.
-/

namespace Erdos524.CoordinateSymmetrization

open Set

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Vec (ι : Type*) := ι → ℝ

/-- Keep the common off-coordinate fiber and center its one-dimensional
difference interval. -/
def centerFiber (i : ι) (p q : Vec ι) : Vec ι :=
  fun j ↦ if j = i then (p j - q j) / 2 else p j

/-- Reflection in one coordinate hyperplane. -/
def reflect (i : ι) (x : Vec ι) : Vec ι :=
  fun j ↦ if j = i then -x j else x j

/-- Coordinate symmetrization, expressed without fiber endpoint functions. -/
def symm (i : ι) (A : Set (Vec ι)) : Set (Vec ι) :=
  {x | ∃ p ∈ A, ∃ q ∈ A,
    (∀ j, j ≠ i → p j = q j) ∧ centerFiber i p q = x}

/-- The pointwise difference set, with explicit witnesses. -/
def difference (A B : Set (Vec ι)) : Set (Vec ι) :=
  {x | ∃ a ∈ A, ∃ b ∈ B, a - b = x}

def InvariantIn (i : ι) (A : Set (Vec ι)) : Prop :=
  ∀ ⦃x⦄, x ∈ A → reflect i x ∈ A

theorem symm_mono (i : ι) {A B : Set (Vec ι)} (hAB : A ⊆ B) :
    symm i A ⊆ symm i B := by
  rintro x ⟨p, hp, q, hq, hpq, hpx⟩
  exact ⟨p, hAB hp, q, hAB hq, hpq, hpx⟩

theorem difference_mono {A B C D : Set (Vec ι)}
    (hAC : A ⊆ C) (hBD : B ⊆ D) :
    difference A B ⊆ difference C D := by
  rintro x ⟨a, ha, b, hb, hab⟩
  exact ⟨a, hAC ha, b, hBD hb, hab⟩

theorem centerFiber_swap (i : ι) (p q : Vec ι)
    (hpq : ∀ j, j ≠ i → p j = q j) :
    centerFiber i q p = reflect i (centerFiber i p q) := by
  ext j
  by_cases hji : j = i
  · simp only [centerFiber, reflect, if_pos hji]
    ring
  · simpa only [centerFiber, reflect, if_neg hji] using (hpq j hji).symm

theorem reflect_involutive (i : ι) : Function.Involutive (reflect i) := by
  intro x
  ext j
  by_cases hji : j = i <;> simp [reflect, hji]

theorem invariant_symm (i : ι) (A : Set (Vec ι)) :
    InvariantIn i (symm i A) := by
  rintro x ⟨p, hp, q, hq, hpq, rfl⟩
  exact ⟨q, hq, p, hp, fun j hj ↦ (hpq j hj).symm,
    centerFiber_swap i p q hpq⟩

theorem centerFiber_reflect (i j : ι) (hji : j ≠ i) (p q : Vec ι) :
    centerFiber i (reflect j p) (reflect j q) =
      reflect j (centerFiber i p q) := by
  ext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [centerFiber, reflect] <;> ring

theorem invariant_symm_of_ne (i j : ι) (hji : j ≠ i)
    {A : Set (Vec ι)} (hA : InvariantIn j A) :
    InvariantIn j (symm i A) := by
  rintro x ⟨p, hp, q, hq, hpq, rfl⟩
  refine ⟨reflect j p, hA hp, reflect j q, hA hq, ?_,
    centerFiber_reflect i j hji p q⟩
  intro k hki
  by_cases hkj : k = j
  · subst k
    simp [reflect, hpq j hji]
  · simp [reflect, hkj, hpq k hki]

theorem centerFiber_add_smul (i : ι) (p q r s : Vec ι) (a b : ℝ) :
    centerFiber i (a • p + b • r) (a • q + b • s) =
      a • centerFiber i p q + b • centerFiber i r s := by
  ext j
  by_cases hji : j = i <;> simp [centerFiber, hji] <;> ring

theorem convex_symm (i : ι) {A : Set (Vec ι)} (hA : Convex ℝ A) :
    Convex ℝ (symm i A) := by
  rintro x ⟨p, hp, q, hq, hpq, rfl⟩
    y ⟨r, hr, s, hs, hrs, rfl⟩ a b ha hb hab
  refine ⟨a • p + b • r, hA hp hr ha hb hab,
    a • q + b • s, hA hq hs ha hb hab, ?_,
    centerFiber_add_smul i p q r s a b⟩
  intro j hji
  change a * p j + b * r j = a * q j + b * s j
  rw [hpq j hji, hrs j hji]

theorem continuous_centerFiber (i : ι) :
    Continuous (fun z : Vec ι × Vec ι ↦ centerFiber i z.1 z.2) := by
  apply continuous_pi
  intro j
  by_cases hji : j = i <;> simp only [centerFiber, hji, if_true, if_false] <;>
    fun_prop

theorem isClosed_sameOff (i : ι) :
    IsClosed {z : Vec ι × Vec ι | ∀ j, j ≠ i → z.1 j = z.2 j} := by
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro hji
  exact isClosed_eq (by fun_prop) (by fun_prop)

theorem symm_eq_image (i : ι) (A : Set (Vec ι)) :
    symm i A =
      (fun z : Vec ι × Vec ι ↦ centerFiber i z.1 z.2) ''
        ((A ×ˢ A) ∩ {z | ∀ j, j ≠ i → z.1 j = z.2 j}) := by
  ext x
  constructor
  · rintro ⟨p, hp, q, hq, hpq, hpx⟩
    exact ⟨(p, q), ⟨⟨hp, hq⟩, hpq⟩, hpx⟩
  · rintro ⟨⟨p, q⟩, ⟨⟨hp, hq⟩, hpq⟩, hpx⟩
    exact ⟨p, hp, q, hq, hpq, hpx⟩

theorem isCompact_symm (i : ι) {A : Set (Vec ι)} (hA : IsCompact A) :
    IsCompact (symm i A) := by
  rw [symm_eq_image]
  exact ((hA.prod hA).inter_right (isClosed_sameOff i)).image
    (continuous_centerFiber i)

theorem centerFiber_sub (i : ι) (p q r s : Vec ι) :
    centerFiber i (p - r) (q - s) =
      centerFiber i p q - centerFiber i r s := by
  ext j
  by_cases hji : j = i <;> simp [centerFiber, hji] <;> ring

/-- The key inclusion follows by subtracting the two witness pairs. -/
theorem difference_symm_subset (i : ι) (A B : Set (Vec ι)) :
    difference (symm i A) (symm i B) ⊆ symm i (difference A B) := by
  rintro x ⟨u, ⟨p, hp, q, hq, hpq, rfl⟩,
    v, ⟨r, hr, s, hs, hrs, rfl⟩, rfl⟩
  refine ⟨p - r, ⟨p, hp, r, hr, rfl⟩,
    q - s, ⟨q, hq, s, hs, rfl⟩, ?_, centerFiber_sub i p q r s⟩
  intro j hji
  change p j - r j = q j - s j
  rw [hpq j hji, hrs j hji]

/-- Previously obtained coordinate symmetries survive every new step. -/
theorem invariant_symm_of_invariant (i j : ι) {A : Set (Vec ι)}
    (hA : InvariantIn j A) : InvariantIn j (symm i A) := by
  by_cases hji : j = i
  · subst j
    exact invariant_symm i A
  · exact invariant_symm_of_ne i j hji hA

/-- Perform a finite sequence of coordinate symmetrizations. -/
def symmList : List ι → Set (Vec ι) → Set (Vec ι)
  | [], A => A
  | i :: is, A => symmList is (symm i A)

theorem symmList_mono (is : List ι) {A B : Set (Vec ι)} (hAB : A ⊆ B) :
    symmList is A ⊆ symmList is B := by
  induction is generalizing A B with
  | nil => exact hAB
  | cons i is ih => exact ih (symm_mono i hAB)

theorem convex_symmList (is : List ι) {A : Set (Vec ι)} (hA : Convex ℝ A) :
    Convex ℝ (symmList is A) := by
  induction is generalizing A with
  | nil => exact hA
  | cons i is ih => exact ih (convex_symm i hA)

theorem isCompact_symmList (is : List ι) {A : Set (Vec ι)} (hA : IsCompact A) :
    IsCompact (symmList is A) := by
  induction is generalizing A with
  | nil => exact hA
  | cons i is ih => exact ih (isCompact_symm i hA)

theorem invariant_symmList (j : ι) (is : List ι) {A : Set (Vec ι)}
    (hA : InvariantIn j A) : InvariantIn j (symmList is A) := by
  induction is generalizing A with
  | nil => exact hA
  | cons i is ih => exact ih (invariant_symm_of_invariant i j hA)

theorem invariant_symmList_of_mem (j : ι) (is : List ι)
    (hj : j ∈ is) (A : Set (Vec ι)) : InvariantIn j (symmList is A) := by
  induction is generalizing A with
  | nil => simp at hj
  | cons i is ih =>
      rcases List.mem_cons.mp hj with hji | hrest
      · subst j
        exact invariant_symmList i is (invariant_symm i A)
      · exact ih hrest (symm i A)

theorem difference_symmList_subset (is : List ι) (A B : Set (Vec ι)) :
    difference (symmList is A) (symmList is B) ⊆
      symmList is (difference A B) := by
  induction is generalizing A B with
  | nil => exact Subset.rfl
  | cons i is ih =>
      exact (ih (symm i A) (symm i B)).trans
        (symmList_mono is (difference_symm_subset i A B))

/-- Simultaneously reflect a finite set of coordinates. -/
def reflectSet (s : Finset ι) (x : Vec ι) : Vec ι :=
  fun j ↦ if j ∈ s then -x j else x j

theorem reflectSet_insert (i : ι) (s : Finset ι) (hi : i ∉ s) (x : Vec ι) :
    reflectSet (insert i s) x = reflect i (reflectSet s x) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [reflectSet, reflect, hi]
  · simp [reflectSet, reflect, hji]

theorem reflectSet_mem {A : Set (Vec ι)}
    (hA : ∀ i, InvariantIn i A) (s : Finset ι) {x : Vec ι} (hx : x ∈ A) :
    reflectSet s x ∈ A := by
  induction s using Finset.induction_on with
  | empty =>
      have hempty : reflectSet (∅ : Finset ι) x = x := by
        ext j
        simp [reflectSet]
      rw [hempty]
      exact hx
  | @insert i s hi ih =>
      rw [reflectSet_insert i s hi]
      exact hA i ih

theorem neg_mem_of_invariant {A : Set (Vec ι)}
    (hA : ∀ i, InvariantIn i A) {x : Vec ι} (hx : x ∈ A) : -x ∈ A := by
  have huniv : reflectSet Finset.univ x = -x := by
    ext j
    simp [reflectSet]
  rw [← huniv]
  exact reflectSet_mem hA Finset.univ hx

theorem neg_mem_symmList (is : List ι) (his : ∀ i, i ∈ is)
    (A : Set (Vec ι)) {x : Vec ι} (hx : x ∈ symmList is A) :
    -x ∈ symmList is A := by
  exact neg_mem_of_invariant
    (fun i ↦ invariant_symmList_of_mem i is (his i) A) hx

/-- A centrally symmetric convex body's difference set is its double. -/
theorem difference_self_eq_double {A : Set (Vec ι)} (hA : Convex ℝ A)
    (hneg : ∀ ⦃x⦄, x ∈ A → -x ∈ A) :
    difference A A = (fun x : Vec ι ↦ (2 : ℝ) • x) '' A := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨(1 / 2 : ℝ) • a + (1 / 2 : ℝ) • (-b),
      hA ha (hneg hb) (by norm_num) (by norm_num) (by norm_num), ?_⟩
    ext j
    simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Pi.sub_apply,
      smul_eq_mul]
    ring
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ha, -a, hneg ha, ?_⟩
    ext j
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Finite symmetrization sends the original difference body onto a set
containing twice the symmetrized original body. Volume comparison is the
separate next module; it is not assumed here. -/
theorem double_symmList_subset (is : List ι) (his : ∀ i, i ∈ is)
    {A : Set (Vec ι)} (hA : Convex ℝ A) :
    (fun x : Vec ι ↦ (2 : ℝ) • x) '' symmList is A ⊆
      symmList is (difference A A) := by
  rw [← difference_self_eq_double (convex_symmList is hA)
    (fun _ hx ↦ neg_mem_symmList is his A hx)]
  exact difference_symmList_subset is A A

end

end Erdos524.CoordinateSymmetrization
