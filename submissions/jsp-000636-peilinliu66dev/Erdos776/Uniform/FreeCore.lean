import Erdos776.Uniform.Assembly

/-!
# The explicit free core from Section 15

The upper-core data first makes the complete constant core profile feasible
on `r+5` points.  We then identify its first `r` top-level colex members and
use them to certify an explicit family of `r` free `(r+1)`-sets.
-/

namespace Erdos776.Uniform

open Finset
open Erdos776.Antichain
open Erdos776.KruskalKatona

/-- The upper-core data makes the complete core recurrence fit on `r+5` points. -/
theorem upperCoreChain_is_core_recurrence
    (r : ℕ) (hr : 1 ≤ r) (hupper : HasUpperCoreData r) :
    IsProfileRecurrence (r + 5) 2 (r + 2) (fun _ => r)
      (upperCoreChain r) := by
  obtain ⟨e, hfit, hexcess, heLower, heUpper⟩ := hupper
  refine ⟨upperCoreChain_above_top r,
    (fun i _ hi => upperCoreChain_step r i hi), ?_⟩
  intro i hi2 hii
  by_cases htop : i = r + 3
  · subst i
    simp
  have hiCore : i ≤ r + 2 := by omega
  by_cases hi2eq : i = 2
  · subst i
    have hten : 10 ≤ (r + 4).choose 2 := by
      have hmono := Nat.choose_le_choose 2 (by omega : 5 ≤ r + 4)
      norm_num at hmono
      exact hmono
    have heLt : e < (r + 4).choose 2 := by omega
    have hshell := canonicalShadow_add_shell
      (B := r + 4) (k := 3) (x := e)
      (by omega) (by omega) heLt
    have hshell' : canonicalShadow 3 ((r + 4).choose 3 + e) =
        (r + 4).choose 2 + canonicalShadow 2 e := by
      simpa only [show 3 - 1 = 2 by omega] using hshell
    have hsix : canonicalShadow 2 6 = 4 := by
      rw [show 6 = (4 : ℕ).choose 2 by norm_num [Nat.choose],
        canonicalShadow_choose (by omega) (by omega)]
      norm_num [Nat.choose]
    have hshadowE : canonicalShadow 2 e ≤ 4 := by
      have hm := canonicalShadow_mono 2 (by omega) heUpper
      rw [hsix] at hm
      exact hm
    have hstep : upperCoreChain r 2 =
        r + ((r + 4).choose 2 + canonicalShadow 2 e) := by
      rw [upperCoreChain_step r 2 (by omega), hexcess, hshell']
    have hp : (r + 5).choose 2 =
        (r + 4).choose 1 + (r + 4).choose 2 := by
      simpa only [show r + 5 = r + 4 + 1 by omega] using
        Nat.choose_succ_succ (r + 4) 1
    calc
      upperCoreChain r 2 =
          r + ((r + 4).choose 2 + canonicalShadow 2 e) := hstep
      _ ≤ r + ((r + 4).choose 2 + 4) := by omega
      _ = (r + 5).choose 2 := by
        rw [hp, Nat.choose_one_right]
        omega
  by_cases hi3eq : i = 3
  · subst i
    have hsix : 6 ≤ (r + 4).choose 2 := by
      have hmono := Nat.choose_le_choose 2 (by omega : 4 ≤ r + 4)
      norm_num at hmono
      exact hmono
    have hp : (r + 5).choose 3 =
        (r + 4).choose 2 + (r + 4).choose 3 := by
      simpa only [show r + 5 = r + 4 + 1 by omega] using
        Nat.choose_succ_succ (r + 4) 2
    rw [hexcess, hp]
    omega
  exact (hfit i (by omega) hiCore).trans
    (Nat.choose_le_choose i (by omega : r + 4 ≤ r + 5))

/-- The natural-number representative of the `j`th top core member. -/
def coreTopNatural (r : ℕ) (j : Fin r) : Finset ℕ :=
  (range (r + 3)).erase (j.val + 3)

/-- The `j`th top core member `X \ {j+3}` on `Fin (r+5)`. -/
noncomputable def coreTopSet (r : ℕ) (j : Fin r) :
    Finset (Fin (r + 5)) :=
  finify (r + 5) (coreTopNatural r j)

/-- The proposed free set is obtained by deleting point zero once more. -/
noncomputable def explicitFreeSet (r : ℕ) (j : Fin r) :
    Finset (Fin (r + 5)) :=
  (coreTopSet r j).erase 0

/-- The family of all `r` explicit free sets. -/
noncomputable def explicitFreeFamily (r : ℕ) :
    Family (Fin (r + 5)) :=
  Finset.univ.image (explicitFreeSet r)

theorem coreTopNatural_bounded {r : ℕ} {j : Fin r} :
    ∀ x ∈ coreTopNatural r j, x < r + 5 := by
  intro x hx
  exact (mem_range.mp (mem_of_mem_erase hx)).trans (by omega)

@[simp] theorem card_coreTopSet (r : ℕ) (j : Fin r) :
    (coreTopSet r j).card = r + 2 := by
  rw [coreTopSet, card_finify coreTopNatural_bounded,
    coreTopNatural, card_erase_of_mem (mem_range.mpr (by omega)), card_range]
  omega

@[simp] theorem zero_mem_coreTopSet (r : ℕ) (j : Fin r) :
    (0 : Fin (r + 5)) ∈ coreTopSet r j := by
  simp [coreTopSet, coreTopNatural]

@[simp] theorem card_explicitFreeSet (r : ℕ) (j : Fin r) :
    (explicitFreeSet r j).card = r + 1 := by
  rw [explicitFreeSet, card_erase_of_mem (zero_mem_coreTopSet r j),
    card_coreTopSet]
  omega

theorem explicitFreeSet_subset_coreTopSet (r : ℕ) (j : Fin r) :
    explicitFreeSet r j ⊆ coreTopSet r j := by
  exact erase_subset _ _

theorem coreTopSet_not_subset_explicitFreeSet (r : ℕ) (j : Fin r) :
    ¬ coreTopSet r j ⊆ explicitFreeSet r j := by
  intro hsub
  exact (notMem_erase 0 (coreTopSet r j))
    (hsub (zero_mem_coreTopSet r j))

theorem explicitFreeSet_injective (r : ℕ) :
    Function.Injective (explicitFreeSet r) := by
  intro i j hij
  apply Fin.ext
  by_contra hval
  let p : Fin (r + 5) := ⟨i.val + 3, by omega⟩
  have hpi : p ∉ explicitFreeSet r i := by
    simp [p, explicitFreeSet, coreTopSet, coreTopNatural]
  have hpj : p ∈ explicitFreeSet r j := by
    simp [p, explicitFreeSet, coreTopSet, coreTopNatural]
    exact hval
  rw [hij] at hpi
  exact hpi hpj

@[simp] theorem card_explicitFreeFamily (r : ℕ) :
    (explicitFreeFamily r).card = r := by
  rw [explicitFreeFamily, card_image_of_injective _
    (explicitFreeSet_injective r)]
  simp

theorem explicitFreeFamily_sized (r : ℕ) :
    (explicitFreeFamily r : Set (Finset (Fin (r + 5)))).Sized (r + 1) := by
  intro d hd
  obtain ⟨j, -, rfl⟩ := mem_image.mp hd
  exact card_explicitFreeSet r j

/-- The top state of the complete core recurrence is exactly `r`. -/
@[simp] theorem upperCoreChain_at_top (r : ℕ) :
    upperCoreChain r (r + 2) = r := by
  rw [upperCoreChain_step r (r + 2) (by omega),
    upperCoreChain_above_top, canonicalShadow_zero]
  omega

theorem coreTopSet_mem_canonicalFamily (r : ℕ) (j : Fin r) :
    coreTopSet r j ∈ canonicalFamily (r + 5) (r + 2) r := by
  have hcanon : IsCanonical (r + 2) (diagonalDigits (r + 2) r) :=
    isCanonical_diagonalDigits (by omega)
  have hvalue : cascadeValue (r + 2) (diagonalDigits (r + 2) r) = r :=
    cascadeValue_diagonalDigits (by omega)
  have hdigits : canonicalDigits (r + 2) r = diagonalDigits (r + 2) r :=
    (canonicalDigits_unique hcanon hvalue).symm
  have hmem : coreTopNatural r j ∈
      cascadeFamily (r + 2) (diagonalDigits (r + 2) r) := by
    exact erase_range_mem_cascadeFamily_diagonalDigits
      (by omega) (by omega) (by omega)
  rw [canonicalFamily, hdigits, finifyFamily]
  exact mem_image.mpr ⟨coreTopNatural r j, hmem, rfl⟩

/-- The canonical constant-profile core used in Section 15. -/
noncomputable def canonicalCore (r : ℕ) : Family (Fin (r + 5)) :=
  profileFamily (r + 5) 2 (r + 2) (upperCoreChain r)

theorem coreTopSet_mem_canonicalCore (r : ℕ) (j : Fin r) :
    coreTopSet r j ∈ canonicalCore r := by
  apply mem_profileFamily.mpr
  refine ⟨r + 2, mem_Icc.mpr ⟨by omega, le_rfl⟩, ?_⟩
  have htop := coreTopSet_mem_canonicalFamily r j
  have hempty : canonicalFamily (r + 5) (r + 3) 0 = ∅ := by
    apply card_eq_zero.mp
    exact card_canonicalFamily
      (n := r + 5) (k := r + 3) (m := 0)
      (by omega) (Nat.zero_le _)
  rw [selectedLayer, upperCoreChain_at_top,
    upperCoreChain_above_top, hempty]
  simpa using htop

/-- Any capacity proof for the core recurrence gives the required core profile. -/
theorem canonicalCore_spec_of_recurrence
    (r : ℕ)
    (hrec : IsProfileRecurrence (r + 5) 2 (r + 2) (fun _ => r)
      (upperCoreChain r)) :
    IsSperner (canonicalCore r) ∧
      HasMultiplicities (canonicalCore r) r 2 (r + 2) := by
  constructor
  · exact isSperner_profileFamily (by omega) hrec
  · intro i hi2 hir
    unfold HasMultiplicityAt
    rw [canonicalCore, level_profileFamily (by omega) hrec hi2 hir,
      card_selectedLayer (by omega) hrec hi2 hir]

/-- The canonical core is an antichain with exactly `r` members per level. -/
theorem canonicalCore_spec
    (r : ℕ) (hr : 1 ≤ r) (hupper : HasUpperCoreData r) :
    IsSperner (canonicalCore r) ∧
      HasMultiplicities (canonicalCore r) r 2 (r + 2) := by
  exact canonicalCore_spec_of_recurrence r
    (upperCoreChain_is_core_recurrence r hr hupper)

/-- Antichainness alone makes every displayed `D_j` free for the core. -/
theorem explicitFreeFamily_isFree_of_isSperner
    (r : ℕ) (hanti : IsSperner (canonicalCore r)) :
    IsFreeFamily (canonicalCore r) (explicitFreeFamily r) := by
  intro d hd
  obtain ⟨j, -, rfl⟩ := mem_image.mp hd
  intro c hc hcd
  have htop : coreTopSet r j ∈ canonicalCore r :=
    coreTopSet_mem_canonicalCore r j
  have hctop : c ⊆ coreTopSet r j :=
    hcd.trans (explicitFreeSet_subset_coreTopSet r j)
  have heq : c = coreTopSet r j := hanti.eq hc htop hctop
  apply coreTopSet_not_subset_explicitFreeSet r j
  simpa [heq] using hcd

/-- Every displayed set `D_j` is free for the entire canonical core. -/
theorem explicitFreeFamily_isFree
    (r : ℕ) (hr : 1 ≤ r) (hupper : HasUpperCoreData r) :
    IsFreeFamily (canonicalCore r) (explicitFreeFamily r) := by
  exact explicitFreeFamily_isFree_of_isSperner r
    (canonicalCore_spec r hr hupper).1

/-- Any feasible canonical core recurrence carries the explicit free family. -/
theorem hasSuitableFreeCore_of_recurrence
    (r : ℕ)
    (hrec : IsProfileRecurrence (r + 5) 2 (r + 2) (fun _ => r)
      (upperCoreChain r)) :
    HasSuitableFreeCore r := by
  have hspec := canonicalCore_spec_of_recurrence r hrec
  refine ⟨canonicalCore r, explicitFreeFamily r,
    hspec.1, hspec.2, explicitFreeFamily_sized r, ?_,
    explicitFreeFamily_isFree_of_isSperner r hspec.1⟩
  rw [card_explicitFreeFamily]

/-- Section 15 supplies the suitable free core required by the assembly. -/
theorem hasSuitableFreeCore_of_upperCoreData
    (r : ℕ) (hr : 1 ≤ r) (hupper : HasUpperCoreData r) :
    HasSuitableFreeCore r := by
  have hspec := canonicalCore_spec r hr hupper
  refine ⟨canonicalCore r, explicitFreeFamily r,
    hspec.1, hspec.2, explicitFreeFamily_sized r, ?_,
    explicitFreeFamily_isFree r hr hupper⟩
  rw [card_explicitFreeFamily]

/--
After formalizing the free core, upper-core data is the sole remaining input
to the full middle-profile threshold for the symbolic range.
-/
theorem fullMiddleProfileThreshold_of_upperCoreData
    (r : ℕ) (hr : 29 ≤ r) (hupper : HasUpperCoreData r) :
    FullMiddleProfileThreshold r := by
  exact uniform_profile_threshold_from_components r hr hupper
    (hasSuitableFreeCore_of_upperCoreData r (by omega) hupper)

end Erdos776.Uniform
