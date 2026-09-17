import Erdos776.Combinatorics.Antichain
import Mathlib.Data.Finset.Sups
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Lean.Elab.Tactic.Omega

/-!
# The core-to-full construction

A core antichain supplies levels `2, ..., ⌊n/2⌋-1`.  We adjoin a pivot and
private points, attach the pivot to every core member, add the private pairs,
and finally take these lower members together with their complements.  The
result supplies every level `2, ..., n-2`.

The ground set is given a named decomposition into core points, one pivot,
`r` private points, and arbitrary spare points.  This makes the construction
fully explicit and avoids cardinality-choice axioms.
-/

namespace Erdos776.Antichain

open Finset

/-- Named ground set for the core-to-full construction. -/
abbrev CoreGround (α : Type*) (r : ℕ) (γ : Type*) :=
  α ⊕ (Unit ⊕ (Fin r ⊕ γ))

variable {α γ : Type*} [Fintype α] [DecidableEq α]
  [Fintype γ] [DecidableEq γ]
variable {r : ℕ}

/-- Inclusion of the core ground set. -/
def corePointEmbedding : α ↪ CoreGround α r γ :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- The common pivot point. -/
def corePivot : CoreGround α r γ :=
  Sum.inr (Sum.inl Unit.unit)

/-- The private point indexed by `j`. -/
def privatePoint (j : Fin r) : CoreGround α r γ :=
  Sum.inr (Sum.inr (Sum.inl j))

/-- Restrict a core to the levels used by the construction. -/
def coreWindow (C : Family α) (h : ℕ) : Family α :=
  C.filter fun c => 2 ≤ c.card ∧ c.card ≤ h - 1

omit [Fintype α] [DecidableEq α] in
@[simp] theorem mem_coreWindow {C : Family α} {h : ℕ} {c : Finset α} :
    c ∈ coreWindow C h ↔ c ∈ C ∧ 2 ≤ c.card ∧ c.card ≤ h - 1 := by
  simp [coreWindow]

omit [Fintype α] [DecidableEq α] in
theorem isSperner_coreWindow {C : Family α} {h : ℕ}
    (hC : IsSperner C) : IsSperner (coreWindow C h) := by
  exact hC.subset (by intro c hc; exact (mem_coreWindow.mp hc).1)

omit [Fintype α] in
theorem level_coreWindow_eq {C : Family α} {h i : ℕ}
    (hi2 : 2 ≤ i) (hih : i ≤ h - 1) :
    level (coreWindow C h) i = level C i := by
  ext c
  simp only [mem_level, mem_coreWindow]
  constructor
  · rintro ⟨⟨hc, -, -⟩, hcard⟩
    exact ⟨hc, hcard⟩
  · rintro ⟨hc, hcard⟩
    exact ⟨⟨hc, hcard ▸ hi2, hcard ▸ hih⟩, hcard⟩

/-- Attach the pivot to a core member. -/
def pivotedSet (c : Finset α) : Finset (CoreGround α r γ) :=
  insert corePivot (c.map corePointEmbedding)

/-- The pair formed by the pivot and one private point. -/
def privatePair (j : Fin r) : Finset (CoreGround α r γ) :=
  {corePivot, privatePoint j}

omit [Fintype α] [Fintype γ] in
@[simp] theorem mem_pivotedSet_core {c : Finset α} {x : α} :
    corePointEmbedding x ∈ (pivotedSet c : Finset (CoreGround α r γ)) ↔ x ∈ c := by
  simp [pivotedSet, corePointEmbedding, corePivot]

omit [Fintype α] [Fintype γ] in
@[simp] theorem pivot_mem_pivotedSet {c : Finset α} :
    (corePivot : CoreGround α r γ) ∈ pivotedSet c := by
  simp [pivotedSet]

omit [Fintype α] [Fintype γ] in
@[simp] theorem private_not_mem_pivotedSet {c : Finset α} {j : Fin r} :
    privatePoint j ∉ (pivotedSet c : Finset (CoreGround α r γ)) := by
  simp [pivotedSet, privatePoint, corePivot, corePointEmbedding]

omit [Fintype α] [Fintype γ] in
@[simp] theorem card_pivotedSet (c : Finset α) :
    (pivotedSet c : Finset (CoreGround α r γ)).card = c.card + 1 := by
  rw [pivotedSet, card_insert_of_notMem]
  · simp
  · simp [corePivot, corePointEmbedding]

omit [Fintype α] [Fintype γ] in
@[simp] theorem pivot_mem_privatePair (j : Fin r) :
    (corePivot : CoreGround α r γ) ∈ privatePair j := by
  simp [privatePair]

omit [Fintype α] [Fintype γ] in
@[simp] theorem private_mem_privatePair (j : Fin r) :
    privatePoint j ∈ (privatePair j : Finset (CoreGround α r γ)) := by
  simp [privatePair]

omit [Fintype α] [Fintype γ] in
@[simp] theorem card_privatePair (j : Fin r) :
    (privatePair j : Finset (CoreGround α r γ)).card = 2 := by
  simp [privatePair, privatePoint, corePivot]

omit [Fintype α] [Fintype γ] in
theorem pivotedSet_injective :
    Function.Injective (pivotedSet (α := α) (r := r) (γ := γ)) := by
  intro c d hcd
  ext x
  have h := congrArg
    (fun s : Finset (CoreGround α r γ) => corePointEmbedding x ∈ s) hcd
  simpa using h

omit [Fintype α] [Fintype γ] in
theorem privatePair_injective :
    Function.Injective (privatePair (α := α) (r := r) (γ := γ)) := by
  intro i j hij
  have hmem : privatePoint i ∈ (privatePair j : Finset (CoreGround α r γ)) := by
    rw [← hij]
    exact private_mem_privatePair i
  simp [privatePair, privatePoint, corePivot] at hmem
  exact hmem

def pivotedSetEmbedding :
    Finset α ↪ Finset (CoreGround α r γ) :=
  ⟨pivotedSet, pivotedSet_injective⟩

def privatePairEmbedding :
    Fin r ↪ Finset (CoreGround α r γ) :=
  ⟨privatePair, privatePair_injective⟩

/-- Pivoted members from the usable part of the core. -/
def pivotedFamily (C : Family α) (h : ℕ) : Family (CoreGround α r γ) :=
  (coreWindow C h).map pivotedSetEmbedding

/-- The `r` private pairs on level two. -/
def privatePairFamily : Family (CoreGround α r γ) :=
  (Finset.univ : Finset (Fin r)).map privatePairEmbedding

/-- The lower half before adjoining complements. -/
def lowerCoreFamily (C : Family α) (h : ℕ) : Family (CoreGround α r γ) :=
  privatePairFamily ∪ pivotedFamily C h

omit [Fintype α] [Fintype γ] in
@[simp] theorem mem_pivotedFamily {C : Family α} {h : ℕ}
    {u : Finset (CoreGround α r γ)} :
    u ∈ pivotedFamily C h ↔ ∃ c ∈ coreWindow C h, pivotedSet c = u := by
  simp [pivotedFamily, pivotedSetEmbedding]

omit [Fintype α] [Fintype γ] in
@[simp] theorem mem_privatePairFamily {u : Finset (CoreGround α r γ)} :
    u ∈ (privatePairFamily : Family (CoreGround α r γ)) ↔
      ∃ j : Fin r, privatePair j = u := by
  simp [privatePairFamily, privatePairEmbedding]

omit [Fintype α] [Fintype γ] in
@[simp] theorem card_privatePairFamily :
    (privatePairFamily : Family (CoreGround α r γ)).card = r := by
  simp [privatePairFamily]

omit [Fintype α] [Fintype γ] in
theorem privatePairFamily_sized :
    ((privatePairFamily (α := α) (r := r) (γ := γ) :
      Family (CoreGround α r γ)) : Set (Finset (CoreGround α r γ))).Sized 2 := by
  intro u hu
  obtain ⟨j, rfl⟩ := mem_privatePairFamily.mp hu
  exact card_privatePair j

omit [Fintype α] [Fintype γ] in
theorem pivotedSet_subset_iff {c d : Finset α} :
    (pivotedSet c : Finset (CoreGround α r γ)) ⊆ pivotedSet d ↔ c ⊆ d := by
  constructor
  · intro h x hx
    exact mem_pivotedSet_core.mp (h (mem_pivotedSet_core.mpr hx))
  · intro h x hx
    rcases mem_insert.mp hx with hx | hx
    · exact hx ▸ pivot_mem_pivotedSet
    · obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      exact mem_pivotedSet_core.mpr (h hy)

omit [Fintype α] [Fintype γ] in
theorem isSperner_pivotedFamily {C : Family α} {h : ℕ}
    (hC : IsSperner C) :
    IsSperner (pivotedFamily (r := r) (γ := γ) C h) := by
  intro u hu v hv huv hsub
  obtain ⟨c, hc, rfl⟩ := mem_pivotedFamily.mp hu
  obtain ⟨d, hd, rfl⟩ := mem_pivotedFamily.mp hv
  have hcd : c ⊆ d := pivotedSet_subset_iff.mp hsub
  have heq : c = d := (isSperner_coreWindow hC).eq hc hd hcd
  exact huv (congrArg pivotedSet heq)

omit [Fintype α] [Fintype γ] in
theorem privatePair_not_subset_pivotedSet
    (j : Fin r) (c : Finset α) :
    ¬ (privatePair j : Finset (CoreGround α r γ)) ⊆ pivotedSet c := by
  intro hsub
  exact private_not_mem_pivotedSet (hsub (private_mem_privatePair j))

omit [Fintype α] [Fintype γ] in
theorem pivotedSet_not_subset_privatePair
    {C : Family α} {h : ℕ} {c : Finset α}
    (hc : c ∈ coreWindow C h) (j : Fin r) :
    ¬ (pivotedSet c : Finset (CoreGround α r γ)) ⊆ privatePair j := by
  intro hsub
  have hcard := card_le_card hsub
  rw [card_pivotedSet, card_privatePair] at hcard
  have hc2 := (mem_coreWindow.mp hc).2.1
  omega

omit [Fintype α] [Fintype γ] in
theorem isSperner_lowerCoreFamily {C : Family α} {h : ℕ}
    (hC : IsSperner C) :
    IsSperner (lowerCoreFamily (r := r) (γ := γ) C h) := by
  have hpairs : IsSperner
      (privatePairFamily (α := α) (r := r) (γ := γ) :
        Family (CoreGround α r γ)) :=
    privatePairFamily_sized.isAntichain
  have hpivoted : IsSperner (pivotedFamily (r := r) (γ := γ) C h) :=
    isSperner_pivotedFamily hC
  unfold IsSperner lowerCoreFamily
  rw [Finset.coe_union]
  apply isAntichain_union.mpr
  refine ⟨hpairs, hpivoted, ?_⟩
  intro u hu v hv huv
  obtain ⟨j, rfl⟩ := mem_privatePairFamily.mp hu
  obtain ⟨c, hc, rfl⟩ := mem_pivotedFamily.mp hv
  exact ⟨privatePair_not_subset_pivotedSet j c,
    pivotedSet_not_subset_privatePair hc j⟩

omit [Fintype α] [Fintype γ] in
theorem level_pivotedFamily_succ {C : Family α} {h i : ℕ} :
    level (pivotedFamily (r := r) (γ := γ) C h) (i + 1) =
      (level (coreWindow C h) i).map
        (pivotedSetEmbedding (r := r) (γ := γ)) := by
  ext u
  constructor
  · intro hu
    obtain ⟨huF, hucard⟩ := mem_level.mp hu
    obtain ⟨c, hc, rfl⟩ := mem_pivotedFamily.mp huF
    apply mem_map.mpr
    refine ⟨c, mem_level.mpr ⟨hc, ?_⟩, rfl⟩
    rw [card_pivotedSet] at hucard
    omega
  · intro hu
    obtain ⟨c, hc, rfl⟩ := mem_map.mp hu
    apply mem_level.mpr
    refine ⟨mem_pivotedFamily.mpr ⟨c, (mem_level.mp hc).1, rfl⟩, ?_⟩
    change (pivotedSet c : Finset (CoreGround α r γ)).card = i + 1
    rw [card_pivotedSet, (mem_level.mp hc).2]

omit [Fintype α] [Fintype γ] in
theorem card_level_pivotedFamily_succ {C : Family α} {h i : ℕ} :
    (level (pivotedFamily (r := r) (γ := γ) C h) (i + 1)).card =
      (level (coreWindow C h) i).card := by
  rw [level_pivotedFamily_succ, card_map]

omit [Fintype α] [Fintype γ] in
theorem level_privatePairFamily_two :
    level (privatePairFamily (α := α) (r := r) (γ := γ) :
      Family (CoreGround α r γ)) 2 =
      privatePairFamily (α := α) (r := r) (γ := γ) := by
  ext u
  constructor
  · exact fun hu => (mem_level.mp hu).1
  · intro hu
    exact mem_level.mpr ⟨hu, privatePairFamily_sized hu⟩

omit [Fintype α] [Fintype γ] in
theorem hasMultiplicities_lowerCoreFamily
    {C : Family α} {h : ℕ} (hh : 2 ≤ h)
    (hlevels : HasMultiplicities C r 2 (h - 1)) :
    HasMultiplicities (lowerCoreFamily (r := r) (γ := γ) C h) r 2 h := by
  intro i hi2 hih
  unfold HasMultiplicityAt
  by_cases hi : i = 2
  · subst i
    have hsubset :
        (privatePairFamily (α := α) (r := r) (γ := γ) :
          Family (CoreGround α r γ)) ⊆
        lowerCoreFamily (r := r) (γ := γ) C h := subset_union_left
    have hcard := card_le_card (level_mono hsubset 2)
    rw [level_privatePairFamily_two, card_privatePairFamily] at hcard
    exact hcard
  · have hi3 : 3 ≤ i := by omega
    have hsubset : pivotedFamily (r := r) (γ := γ) C h ⊆
        lowerCoreFamily (r := r) (γ := γ) C h := subset_union_right
    have hcard := card_le_card (level_mono hsubset i)
    have hpred2 : 2 ≤ i - 1 := by omega
    have hpredh : i - 1 ≤ h - 1 := by omega
    have hcore := hlevels (i - 1) hpred2 hpredh
    unfold HasMultiplicityAt at hcore
    rw [show i = (i - 1) + 1 by omega,
      card_level_pivotedFamily_succ,
      level_coreWindow_eq hpred2 hpredh] at hcard
    simpa [show i - 1 + 1 = i by omega] using hcore.trans hcard

/-! ### Complements and the full family -/

theorem level_compls {δ : Type*} [Fintype δ] [DecidableEq δ]
    (F : Family δ) {i : ℕ} (hi : i ≤ Fintype.card δ) :
    level (Finset.compls F) i =
      Finset.compls (level F (Fintype.card δ - i)) := by
  ext s
  simp only [mem_level, Finset.mem_compls]
  constructor
  · rintro ⟨hsF, hcard⟩
    refine ⟨hsF, ?_⟩
    rw [Finset.card_compl, hcard]
  · rintro ⟨hsF, hcard⟩
    refine ⟨hsF, ?_⟩
    rw [Finset.card_compl] at hcard
    have hsle : s.card ≤ Fintype.card δ := by
      simpa using card_le_card (subset_univ s)
    omega

theorem card_level_compls {δ : Type*} [Fintype δ] [DecidableEq δ]
    (F : Family δ) {i : ℕ} (hi : i ≤ Fintype.card δ) :
    (level (Finset.compls F) i).card =
      (level F (Fintype.card δ - i)).card := by
  rw [level_compls F hi, Finset.card_compls]

/-- Add the complemented upper half to the lower construction. -/
def coreToFullFamily (C : Family α) (h : ℕ) :
    Family (CoreGround α r γ) :=
  lowerCoreFamily C h ∪ Finset.compls (lowerCoreFamily C h)

omit [Fintype α] [Fintype γ] in
theorem pivot_mem_lowerCoreFamily {C : Family α} {h : ℕ}
    {u : Finset (CoreGround α r γ)}
    (hu : u ∈ lowerCoreFamily (r := r) (γ := γ) C h) :
    corePivot ∈ u := by
  rcases mem_union.mp hu with hu | hu
  · obtain ⟨j, rfl⟩ := mem_privatePairFamily.mp hu
    exact pivot_mem_privatePair j
  · obtain ⟨c, hc, rfl⟩ := mem_pivotedFamily.mp hu
    exact pivot_mem_pivotedSet

omit [Fintype α] [Fintype γ] in
theorem card_lowerCoreFamily_le {C : Family α} {h : ℕ} (hh : 2 ≤ h)
    {u : Finset (CoreGround α r γ)}
    (hu : u ∈ lowerCoreFamily (r := r) (γ := γ) C h) :
    u.card ≤ h := by
  rcases mem_union.mp hu with hu | hu
  · obtain ⟨j, rfl⟩ := mem_privatePairFamily.mp hu
    rw [card_privatePair]
    exact hh
  · obtain ⟨c, hc, rfl⟩ := mem_pivotedFamily.mp hu
    rw [card_pivotedSet]
    have hcupper := (mem_coreWindow.mp hc).2.2
    omega

theorem isSperner_compls {δ : Type*} [Fintype δ] [DecidableEq δ]
    {F : Family δ} (hF : IsSperner F) :
    IsSperner (Finset.compls F) := by
  unfold IsSperner at hF ⊢
  simpa only [Finset.coe_compls] using hF.image_compl

/--
The lower family and its complement are mutually incomparable because all
lower members contain the pivot and have size at most half the ground set.
-/
theorem isSperner_coreToFullFamily
    {C : Family α} {h : ℕ} (hh : 2 ≤ h)
    (hhalf : 2 * h ≤ Fintype.card (CoreGround α r γ))
    (hC : IsSperner C) :
    IsSperner (coreToFullFamily (r := r) (γ := γ) C h) := by
  have hL : IsSperner
      (lowerCoreFamily (r := r) (γ := γ) C h) :=
    isSperner_lowerCoreFamily hC
  have hLc : IsSperner
      (Finset.compls (lowerCoreFamily (r := r) (γ := γ) C h)) :=
    isSperner_compls hL
  unfold IsSperner coreToFullFamily
  rw [Finset.coe_union]
  apply isAntichain_union.mpr
  refine ⟨hL, hLc, ?_⟩
  intro a ha b hb hab
  have hbL : bᶜ ∈ lowerCoreFamily (r := r) (γ := γ) C h :=
    Finset.mem_compls.mp hb
  constructor
  · intro habsub
    have hpiva : corePivot ∈ a := pivot_mem_lowerCoreFamily ha
    have hpivb : corePivot ∈ b := habsub hpiva
    have hpivbc : corePivot ∈ bᶜ := pivot_mem_lowerCoreFamily hbL
    have hpiv_not : corePivot ∉ b := by simpa using hpivbc
    exact hpiv_not hpivb
  · intro hbasub
    have hunion : a ∪ bᶜ = (Finset.univ : Finset (CoreGround α r γ)) := by
      ext x
      simp only [mem_union, mem_compl, mem_univ, iff_true]
      by_cases hxb : x ∈ b
      · exact Or.inl (hbasub hxb)
      · exact Or.inr hxb
    have hinter : 1 ≤ (a ∩ bᶜ).card := by
      apply card_pos.mpr
      exact ⟨corePivot,
        mem_inter.mpr ⟨pivot_mem_lowerCoreFamily ha,
          pivot_mem_lowerCoreFamily hbL⟩⟩
    have hacard : a.card ≤ h := card_lowerCoreFamily_le hh ha
    have hbcard : bᶜ.card ≤ h := card_lowerCoreFamily_le hh hbL
    have hcount := card_union_add_card_inter a bᶜ
    rw [hunion, card_univ] at hcount
    omega

theorem hasMultiplicities_coreToFullFamily
    {C : Family α}
    (hn : 4 ≤ Fintype.card (CoreGround α r γ))
    (hlevels : HasMultiplicities C r 2
      (Fintype.card (CoreGround α r γ) / 2 - 1)) :
    HasMultiplicities
      (coreToFullFamily (r := r) (γ := γ) C
        (Fintype.card (CoreGround α r γ) / 2))
      r 2 (Fintype.card (CoreGround α r γ) - 2) := by
  let n := Fintype.card (CoreGround α r γ)
  let h := n / 2
  let L : Family (CoreGround α r γ) :=
    lowerCoreFamily (r := r) (γ := γ) C h
  have hh : 2 ≤ h := by
    dsimp [h, n]
    omega
  have hL : HasMultiplicities L r 2 h := by
    exact hasMultiplicities_lowerCoreFamily hh hlevels
  intro i hi2 hin
  unfold HasMultiplicityAt
  by_cases hilow : i ≤ h
  · have hsubset : L ⊆ coreToFullFamily (r := r) (γ := γ) C h :=
      subset_union_left
    exact (hL i hi2 hilow).trans (card_le_card (level_mono hsubset i))
  · have hij2 : 2 ≤ n - i := by
      dsimp [n] at hin ⊢
      omega
    have hijh : n - i ≤ h := by
      dsimp [h]
      omega
    have hi_le_n : i ≤ n := by omega
    have hcomp_subset : Finset.compls L ⊆
        coreToFullFamily (r := r) (γ := γ) C h := subset_union_right
    have hcomp_card := card_le_card (level_mono hcomp_subset i)
    have hlevel_compl := card_level_compls L hi_le_n
    have hLj := hL (n - i) hij2 hijh
    rw [hlevel_compl] at hcomp_card
    exact hLj.trans hcomp_card

/-- The manuscript's core-to-full lemma, with antichain and profile conclusions. -/
theorem coreToFull
    {C : Family α}
    (hn : 4 ≤ Fintype.card (CoreGround α r γ))
    (hC : IsSperner C)
    (hlevels : HasMultiplicities C r 2
      (Fintype.card (CoreGround α r γ) / 2 - 1)) :
    IsSperner
        (coreToFullFamily (r := r) (γ := γ) C
          (Fintype.card (CoreGround α r γ) / 2)) ∧
      HasMultiplicities
        (coreToFullFamily (r := r) (γ := γ) C
          (Fintype.card (CoreGround α r γ) / 2))
        r 2 (Fintype.card (CoreGround α r γ) - 2) := by
  have hhalf :
      2 * (Fintype.card (CoreGround α r γ) / 2) ≤
        Fintype.card (CoreGround α r γ) :=
    Nat.mul_div_le _ 2
  have hh : 2 ≤ Fintype.card (CoreGround α r γ) / 2 := by omega
  exact ⟨isSperner_coreToFullFamily hh hhalf hC,
    hasMultiplicities_coreToFullFamily hn hlevels⟩

/-- Transport the named construction to the conventional ground set `Fin n`. -/
noncomputable def coreToFullFinFamily (C : Family α) :
    Family (Fin (Fintype.card (CoreGround α r γ))) :=
  mapFamily (Fintype.equivFin (CoreGround α r γ)).toEmbedding <|
    coreToFullFamily (r := r) (γ := γ) C
      (Fintype.card (CoreGround α r γ) / 2)

/-- `coreToFull`, stated on the numerical ground set used in the manuscripts. -/
theorem coreToFull_fin
    {C : Family α}
    (hn : 4 ≤ Fintype.card (CoreGround α r γ))
    (hC : IsSperner C)
    (hlevels : HasMultiplicities C r 2
      (Fintype.card (CoreGround α r γ) / 2 - 1)) :
    IsSperner (coreToFullFinFamily (r := r) (γ := γ) C) ∧
      HasMultiplicities (coreToFullFinFamily (r := r) (γ := γ) C)
        r 2 (Fintype.card (CoreGround α r γ) - 2) := by
  obtain ⟨hanti, hprofile⟩ := coreToFull hn hC hlevels
  constructor
  · exact isSperner_mapFamily hanti
  · intro i hi hin
    unfold HasMultiplicityAt
    rw [coreToFullFinFamily, card_level_mapFamily]
    exact hprofile i hi hin

end Erdos776.Antichain
