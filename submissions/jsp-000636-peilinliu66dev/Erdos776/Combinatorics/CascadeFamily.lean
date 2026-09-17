import Erdos776.Combinatorics.Cascade
import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Combinatorics.SetFamily.Shadow
import Mathlib.Data.Finset.Powerset

/-!
# Set families represented by numerical cascades

For canonical digits `aₖ > aₖ₋₁ > ...`, `cascadeFamily k digits` is the
recursive colex family consisting of all `k`-subsets below `aₖ`, followed by
sets containing `aₖ` whose remainders belong to the tail family.
-/

namespace Erdos776.KruskalKatona

open Finset

/-- The concrete finite family encoded by a list of cascade digits. -/
def cascadeFamily : ℕ → List ℕ → Finset (Finset ℕ)
  | _, [] => ∅
  | 0, _ :: _ => {∅}
  | k + 1, a :: digits =>
      (range a).powersetCard (k + 1) ∪
        (cascadeFamily k digits).image (insert a)

@[simp] theorem cascadeFamily_nil (k : ℕ) : cascadeFamily k [] = ∅ := by
  cases k <;> rfl

@[simp] theorem cascadeFamily_zero_cons (a : ℕ) (digits : List ℕ) :
    cascadeFamily 0 (a :: digits) = {∅} := rfl

@[simp] theorem cascadeFamily_succ_cons (k a : ℕ) (digits : List ℕ) :
    cascadeFamily (k + 1) (a :: digits) =
      (range a).powersetCard (k + 1) ∪
      (cascadeFamily k digits).image (insert a) := rfl

/--
The diagonal cascade of length `len` consists of the first `len` colex
`a`-sets: the sets obtained from `range (a+1)` by deleting one of its final
`len` points.
-/
theorem erase_range_mem_cascadeFamily_diagonalDigits
    {a len j : ℕ} (hlen : len ≤ a)
    (hjlow : a + 1 - len ≤ j) (hjhigh : j ≤ a) :
    (range (a + 1)).erase j ∈
      cascadeFamily a (diagonalDigits a len) := by
  induction len generalizing a j with
  | zero => omega
  | succ len ih =>
      cases a with
      | zero => omega
      | succ a =>
          simp only [diagonalDigits_succ, cascadeFamily_succ_cons]
          by_cases hja : j = a + 1
          · subst j
            apply mem_union_left
            apply mem_powersetCard.mpr
            have heq : (range (a + 1 + 1)).erase (a + 1) = range (a + 1) := by
              ext x
              simp
              omega
            rw [heq]
            simp
          · apply mem_union_right
            apply mem_image.mpr
            refine ⟨(range (a + 1)).erase j, ?_, ?_⟩
            · apply ih (by omega) (by omega) (by omega)
            · ext x
              simp
              omega

/-- Every point used by the family is below some cascade digit. -/
theorem mem_cascadeFamily_lt_of_digits_lt
    {k A : ℕ} {digits : List ℕ} {s : Finset ℕ}
    (hdigits : ∀ d ∈ digits, d < A)
    (hs : s ∈ cascadeFamily k digits) : ∀ x ∈ s, x < A := by
  induction k generalizing digits s with
  | zero =>
      cases digits with
      | nil => simp at hs
      | cons =>
          simp at hs
          subst s
          simp
  | succ k ih =>
      cases digits with
      | nil => simp at hs
      | cons a digits =>
          simp only [cascadeFamily_succ_cons, mem_union, mem_powersetCard,
            mem_image] at hs
          intro x hx
          rcases hs with hs | ⟨t, ht, hst⟩
          · exact (Finset.mem_range.mp (hs.1 hx)).trans
              (hdigits a (List.mem_cons_self))
          · subst s
            rcases mem_insert.mp hx with hxa | hx
            · subst x
              exact hdigits a (List.mem_cons_self)
            · exact ih (fun d hd => hdigits d (List.mem_cons_of_mem a hd)) ht x hx

/-- Tail-family members do not contain the preceding canonical digit. -/
theorem IsCanonical.head_notMem_tail_family
    {k a : ℕ} {digits : List ℕ} (h : IsCanonical (k + 1) (a :: digits))
    {s : Finset ℕ} (hs : s ∈ cascadeFamily k digits) : a ∉ s := by
  intro ha
  exact (Nat.lt_irrefl a) <|
    mem_cascadeFamily_lt_of_digits_lt h.2.1 hs a ha

/-- Every member has the lower index prescribed by the cascade. -/
theorem sized_cascadeFamily {k : ℕ} {digits : List ℕ}
    (h : IsCanonical k digits) :
    (cascadeFamily k digits : Set (Finset ℕ)).Sized k := by
  induction k generalizing digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at h
  | succ k ih =>
      cases digits with
      | nil => simp
      | cons a digits =>
          intro s hs
          rw [cascadeFamily_succ_cons, mem_coe, mem_union] at hs
          rcases hs with hs | hs
          · exact (mem_powersetCard.mp hs).2
          · obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
            rw [card_insert_of_notMem (h.head_notMem_tail_family ht)]
            exact congrArg (· + 1) (ih h.2.2 ht)

/-- The full block of `k+1`-sets below `a` shadows to the full `k`-block. -/
theorem shadow_powersetCard_range {k a : ℕ} (hka : k + 1 ≤ a) :
    Finset.shadow ((range a).powersetCard (k + 1)) =
      (range a).powersetCard k := by
  ext t
  simp only [mem_shadow_iff, mem_powersetCard]
  constructor
  · rintro ⟨s, hs, x, hx, rfl⟩
    refine ⟨fun y hy => hs.1 (mem_of_mem_erase hy), ?_⟩
    rw [card_erase_of_mem hx, hs.2]
    omega
  · rintro ⟨htrange, htcard⟩
    have hcard : t.card < (range a).card := by
      simp only [card_range, htcard]
      omega
    obtain ⟨x, hx⟩ := sdiff_nonempty_of_card_lt_card hcard
    have hxrange : x ∈ range a := (mem_sdiff.mp hx).1
    have hxnot : x ∉ t := (mem_sdiff.mp hx).2
    refine ⟨insert x t, ?_, x, mem_insert_self x t, erase_insert hxnot⟩
    refine ⟨?_, ?_⟩
    · exact insert_subset hxrange htrange
    · rw [card_insert_of_notMem hxnot, htcard]

/--
Shadowing one recursive colex block: removing the new largest point either
lands in the full lower block, or removes a point from the tail family.
-/
theorem shadow_fullBlock_union_insert
    {k a : ℕ} {T : Finset (Finset ℕ)}
    (hka : k + 1 ≤ a)
    (hsize : (T : Set (Finset ℕ)).Sized k)
    (hbound : ∀ s ∈ T, s ⊆ range a) :
    Finset.shadow
        ((range a).powersetCard (k + 1) ∪ T.image (insert a)) =
      (range a).powersetCard k ∪ (Finset.shadow T).image (insert a) := by
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs, x, hx, hxt⟩ := mem_shadow_iff.mp ht
    rcases mem_union.mp hs with hs | hs
    · apply mem_union_left
      rw [← shadow_powersetCard_range hka]
      exact hxt ▸ erase_mem_shadow hs hx
    · obtain ⟨u, hu, hsu⟩ := mem_image.mp hs
      subst s
      have hau : a ∉ u := by
        intro ha
        exact (Finset.mem_range.mp (hbound u hu ha)).false
      rcases mem_insert.mp hx with hxa | hxu
      · subst x
        rw [erase_insert hau] at hxt
        subst t
        apply mem_union_left
        exact mem_powersetCard.mpr ⟨hbound u hu, hsize hu⟩
      · have hxa : a ≠ x := fun h => hau (h ▸ hxu)
        rw [erase_insert_of_ne hxa] at hxt
        subst t
        apply mem_union_right
        exact mem_image.mpr ⟨u.erase x, erase_mem_shadow hu hxu, rfl⟩
  · intro ht
    rcases mem_union.mp ht with ht | ht
    · have ht' : t ∈ Finset.shadow ((range a).powersetCard (k + 1)) := by
        rwa [shadow_powersetCard_range hka]
      exact shadow_mono subset_union_left ht'
    · obtain ⟨v, hv, rfl⟩ := mem_image.mp ht
      obtain ⟨u, hu, x, hxu, hxv⟩ := mem_shadow_iff.mp hv
      have hau : a ∉ u := by
        intro ha
        exact (Finset.mem_range.mp (hbound u hu ha)).false
      have hax : a ≠ x := fun h => hau (h ▸ hxu)
      apply mem_shadow_iff.mpr
      refine ⟨insert a u, mem_union.mpr (Or.inr (mem_image.mpr ⟨u, hu, rfl⟩)),
        x, mem_insert_of_mem hxu, ?_⟩
      rw [erase_insert_of_ne hax, hxv]

/-- A canonical cascade shadows term by term. -/
theorem shadow_cascadeFamily {k : ℕ} {digits : List ℕ}
    (h : IsCanonical k digits) :
    Finset.shadow (cascadeFamily k digits) =
      cascadeFamily (k - 1) digits := by
  induction k generalizing digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at h
  | succ k ih =>
      cases digits with
      | nil => simp
      | cons a digits =>
          have htail : IsCanonical k digits := h.2.2
          have hbound : ∀ s ∈ cascadeFamily k digits, s ⊆ range a := by
            intro s hs x hx
            exact mem_range.mpr <| mem_cascadeFamily_lt_of_digits_lt h.2.1 hs x hx
          rw [cascadeFamily_succ_cons,
            shadow_fullBlock_union_insert h.1 (sized_cascadeFamily htail) hbound]
          cases k with
          | zero =>
              cases digits with
              | nil => simp
              | cons => simp at htail
          | succ k =>
              rw [ih htail]
              rfl

/-- `cascadeFamily` has exactly the cardinality represented by its digits. -/
theorem card_cascadeFamily {k : ℕ} {digits : List ℕ}
    (h : IsCanonical k digits) :
    (cascadeFamily k digits).card = cascadeValue k digits := by
  induction k generalizing digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at h
  | succ k ih =>
      cases digits with
      | nil => simp
      | cons a digits =>
          have htail : IsCanonical k digits := h.2.2
          have hnot : ∀ s ∈ cascadeFamily k digits, a ∉ s :=
            fun s hs => h.head_notMem_tail_family hs
          have hinj : Set.InjOn (insert a) (cascadeFamily k digits : Set (Finset ℕ)) := by
            intro s hs t ht hst
            have hs' := hnot s hs
            have ht' := hnot t ht
            have herase := congrArg (erase · a) hst
            simpa [hs', ht'] using herase
          have hdisjoint :
              Disjoint ((range a).powersetCard (k + 1))
                ((cascadeFamily k digits).image (insert a)) := by
            rw [Finset.disjoint_left]
            intro s hs hsi
            obtain ⟨t, ht, rfl⟩ := mem_image.mp hsi
            have ha_range := (mem_powersetCard.mp hs).1 (mem_insert_self a t)
            simp at ha_range
          rw [cascadeFamily_succ_cons, card_union_of_disjoint hdisjoint,
            card_powersetCard, card_range, card_image_of_injOn hinj, ih htail]
          rfl

/-- The lowered family has the cardinality obtained by lowering every index. -/
theorem card_lowered_cascadeFamily {k : ℕ} {digits : List ℕ}
    (h : IsCanonical k digits) :
    (cascadeFamily (k - 1) digits).card = cascadeValue (k - 1) digits := by
  induction k generalizing digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at h
  | succ k ih =>
      cases digits with
      | nil => simp
      | cons a digits =>
          have htail : IsCanonical k digits := h.2.2
          cases k with
          | zero =>
              cases digits with
              | nil => simp [cascadeValue]
              | cons => simp at htail
          | succ k =>
              have hnot : ∀ s ∈ cascadeFamily k digits, a ∉ s := by
                intro s hs ha
                exact (Nat.lt_irrefl a) <|
                  mem_cascadeFamily_lt_of_digits_lt h.2.1 hs a ha
              have hinj :
                  Set.InjOn (insert a) (cascadeFamily k digits : Set (Finset ℕ)) := by
                intro s hs t ht hst
                have herase := congrArg (erase · a) hst
                simpa [hnot s hs, hnot t ht] using herase
              have hdisjoint :
                  Disjoint ((range a).powersetCard (k + 1))
                    ((cascadeFamily k digits).image (insert a)) := by
                rw [Finset.disjoint_left]
                intro s hs hsi
                obtain ⟨t, ht, rfl⟩ := mem_image.mp hsi
                have ha_range := (mem_powersetCard.mp hs).1 (mem_insert_self a t)
                simp at ha_range
              have hi :
                  (cascadeFamily k digits).card = cascadeValue k digits := by
                simpa using ih htail
              rw [show k + 1 + 1 - 1 = k + 1 by omega,
                cascadeFamily_succ_cons, card_union_of_disjoint hdisjoint,
                card_powersetCard, card_range, card_image_of_injOn hinj, hi]
              rfl

/-- The cardinal form of termwise cascade shadowing. -/
theorem card_shadow_cascadeFamily {k : ℕ} {digits : List ℕ}
    (h : IsCanonical k digits) :
    (Finset.shadow (cascadeFamily k digits)).card =
      cascadeShadowValue k digits := by
  rw [shadow_cascadeFamily h, card_lowered_cascadeFamily h]
  rfl

/-- Adding a full block below `a` to a bounded initial segment preserves colex initiality. -/
theorem isInitSeg_fullBlock_union_insert
    {k a : ℕ} {T : Finset (Finset ℕ)}
    (hT : Finset.Colex.IsInitSeg T k)
    (hbound : ∀ s ∈ T, s ⊆ range a) :
    Finset.Colex.IsInitSeg
      ((range a).powersetCard (k + 1) ∪ T.image (insert a)) (k + 1) := by
  constructor
  · intro s hs
    rcases mem_union.mp hs with hs | hs
    · exact (mem_powersetCard.mp hs).2
    · obtain ⟨u, hu, rfl⟩ := mem_image.mp hs
      have hau : a ∉ u := by
        intro ha
        exact (mem_range.mp (hbound u hu ha)).false
      rw [card_insert_of_notMem hau, hT.1 hu]
  · intro s t hs ht
    rcases mem_union.mp hs with hs | hs
    · apply mem_union_left
      exact mem_powersetCard.mpr ⟨fun x hx => mem_range.mpr <|
        Finset.Colex.forall_lt_mono ht.1.le
          (fun y hy => mem_range.mp ((mem_powersetCard.mp hs).1 hy)) x hx, ht.2⟩
    · obtain ⟨u, hu, rfl⟩ := mem_image.mp hs
      have hau : a ∉ u := by
        intro ha
        exact (mem_range.mp (hbound u hu ha)).false
      by_cases hat : a ∈ t
      · apply mem_union_right
        refine mem_image.mpr ⟨t.erase a, ?_, insert_erase hat⟩
        apply hT.2 hu
        refine ⟨?_, ?_⟩
        · have hremove :=
            (Finset.Colex.toColex_sdiff_lt_toColex_sdiff
              (s := t) (t := insert a u) (u := {a})
              (by simpa using hat) (by simp)).2 ht.1
          simpa [sdiff_singleton_eq_erase, hau] using hremove
        · rw [card_erase_of_mem hat, ht.2]
          omega
      · apply mem_union_left
        refine mem_powersetCard.mpr ⟨?_, ht.2⟩
        intro x hx
        have hle : x ≤ a :=
          Finset.Colex.forall_le_mono ht.1.le (fun y hy => by
            rcases mem_insert.mp hy with rfl | hy
            · exact le_rfl
            · exact (mem_range.mp (hbound u hu hy)).le) x hx
        have hne : x ≠ a := fun hxa => hat (hxa ▸ hx)
        exact mem_range.mpr (lt_of_le_of_ne hle hne)

/-- The recursively represented canonical family is a colex initial segment. -/
theorem isInitSeg_cascadeFamily {k : ℕ} {digits : List ℕ}
    (h : IsCanonical k digits) :
    Finset.Colex.IsInitSeg (cascadeFamily k digits) k := by
  induction k generalizing digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at h
  | succ k ih =>
      cases digits with
      | nil => simp
      | cons a digits =>
          have htail : IsCanonical k digits := h.2.2
          have hbound : ∀ s ∈ cascadeFamily k digits, s ⊆ range a := by
            intro s hs x hx
            exact mem_range.mpr <| mem_cascadeFamily_lt_of_digits_lt h.2.1 hs x hx
          rw [cascadeFamily_succ_cons]
          exact isInitSeg_fullBlock_union_insert (ih htail) hbound

end Erdos776.KruskalKatona
