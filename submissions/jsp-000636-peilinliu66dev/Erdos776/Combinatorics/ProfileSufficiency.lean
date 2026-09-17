import Erdos776.Combinatorics.Antichain
import Erdos776.Combinatorics.NormalShadow
import Mathlib.Order.Interval.Finset.Nat

/-!
# Sufficiency in the prescribed-profile criterion

Given a top-down cascade recurrence which fits inside every level of `Fin n`,
this file constructs the corresponding colex antichain.  Together with
`ProfileNecessity.lean`, this supplies both mathematical directions of the
squashed-antichain profile theorem used throughout the research package.
-/

namespace Erdos776.KruskalKatona

open Finset
open Erdos776.Antichain

/-- The colex initial segment represented by the canonical cascade of `m`. -/
noncomputable def canonicalFamily (n k m : ℕ) : Family (Fin n) :=
  finifyFamily n (cascadeFamily k (canonicalDigits k m))

theorem canonicalFamily_sized
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    (canonicalFamily n k m : Set (Finset (Fin n))).Sized k := by
  exact sized_finifyFamily
    (bounded_cascadeFamily_canonicalDigits hk hm)
    (sized_cascadeFamily (isCanonical_canonicalDigits hk))

@[simp] theorem card_canonicalFamily
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    (canonicalFamily n k m).card = m := by
  rw [canonicalFamily,
    card_finifyFamily (bounded_cascadeFamily_canonicalDigits hk hm),
    card_cascadeFamily (isCanonical_canonicalDigits hk),
    cascadeValue_canonicalDigits hk]

theorem canonicalFamily_isInitSeg
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    Finset.Colex.IsInitSeg (canonicalFamily n k m) k := by
  exact isInitSeg_finifyFamily
    (bounded_cascadeFamily_canonicalDigits hk hm)
    (isInitSeg_cascadeFamily (isCanonical_canonicalDigits hk))

@[simp] theorem card_shadow_canonicalFamily
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    (Finset.shadow (canonicalFamily n k m)).card = canonicalShadow k m := by
  rw [canonicalFamily,
    card_shadow_finifyFamily (bounded_cascadeFamily_canonicalDigits hk hm),
    card_shadow_cascadeFamily (isCanonical_canonicalDigits hk)]
  rfl

/-- Initial colex segments are ordered by their cardinalities. -/
theorem initSeg_subset_of_card_le
    {n k : ℕ} {A B : Family (Fin n)}
    (hA : Finset.Colex.IsInitSeg A k)
    (hB : Finset.Colex.IsInitSeg B k)
    (hcard : A.card ≤ B.card) : A ⊆ B := by
  rcases hA.total hB with hAB | hBA
  · exact hAB
  · have heq : B = A := eq_of_subset_of_card_le hBA hcard
    exact heq ▸ Subset.rfl

/--
`m` is the top-down cascade recurrence for profile `f` on levels `lo..hi`.
The zero at `hi+1` makes the top-level equation uniform with all other levels.
-/
def IsProfileRecurrence
    (n lo hi : ℕ) (f m : ℕ → ℕ) : Prop :=
  m (hi + 1) = 0 ∧
    (∀ i, lo ≤ i → i ≤ hi →
      m i = f i + canonicalShadow (i + 1) (m (i + 1))) ∧
    ∀ i, lo ≤ i → i ≤ hi + 1 → m i ≤ n.choose i

/-- The members selected at level `i` after excluding the shadow from above. -/
noncomputable def selectedLayer (n : ℕ) (m : ℕ → ℕ) (i : ℕ) :
    Family (Fin n) :=
  canonicalFamily n i (m i) \
    Finset.shadow (canonicalFamily n (i + 1) (m (i + 1)))

/-- One recurrence step says that the shadow from above lies in the next segment. -/
theorem shadow_canonicalFamily_subset
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m)
    {i : ℕ} (hloi : lo ≤ i) (hihi : i ≤ hi) :
    Finset.shadow (canonicalFamily n (i + 1) (m (i + 1))) ⊆
      canonicalFamily n i (m i) := by
  have hi1 : 1 ≤ i := hlo.trans hloi
  have hcap_i : m i ≤ n.choose i := hrec.2.2 i hloi (by omega)
  have hcap_next : m (i + 1) ≤ n.choose (i + 1) :=
    hrec.2.2 (i + 1) (by omega) (by omega)
  have hcurrent := canonicalFamily_isInitSeg hi1 hcap_i
  have hnext := canonicalFamily_isInitSeg (by omega : 1 ≤ i + 1) hcap_next
  have hshadow : Finset.Colex.IsInitSeg
      (Finset.shadow (canonicalFamily n (i + 1) (m (i + 1)))) i := by
    simpa using hnext.shadow
  apply initSeg_subset_of_card_le hshadow hcurrent
  rw [card_shadow_canonicalFamily (by omega) hcap_next,
    card_canonicalFamily hi1 hcap_i, hrec.2.1 i hloi hihi]
  omega

theorem selectedLayer_sized
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m)
    {i : ℕ} (hloi : lo ≤ i) (hihi : i ≤ hi) :
    (selectedLayer n m i : Set (Finset (Fin n))).Sized i := by
  intro s hs
  have hcap : m i ≤ n.choose i := hrec.2.2 i hloi (by omega)
  exact canonicalFamily_sized (hlo.trans hloi) hcap (mem_sdiff.mp hs).1

@[simp] theorem card_selectedLayer
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m)
    {i : ℕ} (hloi : lo ≤ i) (hihi : i ≤ hi) :
    (selectedLayer n m i).card = f i := by
  have hcap_i : m i ≤ n.choose i := hrec.2.2 i hloi (by omega)
  have hcap_next : m (i + 1) ≤ n.choose (i + 1) :=
    hrec.2.2 (i + 1) (by omega) (by omega)
  rw [selectedLayer, card_sdiff_of_subset
      (shadow_canonicalFamily_subset hlo hrec hloi hihi),
    card_canonicalFamily (hlo.trans hloi) hcap_i,
    card_shadow_canonicalFamily (by omega) hcap_next,
    hrec.2.1 i hloi hihi]
  omega

/-- The antichain assembled from all selected profile layers. -/
noncomputable def profileFamily
    (n lo hi : ℕ) (m : ℕ → ℕ) : Family (Fin n) :=
  (Finset.Icc lo hi).biUnion (selectedLayer n m)

@[simp] theorem mem_profileFamily
    {n lo hi : ℕ} {m : ℕ → ℕ} {s : Finset (Fin n)} :
    s ∈ profileFamily n lo hi m ↔
      ∃ i ∈ Finset.Icc lo hi, s ∈ selectedLayer n m i := by
  simp [profileFamily]

/--
If a set from a higher canonical segment contains a lower-sized set, the
lower set belongs to the corresponding lower canonical segment.
-/
theorem subset_mem_canonicalFamily
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m)
    {i j : ℕ} (hloi : lo ≤ i) (hij : i ≤ j) (hjhi : j ≤ hi + 1)
    {u v : Finset (Fin n)}
    (hucard : u.card = i) (hvcard : v.card = j)
    (huv : u ⊆ v) (hv : v ∈ canonicalFamily n j (m j)) :
    u ∈ canonicalFamily n i (m i) := by
  induction j, hij using Nat.le_induction generalizing v with
  | base =>
      have huv_eq : u = v := eq_of_subset_of_card_le huv (by omega)
      simpa [huv_eq] using hv
  | succ j hij ih =>
      obtain ⟨w, huw, hwv, hwcard⟩ :=
        exists_subsuperset_card_eq huv (by omega) (by omega : j ≤ v.card)
      have hwshadow : w ∈ Finset.shadow (canonicalFamily n (j + 1) (m (j + 1))) := by
        apply mem_shadow_iff_exists_mem_card_add_one.mpr
        exact ⟨v, hv, hwv, by omega⟩
      have hjlo : lo ≤ j := hloi.trans hij
      have hjhi' : j ≤ hi := by omega
      have hw : w ∈ canonicalFamily n j (m j) :=
        shadow_canonicalFamily_subset hlo hrec hjlo hjhi' hwshadow
      exact ih (by omega) hwcard huw hw

/-- The selected layers are pairwise incomparable. -/
theorem isSperner_profileFamily
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m) :
    IsSperner (profileFamily n lo hi m) := by
  intro a ha b hb hab hsub
  obtain ⟨i, hiIcc, hai⟩ := mem_profileFamily.mp ha
  obtain ⟨j, hjIcc, hbj⟩ := mem_profileFamily.mp hb
  have hiBounds : lo ≤ i ∧ i ≤ hi := Finset.mem_Icc.mp hiIcc
  have hjBounds : lo ≤ j ∧ j ≤ hi := Finset.mem_Icc.mp hjIcc
  have hacard : a.card = i :=
    selectedLayer_sized hlo hrec hiBounds.1 hiBounds.2 hai
  have hbcard : b.card = j :=
    selectedLayer_sized hlo hrec hjBounds.1 hjBounds.2 hbj
  have hij : i < j := by
    have hssub : a ⊂ b := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hab⟩
    exact hacard ▸ hbcard ▸ card_lt_card hssub
  obtain ⟨u, hau, hub, hucard⟩ :=
    exists_subsuperset_card_eq (n := i + 1) hsub
      (by omega) (by omega : i + 1 ≤ b.card)
  have hbM : b ∈ canonicalFamily n j (m j) := (mem_sdiff.mp hbj).1
  have huM : u ∈ canonicalFamily n (i + 1) (m (i + 1)) :=
    subset_mem_canonicalFamily (i := i + 1) (j := j)
      hlo hrec (by omega) (by omega) (by omega)
      hucard hbcard hub hbM
  have haShadow : a ∈ Finset.shadow (canonicalFamily n (i + 1) (m (i + 1))) := by
    apply mem_shadow_iff_exists_mem_card_add_one.mpr
    exact ⟨u, huM, hau, by omega⟩
  exact (mem_sdiff.mp hai).2 haShadow

theorem level_profileFamily
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m)
    {i : ℕ} (hloi : lo ≤ i) (hihi : i ≤ hi) :
    level (profileFamily n lo hi m) i = selectedLayer n m i := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsF, hscard⟩ := mem_level.mp hs
    obtain ⟨j, hjIcc, hsj⟩ := mem_profileFamily.mp hsF
    have hjBounds : lo ≤ j ∧ j ≤ hi := Finset.mem_Icc.mp hjIcc
    have hjcard : s.card = j :=
      selectedLayer_sized hlo hrec hjBounds.1 hjBounds.2 hsj
    have : j = i := by omega
    simpa [this] using hsj
  · intro hs
    apply mem_level.mpr
    refine ⟨mem_profileFamily.mpr ⟨i, mem_Icc.mpr ⟨hloi, hihi⟩, hs⟩, ?_⟩
    exact selectedLayer_sized hlo hrec hloi hihi hs

/-- Every member of the constructed family lies on one of the requested levels. -/
theorem profileFamily_card_mem_Icc
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m)
    {s : Finset (Fin n)} (hs : s ∈ profileFamily n lo hi m) :
    s.card ∈ Finset.Icc lo hi := by
  obtain ⟨i, hiIcc, hsi⟩ := mem_profileFamily.mp hs
  have hiBounds : lo ≤ i ∧ i ≤ hi := Finset.mem_Icc.mp hiIcc
  have hcard := selectedLayer_sized hlo hrec hiBounds.1 hiBounds.2 hsi
  simpa [hcard] using hiIcc

/--
The sufficiency direction of the prescribed-profile theorem: fitting the
canonical recurrence produces an actual antichain with exactly profile `f`.
-/
theorem profile_sufficiency
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m) :
    ∃ F : Family (Fin n),
      IsSperner F ∧
        (∀ i, lo ≤ i → i ≤ hi → (level F i).card = f i) ∧
        ∀ s ∈ F, s.card ∈ Finset.Icc lo hi := by
  refine ⟨profileFamily n lo hi m, isSperner_profileFamily hlo hrec, ?_, ?_⟩
  · intro i hloi hihi
    rw [level_profileFamily hlo hrec hloi hihi,
      card_selectedLayer hlo hrec hloi hihi]
  · exact fun s hs => profileFamily_card_mem_Icc hlo hrec hs

end Erdos776.KruskalKatona
