import Mathlib
import Erdos776.Uniform.OccupiedLevels

/-!
# The universal occupied-level upper bound for Erdős 776

Target: Lean 4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Mathematical source: Yixin He and Quanyu Tang, arXiv:2602.09803v2,
Lemma 2.5.  The strengthened singleton estimate also handles (n,r)=(8,3).

This extension uses, without changing, the upstream definitions and proved
complement/singleton lemmas from mthiim/erdos_776 at commit
1ca43203123642edaac45bf00b6fc333c848b4c9.
Upstream copyright (c) 2026 mthiim and contributors; MIT license retained in
LICENSE-JSP636-MIT.txt.  New proof bodies prepared with OpenAI ChatGPT.
See verification/ for actual local build and terminal axiom reports.
-/

namespace JSP636

open Finset
open Erdos776.Antichain Erdos776.Uniform

/-- Lowering the required multiplicity does not change the family or its levels. -/
theorem multiplicity_mono {n r s : ℕ} {F : Family (Fin n)}
    (hrs : r ≤ s) (hF : IsMultiplicityAntichain F s) :
    IsMultiplicityAntichain F r :=
  ⟨hF.1, fun i hi => hrs.trans (hF.2 i hi)⟩

/-- If at least `r` singletons occur and `n-r ≥ 2`, at most one set
can occur on level `n-r`.  The support outside all singleton points is
constructed, rather than assumed. -/
theorem card_level_sub_le_one_of_singletons
    {n r : ℕ} {F : Family (Fin n)}
    (hnr : r + 2 ≤ n) (hanti : IsSperner F)
    (hsingle : r ≤ (singletonPoints F).card) :
    (level F (n - r)).card ≤ 1 := by
  classical
  let U : Finset (Fin n) := Finset.univ \ singletonPoints F
  have hUcard : U.card ≤ n - r := by
    dsimp only [U]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hsub (s : Finset (Fin n)) (hs : s ∈ level F (n - r)) : s ⊆ U := by
    have hsF : s ∈ F := (mem_level.mp hs).1
    have hscard : s.card = n - r := (mem_level.mp hs).2
    have hdisj := disjoint_singletonPoints_of_card_ne_one hanti hsF
      (show s.card ≠ 1 by omega)
    intro x hx
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_univ x, fun hxs =>
      (Finset.disjoint_left.mp hdisj) hx hxs⟩
  have heq (s : Finset (Fin n)) (hs : s ∈ level F (n - r)) : s = U := by
    apply Finset.eq_of_subset_of_card_le (hsub s hs)
    simpa only [(mem_level.mp hs).2] using hUcard
  apply Finset.card_le_one.mpr
  intro s hs t ht
  exact (heq s hs).trans (heq t ht).symm

/-- Multiplicity at the top of the complement of singleton points is impossible. -/
theorem sub_not_mem_occupiedLevels_of_one
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hnr : r + 2 ≤ n)
    (hF : IsMultiplicityAntichain F r) (hone : 1 ∈ occupiedLevels F) :
    n - r ∉ occupiedLevels F := by
  intro htop
  have hsingle : r ≤ (singletonPoints F).card := by
    rw [card_singletonPoints]
    exact hF.2 1 hone
  have hcap := card_level_sub_le_one_of_singletons hnr hF.1 hsingle
  have hmult := hF.2 (n - r) htop
  omega

/-- A singleton level forces all occurring levels into `1,...,n-r-1`.
The missing final level, not just exclusion of singleton points, supplies
the extra unit needed when `r=2` or `r=3`. -/
theorem occupiedLevels_subset_Icc_pred_of_one
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hnr : r + 2 ≤ n)
    (hF : IsMultiplicityAntichain F r) (hone : 1 ∈ occupiedLevels F) :
    occupiedLevels F ⊆ Finset.Icc 1 (n - r - 1) := by
  have hcoarse := occupiedLevels_subset_Icc_of_one hr (by omega) hF hone
  have hnot := sub_not_mem_occupiedLevels_of_one hr hnr hF hone
  intro i hi
  have hib := Finset.mem_Icc.mp (hcoarse hi)
  have hne : i ≠ n - r := by
    intro heq
    subst i
    exact hnot hi
  exact Finset.mem_Icc.mpr ⟨hib.1, by omega⟩

theorem card_occupiedLevels_le_pred_of_one
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hnr : r + 2 ≤ n)
    (hF : IsMultiplicityAntichain F r) (hone : 1 ∈ occupiedLevels F) :
    (occupiedLevels F).card ≤ n - r - 1 := by
  have hcard := Finset.card_le_card
    (occupiedLevels_subset_Icc_pred_of_one hr hnr hF hone)
  simpa [Nat.card_Icc] using hcard

/-- The complementary version preserves the number of occupied levels exactly. -/
theorem card_occupiedLevels_le_pred_of_penultimate
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hnr : r + 2 ≤ n)
    (hF : IsMultiplicityAntichain F r)
    (hpen : n - 1 ∈ occupiedLevels F) :
    (occupiedLevels F).card ≤ n - r - 1 := by
  have hcomp : IsMultiplicityAntichain (Finset.compls F) r :=
    isMultiplicityAntichain_compls hF
  have hone : 1 ∈ occupiedLevels (Finset.compls F) := by
    rw [occupiedLevels_compls]
    exact Finset.mem_image.mpr ⟨n - 1, hpen, by omega⟩
  have hbound := card_occupiedLevels_le_pred_of_one hr hnr hcomp hone
  simpa only [card_occupiedLevels_compls] using hbound

/-- He–Tang's universal obstruction, with all parameters: `r≥2`, `n≥4`.
This is a bound for every admissible family, not an existence assertion. -/
theorem universal_occupiedLevels_bound
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hn : 4 ≤ n) (hF : IsMultiplicityAntichain F r) :
    (occupiedLevels F).card ≤ n - 3 := by
  have htwo : IsMultiplicityAntichain F 2 := multiplicity_mono hr hF
  by_cases hone : 1 ∈ occupiedLevels F
  · have hbound := card_occupiedLevels_le_pred_of_one
      (r := 2) (by omega) (by omega) htwo hone
    omega
  by_cases hpen : n - 1 ∈ occupiedLevels F
  · have hbound := card_occupiedLevels_le_pred_of_penultimate
      (r := 2) (by omega) (by omega) htwo hpen
    omega
  exact card_occupiedLevels_le_of_boundary_free (by omega) htwo hone hpen

end JSP636

#print axioms JSP636.universal_occupiedLevels_bound
