/-
Copyright (c) 2026. Released under Apache 2.0.
Original assembly of the actual Conlon--Fox--Pham/Pham--Zakharov structure
endpoint into the projective paper's real-scale convention. The separately
acquired generic proof and original projective argument retain their authors.
Compiled and audited; Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
-/
import Erdos131Research.GAPCompatibility
import Erdos131Research.CFPScale

open scoped BigOperators
open Filter

namespace Erdos131Research
noncomputable section
open Erdos186.PZ.Reduction Erdos186.DiscreteJohn

private def symmetricIntegerBox {d : ℕ} (M : Fin d → ℕ) : Erdos186.CFP.IntegerBox d :=
  ⟨fun i => -(M i : ℤ), fun i => (M i : ℤ)⟩

private theorem symmetricIntegerBox_carrier {d : ℕ} (M : Fin d → ℕ) :
    (symmetricIntegerBox M).carrier = Nondividing.coordinateBox M := by
  ext x
  rw [Erdos186.CFP.IntegerBox.mem_carrier_iff, Nondividing.mem_coordinateBox]
  rfl

private theorem floor_radius_le {r : ℕ} (N : Fin r → ℕ) {t : ℝ} {k : ℕ}
    (ht : t ≤ (k : ℝ)) (i : Fin r) : ⌊t * (N i : ℝ)⌋₊ ≤ k * N i := by
  have h := Nat.floor_mono (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg (N i)))
  simpa only [← Nat.cast_mul, Nat.floor_natCast] using h

/-- Source-strength CFP conclusion. The translate's location is derived
from reserve subset sums, not added as a premise. -/
theorem cfp_structure (ell : ℕ) (beta : ℝ) (hbeta : 1 < beta) :
    ∃ c : ℝ, 0 < c ∧ ∃ D m₀ : ℕ,
      ∀ (A : Finset (Fin ell → ℤ)) (M : Fin ell → ℕ),
        m₀ ≤ A.card → A ⊆ Nondividing.coordinateBox M →
        ((Nondividing.coordinateBox M).card : ℝ) ≤ (A.card : ℝ) ^ beta →
        ∃ Chat : Finset (Fin ell → ℤ), Chat ⊆ A ∧
          ((A \ Chat).card : ℝ) ≤ c⁻¹ * A.card / Real.log A.card ∧
        ∃ e : ℕ, e ≤ D ∧ ∃ P : Nondividing.GAP ell e,
          Chat ∪ {0} ⊆ P.carrier ∧
        ∃ C₀ : Finset (Fin ell → ℤ), C₀ ⊆ Chat ∧ (C₀.card : ℝ) ≤ structureScale A.card ∧
        ∃ q : Fin ell → ℤ, q ∈ P.dilatedCarrier (structureScale A.card) ∧
          (∀ z ∈ P.dilatedCarrier (c * structureScale A.card),
            q + z ∈ Nondividing.subsetSums C₀) ∧
          Set.InjOn P.evalHom (P.dilatedCoeffBox (c * structureScale A.card) : Set (Fin e → ℤ)) := by
  classical
  obtain ⟨C⟩ : Nonempty (HigherDimensionalContext beta (1 / 2)) :=
    exists_higherDimensionalContext Erdos186.CFP.nonemptyHigherDimensionalCorollary5
      hbeta (by norm_num) (by norm_num)
  let κ : ℝ := (C.scaleNum ell : ℝ) / (C.scaleDen ell : ℝ) * scaleRatio C ell
  let b : ℝ := lossRatio C ell
  have hnum : 0 < (C.scaleNum ell : ℝ) := by exact_mod_cast C.scaleNum_pos ell
  have hden : 0 < (C.scaleDen ell : ℝ) := by exact_mod_cast C.scaleDen_pos ell
  have hκ : 0 < κ := mul_pos (div_pos hnum hden) (scaleRatio_pos C ell)
  have hb : 0 < b := lossRatio_pos C ell
  let c : ℝ := min κ (1 / b)
  have hc : 0 < c := lt_min hκ (one_div_pos.mpr hb)
  have hcκ : c ≤ κ := min_le_left _ _
  have hcb : b ≤ c⁻¹ := by
    have hcb' : c * b ≤ 1 := (le_div_iff₀ hb).mp (min_le_right κ (1 / b))
    have hi : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
    nlinarith
  obtain ⟨t₁, ht₁, hscale⟩ := exists_canonicalScale_threshold C ell
    (by norm_num) (by norm_num) (ε := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨t₂, hcompare⟩ := eventually_atTop.mp (eventually_canonicalScale_comparison C ell)
  refine ⟨c, hc, C.rankBound ell, max t₁ t₂, ?_⟩
  intro A M hlarge hA hbox
  have htA : t₁ ≤ A.card := (le_max_left _ _).trans hlarge
  have htA' : t₂ ≤ A.card := (le_max_right _ _).trans hlarge
  have hm2 : 2 ≤ A.card := ht₁.trans htA
  have hlog : 0 < Real.log (A.card : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < A.card))
  have hS : 0 ≤ structureScale A.card := by unfold structureScale; positivity
  have hsc := hscale A.card htA
  have hcomp := hcompare A.card htA'
  obtain ⟨k, loss, ⟨W⟩, hloss⟩ := C.produce (symmetricIntegerBox M) A
    (canonicalScale C ell A.card)
    (Finset.card_pos.mp (by omega))
    (by rwa [symmetricIntegerBox_carrier])
    (by rwa [symmetricIntegerBox_carrier]) hsc.1 hsc.2.2
  let E := W.enhanced
  have hkscale : c * structureScale A.card ≤ (k : ℝ) := by
    have hmul : (C.scaleNum ell : ℝ) * (canonicalScale C ell A.card : ℝ) ≤
        (C.scaleDen ell : ℝ) * (k : ℝ) := by exact_mod_cast W.scale_lower
    calc
      c * structureScale A.card ≤ κ * structureScale A.card :=
        mul_le_mul_of_nonneg_right hcκ hS
      _ = (C.scaleNum ell : ℝ) * (scaleRatio C ell * structureScale A.card) /
          (C.scaleDen ell : ℝ) := by dsimp [κ]; ring
      _ ≤ (C.scaleNum ell : ℝ) * canonicalScale C ell A.card / (C.scaleDen ell : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcomp.2.1 hnum.le) hden.le
      _ ≤ (k : ℝ) := (div_le_iff₀ hden).mpr (by simpa [mul_comm] using hmul)
  have hcoreloss : ((A \ E.core).card : ℝ) ≤ c⁻¹ * A.card / Real.log A.card := by
    have hnat : ((A \ E.core).card : ℝ) ≤ (loss : ℝ) := by
      exact_mod_cast E.card_sdiff_core_le
    apply hnat.trans (hloss.trans (hcomp.2.2.trans ?_))
    change b * (A.card : ℝ) / Real.log (A.card : ℝ) ≤ _
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcb (Nat.cast_nonneg _)) hlog.le
  let N := E.symmetryRadii
  let P := positiveGAP E.progression.steps N E.symmetryRadii_pos
  have hP : symmetricGAP E.progression.steps N = E.progression :=
    (centered_eq_symmetricGAP E.progression N E.symmetryCentered).symm
  have hPk (j : ℕ) : symmetricGAP E.progression.steps (fun i => j * N i) =
      E.progression.dilate j :=
    (centered_eq_symmetricGAP (E.progression.dilate j) (fun i => j * N i)
      (E.symmetryCentered.dilate j)).symm
  have hPcarrier : P.carrier = E.progression.carrier := by
    rw [positiveGAP_carrier, hP]
  have hcore : E.core ∪ {0} ⊆ P.carrier := by
    rw [hPcarrier]
    simpa only [Finset.union_singleton] using E.core_zero_subset
  have hreserveNat : (E.reserved.card : ℝ) ≤ (canonicalScale C ell A.card : ℝ) := by
    exact_mod_cast E.reserved_small
  have hreserve : (E.reserved.card : ℝ) ≤ structureScale A.card :=
    hreserveNat.trans hcomp.1
  refine ⟨E.core, E.core_subset, hcoreloss, E.rank, E.rank_le, P, hcore,
    E.reserved, E.reserved_subset_core, hreserve, E.translatePoint, ?_, ?_, ?_⟩
  · have hq : E.translatePoint ∈ Erdos186.GAP.subsetSums E.reserved := by
      have hzero := E.dilated_symmetric.zero_mem_carrier
      have h : E.translatePoint ∈ Erdos186.GAP.subsetSums E.reserved :=
        E.covered (Erdos186.CFP.mem_translate_iff.mpr ⟨0, hzero, by simp⟩)
      simpa using h
    obtain ⟨S, hSR, hsum⟩ := Erdos186.GAP.mem_subsetSums_iff.mp hq
    have hRP : E.reserved ⊆ E.progression.carrier :=
      E.reserved_subset_core.trans ((Finset.subset_insert 0 _).trans E.core_zero_subset)
    have hsumP := E.progression.sum_mem_dilate_of_subset hRP hSR
    rw [← hPk S.card] at hsumP
    rw [positiveGAP_dilatedCarrier]
    rw [← hsum]
    apply symmetricGAP_carrier_mono E.progression.steps (fun i => ?_) hsumP
    apply Nat.le_floor
    have hcardReserve : (S.card : ℝ) ≤ (E.reserved.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hSR
    have hcard : (S.card : ℝ) ≤ structureScale A.card :=
      hcardReserve.trans hreserve
    exact_mod_cast mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg (N i))
  · intro z hz
    rw [positiveGAP_dilatedCarrier] at hz
    have hz' : z ∈ (E.progression.dilate k).carrier := by
      rw [← hPk k]
      exact symmetricGAP_carrier_mono E.progression.steps
        (floor_radius_le N hkscale) hz
    have hcovered := E.covered
      (Erdos186.CFP.mem_translate_iff.mpr ⟨z, hz', rfl⟩)
    exact hcovered
  · have hkproper : (symmetricGAP E.progression.steps (fun i => k * N i)).Proper := by
      rw [hPk k]
      exact E.dilate_proper
    have hlargeInj := signed_injOn_of_symmetricGAP_proper _ _ hkproper
    have hsub : (P.dilatedCoeffBox (c * structureScale A.card) : Set (Fin E.rank → ℤ)) ⊆
        (Nondividing.coordinateBox (fun i => k * N i) : Set (Fin E.rank → ℤ)) := by
      intro x hx
      change x ∈ Nondividing.coordinateBox
        (fun i => ⌊(c * structureScale A.card) * (N i : ℝ)⌋₊) at hx
      change x ∈ Nondividing.coordinateBox (fun i => k * N i)
      rw [Nondividing.mem_coordinateBox] at hx ⊢
      intro i
      have h := floor_radius_le N hkscale i
      have hi := hx i
      constructor <;> omega
    exact hlargeInj.mono hsub

end
end Erdos131Research

#print axioms Erdos131Research.cfp_structure
