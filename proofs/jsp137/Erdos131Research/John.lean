/-
Copyright (c) 2026. Released under Apache 2.0.
Original adapter of the separately obtained Erdos186 discrete-John proof.
The nonempty-body hypothesis repairs the empty-body instance in the
projective paper's external interface. This file does not import that axiom.
Compiled and audited; Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
-/
import Erdos131Research.GAPCompatibility
import ErdosProblems.Erdos186.DiscreteJohnMahler
import ErdosProblems.Erdos186.DiscreteJohnMixedVolume

open scoped BigOperators
open Set MeasureTheory

namespace Erdos131Research
noncomputable section
open Erdos186.DiscreteJohn Erdos186.DiscreteJohn.RankReduction
open Erdos186.CFP.Bilu.Mahler

def realSpan {d : ℕ} (A : Finset (Fin d → ℤ)) : Submodule ℝ (Fin d → ℝ) :=
  Submodule.span ℝ (integralEmbed '' (A : Set (Fin d → ℤ)))

theorem range_realSectionSynthesis {d : ℕ} (A : Finset (Fin d → ℤ)) :
    (realSectionSynthesis A).range = realSpan A := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    rw [realSectionSynthesis_apply]
    apply Submodule.sum_mem
    intro i _
    exact (realSpan A).smul_mem _ (sectionStep_mem_realSpan_points A i)
  · apply Submodule.span_le.mpr
    rintro x ⟨z, hz, rfl⟩
    refine ⟨integralEmbed (sectionCoordinates A z (mem_sectionLattice hz)), ?_⟩
    rw [realSectionSynthesis_integralEmbed, sectionSynthesis_eq_integerCombination,
      section_synthesis_coordinates]

theorem sectionRank_eq_finrank_realSpan {d : ℕ} (A : Finset (Fin d → ℤ)) :
    sectionRank A = Module.finrank ℝ (realSpan A) := by
  rw [← range_realSectionSynthesis]
  have h := LinearMap.finrank_range_of_inj (realSectionSynthesis_injective A)
  simpa using h.symm

theorem balanced_of_convex_symmetric {d : ℕ} {K : Set (Fin d → ℝ)}
    (hc : Convex ℝ K) (hs : ∀ x, x ∈ K ↔ -x ∈ K) : Balanced ℝ K := by
  intro a ha x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have ha' : |a| ≤ 1 := by simpa only [Real.norm_eq_abs] using ha
  have h := hc hy ((hs y).mp hy)
    (show 0 ≤ (1 + a) / 2 by linarith [abs_le.mp ha'])
    (show 0 ≤ (1 - a) / 2 by linarith [abs_le.mp ha'])
    (show (1 + a) / 2 + (1 - a) / 2 = 1 by ring)
  convert h using 1 <;> module

/-- A uniform certificate with every step in the intrinsic real span.
The certificate is constructed in intrinsic coordinates and lifted, rather
than treating that extra step-containment conclusion as an assumption. -/
theorem intrinsicJohnCertificate (d : ℕ) :
    ∃ F : ℕ, 1 ≤ F ∧
      ∀ (K : Set (Fin d → ℝ)) (A : Finset (Fin d → ℤ)),
        IsCompact K → Convex ℝ K → K.Nonempty →
        (∀ x, x ∈ K ↔ -x ∈ K) →
        (∀ z, z ∈ A ↔ integralEmbed z ∈ K) →
        ∃ f : ℕ, f ≤ F ∧
          ∃ C : Certificate A (sectionRank A) f,
            ∀ i, integralEmbed (C.steps i) ∈ realSpan A := by
  classical
  choose bound hbound using Erdos186.DiscreteJohn.MahlerExtraction.discreteJohnStatement
  let F := max 1 (∑ e ∈ Finset.range (d + 1), bound e)
  refine ⟨F, le_max_left _ _, ?_⟩
  intro K A hcompact hconvex hne hsymm hexact
  have hbalanced := balanced_of_convex_symmetric hconvex hsymm
  have h0K : (0 : Fin d → ℝ) ∈ K := hbalanced.zero_mem hne
  have hAne : A.Nonempty := ⟨0, (hexact 0).mpr (by simpa using h0K)⟩
  have hbounded : Bornology.IsVonNBounded ℝ K :=
    (NormedSpace.isVonNBounded_iff ℝ).mpr hcompact.isBounded
  let e := sectionRank A
  have hbody := sectionBody_isSymmetricConvexBody A hbalanced hconvex
    hcompact.isClosed hbounded hexact hAne
  obtain ⟨k, f, hk, hf, ⟨C⟩⟩ := hbound e (sectionBody A K) hbody
    (sectionCoordinatePoints A) (sectionCoordinatePoints_exact A K hexact)
  have hek : e ≤ k := sectionRank_le_certificateRank A C
  have hke : k = e := Nat.le_antisymm hk hek
  subst k
  have hfF : f ≤ F := by
    apply hf.trans
    apply (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ?_).trans
      (le_max_right _ _)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (sectionRank_le A))
  refine ⟨f, hfF, liftCertificate A C, ?_⟩
  intro i
  change integralEmbed (sectionSynthesis A (C.steps i)) ∈ realSpan A
  rw [← realSectionSynthesis_integralEmbed]
  rw [← range_realSectionSynthesis]
  exact ⟨integralEmbed (C.steps i), rfl⟩

private theorem small_radius_floor (F f n : ℕ) (hF : 1 ≤ F)
    (hf : 0 < f) (hfF : f ≤ F) :
    ⌊(1 / ((F : ℝ) + 1)) * (max 1 n : ℕ)⌋₊ ≤ n / f := by
  have hn : n < f * (n / f + 1) := by
    have hmod := Nat.mod_lt n hf
    have hdiv := Nat.mod_add_div n f
    nlinarith
  have hN : max 1 n < (F + 1) * (n / f + 1) := by
    apply max_lt
    · nlinarith [Nat.zero_le (n / f)]
    · exact hn.trans_le (Nat.mul_le_mul_right _ (by omega))
  have hreal : ((max 1 n : ℕ) : ℝ) < ((F : ℝ) + 1) * ((n / f : ℕ) + 1 : ℝ) := by
    exact_mod_cast hN
  have hlt : (1 / ((F : ℝ) + 1)) * (max 1 n : ℕ) < ((n / f + 1 : ℕ) : ℝ) := by
    rw [one_div_mul_eq_div]
    apply (div_lt_iff₀ (by positivity : 0 < (F : ℝ) + 1)).mpr
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hreal
  have hfloor : ⌊(1 / ((F : ℝ) + 1)) * (max 1 n : ℕ)⌋₊ < n / f + 1 :=
    (Nat.floor_lt (by positivity : (0 : ℝ) ≤
      (1 / ((F : ℝ) + 1)) * (max 1 n : ℕ))).mpr hlt
  omega

/-- Nonempty, rank-exact replacement for the author's discrete-John axiom.
Radii are made strictly positive at a factor at most `3^d` in cardinality;
the chosen inner scale is smaller than the existing certificate scale. -/
theorem discrete_john (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, 0 < C ∧
      ∀ (h : ℕ) (H : Submodule ℝ (Fin d → ℝ))
        (K : Set (Fin d → ℝ)) (A : Finset (Fin d → ℤ)),
        Module.finrank ℝ H = h → IsCompact K → Convex ℝ K → K.Nonempty →
        (∀ x, x ∈ K ↔ -x ∈ K) → K ⊆ H →
        (∀ z, z ∈ A ↔ integralEmbed z ∈ K) → realSpan A = H →
        ∃ P : Nondividing.GAP d h,
          (∀ i, integralEmbed (P.step i) ∈ H) ∧ P.Proper ∧
          P.dilatedCarrier c ⊆ A ∧ A ⊆ P.carrier ∧
          P.carrier.card ≤ C * A.card := by
  classical
  obtain ⟨F, hF, hcert⟩ := intrinsicJohnCertificate d
  refine ⟨1 / ((F : ℝ) + 1), by positivity,
    (3 * (2 * F + 1)) ^ d, by positivity, ?_⟩
  intro h H K A hdim hcompact hconvex hne hsymm _hKH hexact hspan
  have hAh : sectionRank A = h := by
    rw [sectionRank_eq_finrank_realSpan, hspan, hdim]
  rw [← hAh]
  obtain ⟨f, hfF, C, hsteps⟩ := hcert K A hcompact hconvex hne hsymm hexact
  let radii : Fin (sectionRank A) → ℕ := fun i => max 1 (C.radii i)
  have hpos : ∀ i, 0 < radii i := fun i => lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  let P := positiveGAP C.steps radii hpos
  have hPproper : P.Proper := positiveGAP_proper _ _ _
    (symmetricGAP_proper C.independent radii)
  refine ⟨P, ?_, hPproper, ?_, ?_, ?_⟩
  · intro i
    rw [← hspan]
    exact hsteps i
  · rw [positiveGAP_dilatedCarrier]
    apply (symmetricGAP_carrier_mono C.steps ?_).trans C.inner_carrier_subset
    intro i
    exact small_radius_floor F f (C.radii i) hF C.factor_pos hfF
  · rw [positiveGAP_carrier]
    exact C.subset_outer_carrier.trans
      (symmetricGAP_carrier_mono C.steps fun i => le_max_right _ _)
  · have hpad : (symmetricGAP C.steps radii).volume ≤
        3 ^ sectionRank A * C.outer.volume := by
      rw [symmetricGAP_volume, Certificate.outer, symmetricGAP_volume]
      calc
        (∏ i, (2 * radii i + 1)) ≤ ∏ i, 3 * (2 * C.radii i + 1) := by
          apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          intro i _
          dsimp [radii]
          omega
        _ = _ := by rw [Finset.prod_mul_distrib]; simp
    have hcard : P.carrier.card ≤
        (3 * (2 * f + 1)) ^ sectionRank A * A.card := by
      rw [positiveGAP_carrier,
        Erdos186.GAP.card_carrier_eq_volume _ (symmetricGAP_proper C.independent radii)]
      calc
        (symmetricGAP C.steps radii).volume ≤
            3 ^ sectionRank A * C.outer.volume := hpad
        _ = 3 ^ sectionRank A * C.outer.carrier.card := by
          rw [Erdos186.GAP.card_carrier_eq_volume _ C.outer_proper]
        _ ≤ 3 ^ sectionRank A * ((2 * f + 1) ^ sectionRank A * A.card) :=
          Nat.mul_le_mul_left _ C.card_outer_le
        _ = _ := by rw [mul_pow]; ring
    apply hcard.trans
    apply Nat.mul_le_mul_right
    exact (Nat.pow_le_pow_left (by omega : 3 * (2 * f + 1) ≤ 3 * (2 * F + 1))
      (sectionRank A)).trans
      (Nat.pow_le_pow_right (by omega) (sectionRank_le A))

end
end Erdos131Research

#print axioms Erdos131Research.discrete_john
