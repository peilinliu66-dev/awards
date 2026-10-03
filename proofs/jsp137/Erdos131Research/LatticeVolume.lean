/-
Copyright (c) 2026. Released under Apache 2.0.
Original full-rank lattice count adapter. Its geometric input is the
proved Erdos186 mixed-radius crosspolytope bound, not a new hypothesis.
Compiled and audited; dependencies as in John.lean.
-/
import Erdos131Research.John
import Mathlib.Analysis.Convex.Body

namespace Erdos131Research
noncomputable section
open Set MeasureTheory
open Erdos186.DiscreteJohn Erdos186.DiscreteJohn.RankReduction
open Erdos186.CFP.Bilu.Mahler

theorem full_rank_lattice_points_le_volume (d : ℕ) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (K : ConvexBody (Fin d → ℝ)) (A : Finset (Fin d → ℤ)),
        (∀ x ∈ (K : Set (Fin d → ℝ)), -x ∈ K) →
        (∀ z, z ∈ A ↔ integralEmbed z ∈ K) → realSpan A = ⊤ →
        (A.card : ENNReal) ≤ (C : ENNReal) * volume (K : Set (Fin d → ℝ)) := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨1, by norm_num, ?_⟩
    intro K A _hsym hexact _hspan
    have hzero : (0 : Fin 0 → ℝ) ∈ (K : Set (Fin 0 → ℝ)) :=
      K.zero_mem_of_symmetric _hsym
    have hAzero : (0 : Fin 0 → ℤ) ∈ A := (hexact 0).mpr (by
      rw [integralEmbed_zero]
      exact hzero)
    have hA : A = {0} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hAzero, fun z _ => Subsingleton.elim z 0⟩
    rw [hA, Finset.card_singleton]
    rw [MeasureTheory.Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
    rw [MeasureTheory.Measure.dirac_apply_of_mem hzero]
    norm_num
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    obtain ⟨F, hF, hcert⟩ := intrinsicJohnCertificate d
    let C : ℕ := (2 * F + 1) ^ d * 3 ^ d * d.factorial
    refine ⟨(C : NNReal), by dsimp [C]; positivity, ?_⟩
    intro K A hsym hexact hspan
    have hsymm : ∀ x : Fin d → ℝ, x ∈ K ↔ -x ∈ K := by
      intro x
      constructor
      · exact hsym x
      · intro hx
        simpa using hsym (-x) hx
    obtain ⟨f, hfF, J, _hsteps⟩ :=
      hcert K A K.isCompact' K.convex' K.nonempty' hsymm hexact
    have hrank : sectionRank A = d := by
      rw [sectionRank_eq_finrank_realSpan, hspan]
      simp
    let Jd : Certificate A d f :=
      cast (congrArg (fun r : ℕ => @Certificate d A r f) hrank) J
    have hbalanced := balanced_of_convex_symmetric K.convex' hsymm
    have hbounded : Bornology.IsVonNBounded ℝ (K : Set (Fin d → ℝ)) :=
      (NormedSpace.isVonNBounded_iff ℝ).mpr K.isCompact'.isBounded
    have hupper := outer_volume_le_factorBound_mul_volumeReal Jd hbalanced
      K.convex' hbounded hexact hrank hdpos hfF
    have hcard : (A.card : ℝ) ≤ (Jd.outer.volume : ℝ) := by
      exact_mod_cast (Finset.card_le_card Jd.subset_outer_carrier).trans
        (Erdos186.GAP.card_carrier_le_volume _)
    have hreal : (A.card : ℝ) ≤ (C : ℝ) * volume.real (K : Set (Fin d → ℝ)) :=
      hcard.trans hupper
    have henn := ENNReal.ofReal_le_ofReal hreal
    have hvolFinite : volume (K : Set (Fin d → ℝ)) ≠ ⊤ := K.isCompact'.measure_lt_top.ne
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg C), measureReal_def] at henn
    rw [ENNReal.ofReal_toReal hvolFinite] at henn
    simpa only [ENNReal.ofReal_natCast, ENNReal.coe_natCast] using henn

end
end Erdos131Research

#print axioms Erdos131Research.full_rank_lattice_points_le_volume
