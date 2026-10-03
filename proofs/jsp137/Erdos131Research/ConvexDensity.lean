/-
Copyright (c) 2026. Released under the Apache 2.0 license.

Original interface adapter for the projective non-dividing-set argument of
Theofil Xeff. The mathematical density theorem is Pham--Zakharov, Lemma 1.
Its proof is imported from plby/lean-proofs at
8822f7ddef30fadbd92e1c6ab4ed897af356af5e, whose PZ source files carry
their own Apache 2.0 notices. No author-project source is copied here.

Compiled and audited; see BUILD_REPORT.json. Intended toolchain: Lean 4.33.0; Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d.
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.NormalizedCoreProof
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open Set MeasureTheory
open scoped Topology

namespace Erdos131Research

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The literal algebraic-functional convention used by the projective paper. -/
def SetMuConvexPosition {r : ℕ} (μ : ℝ) (A : Finset (Fin r → ℝ)) : Prop :=
  ∀ p ∈ A, ∃ ell : Module.Dual ℝ (Fin r → ℝ), ∃ t : ℝ,
    t ≤ ell p ∧
      (((A : Set (Fin r → ℝ)) ∩ {x | t ≤ ell x}).ncard : ℝ) ≤ μ * A.card

private theorem ncard_inter_finset {E : Type*} (A : Finset E) (S : Set E) :
    ((A : Set E) ∩ S).ncard = (A.filter fun x => x ∈ S).card := by
  classical
  have h : ((A.filter fun x => x ∈ S : Finset E) : Set E) =
      (A : Set E) ∩ S := by
    ext x
    simp
  rw [← h, Set.ncard_coe_finset]

private theorem card_filter_map_equiv {E F : Type*}
    (A : Finset E) (e : E ≃ F) (S : Set F) :
    ((A.map e.toEmbedding).filter fun y => y ∈ S).card =
      (A.filter fun x => e x ∈ S).card := by
  classical
  have h : (A.map e.toEmbedding).filter (fun y => y ∈ S) =
      (A.filter fun x => e x ∈ S).map e.toEmbedding := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hS⟩
      exact ⟨x, ⟨hx, hS⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hS⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hS⟩
  rw [h, Finset.card_map]

private def euclideanCoordinates (r : ℕ) :
    (Fin r → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin r) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℝ)).symm

private theorem euclideanCoordinates_measurePreserving (r : ℕ) :
    MeasurePreserving (euclideanCoordinates r) := by
  exact PiLp.volume_preserving_toLp (Fin r)

private theorem euclidean_convex_position {r : ℕ} {μ : ℝ}
    (A : Finset (Fin r → ℝ)) (hA : SetMuConvexPosition μ A) :
    Erdos186.ConvexGeometry.IsDeltaConvexPosition μ
      (A.map (euclideanCoordinates r).toEquiv.toEmbedding) := by
  classical
  let e := euclideanCoordinates r
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
  obtain ⟨ell, t, hxt, hcount⟩ := hA x hx
  let ellE : EuclideanSpace ℝ (Fin r) →L[ℝ] ℝ :=
    { toLinearMap := ell.comp e.symm.toLinearMap
      cont := (ell.comp e.symm.toLinearMap).continuous_of_finiteDimensional }
  have heval (z : Fin r → ℝ) : ellE (e z) = ell z := by
    simp [ellE]
  refine ⟨ellE, t, ?_, ?_⟩
  · change t ≤ ellE (e x)
    rw [heval]
    exact hxt
  · rw [Erdos186.ConvexGeometry.halfspaceCount_eq_card_filter]
    have hcard := card_filter_map_equiv A e.toEquiv {z | t ≤ ellE z}
    change ((A.map e.toEquiv.toEmbedding).filter (fun z => t ≤ ellE z)).card =
      (A.filter fun x => t ≤ ellE (e x)).card at hcard
    simp only [heval] at hcard
    rw [hcard, Finset.card_map]
    simpa only [ncard_inter_finset, Set.mem_setOf_eq] using hcount

/-- A measurable compact cap with the literal exponent and quantifier order.

The upstream cap is only asserted convex. Replacing it by the convex hull
of the finitely many captured points supplies measurability, preserves the
count, and can only decrease volume. This avoids any measurability assumption
on an arbitrary convex subset of its boundary.
-/
theorem convex_density_set
    (r : ℕ) (hr : 1 ≤ r) (eps : ℝ) (heps : 0 < eps) :
    ∃ tau μ₀ : ℝ, 0 < tau ∧ tau < 1 ∧ 0 < μ₀ ∧
      ∀ μ : ℝ, 0 < μ → μ < μ₀ → ∃ n₀ : ℕ,
      ∀ (Omega : Set (Fin r → ℝ)) (A : Finset (Fin r → ℝ)),
        n₀ ≤ A.card → IsCompact Omega → Convex ℝ Omega →
        (interior Omega).Nonempty → (A : Set (Fin r → ℝ)) ⊆ Omega →
        SetMuConvexPosition μ A →
        ∃ eta : ℝ, μ ≤ eta ∧ eta ≤ Real.rpow μ tau ∧
        ∃ Omega' : Set (Fin r → ℝ),
          MeasurableSet Omega' ∧ Convex ℝ Omega' ∧ Omega' ⊆ Omega ∧
          volume Omega' ≤ ENNReal.ofReal eta * volume Omega ∧
          (eta ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps)) * A.card ≤
            (((A : Set (Fin r → ℝ)) ∩ Omega').ncard : ℝ) := by
  classical
  obtain ⟨tau, μ₀, htau, htau1, hμ₀, hdensity⟩ :=
    Erdos186.PZ.ConvexDensity.convexDensityStatement r hr eps heps
  refine ⟨tau, μ₀, htau, htau1, hμ₀, ?_⟩
  intro μ hμ hμμ₀
  obtain ⟨n₀, hn₀⟩ := hdensity μ hμ hμμ₀
  refine ⟨n₀, ?_⟩
  intro Omega A hn hcompact hconvex hinterior hsub hposition
  let e := euclideanCoordinates r
  let X := A.map e.toEquiv.toEmbedding
  let OmegaE := e '' Omega
  have hcompactE : IsCompact OmegaE := hcompact.image e.continuous
  have hconvexE : Convex ℝ OmegaE := hconvex.linear_image e.toLinearMap
  have hinteriorE : (interior OmegaE).Nonempty := by
    obtain ⟨x, hx⟩ := hinterior
    refine ⟨e x, mem_interior_iff_mem_nhds.mpr ?_⟩
    have hnhds := (e.toHomeomorph.isOpenMap (interior Omega) isOpen_interior).mem_nhds
      (Set.mem_image_of_mem e hx)
    exact Filter.mem_of_superset hnhds (Set.image_mono interior_subset)
  have hbody : Erdos186.PZ.ConvexDensity.IsConvexBody OmegaE :=
    ⟨hconvexE, hcompactE, hinteriorE⟩
  have hXE : (X : Set (EuclideanSpace ℝ (Fin r))) ⊆ OmegaE := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact Set.mem_image_of_mem e (hsub hx)
  obtain ⟨eta, heta, U, hUconvex, hUsub, hUvolume, hUcount⟩ :=
    hn₀ OmegaE X hbody hXE (by simpa [X] using hn)
      (euclidean_convex_position A hposition)
  let S := Erdos186.PZ.ConvexDensity.pointsIn X U
  let K : Set (EuclideanSpace ℝ (Fin r)) := convexHull ℝ (S : Set _)
  have hKcompact : IsCompact K := S.finite_toSet.isCompact_convexHull ℝ
  have hKconvex : Convex ℝ K := convex_convexHull ℝ _
  have hKU : K ⊆ U := by
    apply convexHull_min
    · intro y hy
      exact (Erdos186.PZ.ConvexDensity.mem_pointsIn.mp hy).2
    · exact hUconvex
  have hSK : (S : Set _) ⊆ K := subset_convexHull ℝ _
  have hcountK : S.card ≤ (X.filter fun y => y ∈ K).card := by
    apply Finset.card_le_card
    intro y hy
    exact Finset.mem_filter.mpr
      ⟨(Erdos186.PZ.ConvexDensity.mem_pointsIn.mp hy).1, hSK hy⟩
  let Omega' := e ⁻¹' K
  have hOmega'meas : MeasurableSet Omega' :=
    hKcompact.measurableSet.preimage e.continuous.measurable
  have hOmega'convex : Convex ℝ Omega' := hKconvex.linear_preimage e.toLinearMap
  have hOmega'sub : Omega' ⊆ Omega := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hUsub (hKU hx)
    exact e.injective heq ▸ hy
  have hpreimageE : e ⁻¹' OmegaE = Omega := by
    exact Set.preimage_image_eq _ e.injective
  have hvolE : volume OmegaE = volume Omega := by
    have h := (euclideanCoordinates_measurePreserving r).measure_preimage
      hcompactE.measurableSet.nullMeasurableSet
    change volume (e ⁻¹' OmegaE) = volume OmegaE at h
    rw [hpreimageE] at h
    exact h.symm
  have hvolK : volume Omega' = volume K :=
    (euclideanCoordinates_measurePreserving r).measure_preimage
      hKcompact.measurableSet.nullMeasurableSet
  have hvol : volume Omega' ≤ ENNReal.ofReal eta * volume Omega := by
    rw [hvolK, ← hvolE]
    exact (measure_mono hKU).trans
      ((Erdos186.PZ.ConvexDensity.relativeVolume_le_iff hbody eta).mp hUvolume)
  refine ⟨eta, heta.1, heta.2, Omega', hOmega'meas, hOmega'convex, hOmega'sub,
    hvol, ?_⟩
  have hcount : (eta ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps)) * A.card ≤
      ((X.filter fun y => y ∈ K).card : ℝ) := by
    have hle : (S.card : ℝ) ≤ (X.filter fun y => y ∈ K).card := by
      exact_mod_cast hcountK
    have hstart : (eta ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps)) * A.card ≤
        (S.card : ℝ) := by
      simpa [Erdos186.PZ.ConvexDensity.densityExponent, X, S] using hUcount
    exact hstart.trans hle
  rw [ncard_inter_finset]
  have hc := card_filter_map_equiv A e.toEquiv K
  change ((A.map e.toEquiv.toEmbedding).filter (fun z => z ∈ K)).card =
    (A.filter fun x => e x ∈ K).card at hc
  change _ ≤ ((A.filter fun x => e x ∈ K).card : ℝ)
  rw [← hc]
  exact hcount

end
end Erdos131Research

#print axioms Erdos131Research.convex_density_set
