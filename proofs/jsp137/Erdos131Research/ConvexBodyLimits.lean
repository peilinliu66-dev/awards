/-
Copyright (c) 2026. Released under the Apache 2.0 license.

Compactness and volume continuity for the non-dividing-set project.
The compactness, support-margin, and dominated-convergence arguments are
adapted from deancureton/MovingSofa, commit
4d5569131940815f47a9ccf3e90a4c5043c56127, under Apache 2.0.
See THIRD_PARTY/NOTICE.md and THIRD_PARTY/MovingSofa-LICENSE.txt.
The transport from Euclidean norm to the author's Pi norm is new.

Compiled and audited; see BUILD_REPORT.json. Intended Lean 4.33.0 / Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d.
-/
import Erdos131Research.Upstream.ConvexHausdorff
import Erdos131Research.Upstream.ConvexSupport
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Sets.VietorisTopology

noncomputable section

open Filter MeasureTheory TopologicalSpace Set
open scoped Topology ENNReal

namespace Erdos131Research

/-- Sequential Blaschke selection, valid in any normed space when all bodies
are contained in one compact body. No interior or full-dimensionality premise. -/
theorem blaschke_selection {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ℕ → ConvexBody E) (C : ConvexBody E)
    (hKC : ∀ n, K n ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ L : ConvexBody E, Tendsto (K ∘ φ) atTop (𝓝 L) := by
  let B : ℕ → NonemptyCompacts E := fun n ↦
    ⟨⟨(K n : Set E), (K n).isCompact⟩, (K n).nonempty⟩
  obtain ⟨L, _, φ, hφ, hlim⟩ :=
    (NonemptyCompacts.isCompact_subsets_of_isCompact C.isCompact).tendsto_subseq
      (show ∀ n, B n ∈ {L : NonemptyCompacts E | (L : Set E) ⊆ C} from hKC)
  have hconv : Convex ℝ (L : Set E) :=
    NonemptyCompacts.convex_of_tendsto (fun n ↦ (K (φ n)).convex) hlim
  refine ⟨φ, hφ, ⟨(L : Set E), hconv, L.isCompact, L.nonempty⟩, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [B, Function.comp_apply, Metric.NonemptyCompacts.dist_eq,
    NonemptyCompacts.coe_mk, Compacts.coe_mk, ConvexBody.coe_mk,
    ← ConvexBody.hausdorffDist_coe] using
    (tendsto_iff_dist_tendsto_zero.mp hlim)

private abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

private def vectorSupport (S : Set (Euc d)) (u : Euc d) : ℝ :=
  sSup ((fun x ↦ inner ℝ x u) '' S)

private theorem abs_vectorSupport_sub_le_hausdorffDist {S T : Set (Euc d)}
    (hS : S.Nonempty) (hcS : IsCompact S) (hT : T.Nonempty) (hcT : IsCompact T)
    {u : Euc d} (hu : ‖u‖ = 1) :
    |vectorSupport S u - vectorSupport T u| ≤ Metric.hausdorffDist S T := by
  simpa only [vectorSupport, hu, mul_one] using
    hcS.abs_csSup_inner_sub_le_hausdorffDist hS hcT hT u

private theorem ball_support_margin
    (U : Set (Euc d)) (L : Set (Euc d)) (q u : (Euc d)) (r : ℝ) (hr : 0 ≤ r)
    (hu : u ∈ U) (hunit : ‖u‖ = 1)
    (hball : Metric.closedBall q r ⊆ ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport L u}) :
    inner ℝ q u + r ≤ vectorSupport L u := by
  have hp : q + r • u ∈ Metric.closedBall q r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [add_sub_cancel_left]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hunit]
    simp
  have hp' := hball hp
  have hpu := (Set.mem_iInter.mp (Set.mem_iInter.mp hp' u) hu)
  dsimp at hpu
  rw [inner_add_left, inner_smul_left] at hpu
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hunit]
    norm_num
  simp only [huu] at hpu
  simpa using hpu

private theorem eventually_ball_center_mem
    (U : Set (Euc d)) (q : (Euc d)) (r : ℝ) (hr : 0 < r)
    (K : ℕ → ConvexBody (Euc d)) (L : ConvexBody (Euc d))
    (hK : ∀ n, (K n : Set (Euc d)) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K n) u})
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set (Euc d)) (L : Set (Euc d)))
      atTop (𝓝 0))
    (hq : ∀ u ∈ U, inner ℝ q u + r ≤ vectorSupport (L : Set (Euc d)) u)
    (hU : ∀ u ∈ U, ‖u‖ = 1) :
    ∀ᶠ n in atTop, q ∈ (K n : Set (Euc d)) := by
  filter_upwards [hlim.eventually (gt_mem_nhds hr)] with n hn
  rw [hK n]
  simp only [Set.mem_iInter]
  intro u hu
  have habs := abs_vectorSupport_sub_le_hausdorffDist
    (K n).nonempty (K n).isCompact L.nonempty L.isCompact (hU u hu)
  have hlower : vectorSupport (L : Set (Euc d)) u -
      Metric.hausdorffDist (K n : Set (Euc d)) (L : Set (Euc d)) ≤
      vectorSupport (K n : Set (Euc d)) u := by
    linarith [neg_le_of_abs_le habs]
  have hqr := hq u hu
  change inner ℝ q u ≤ vectorSupport (K n : Set (Euc d)) u
  calc
    inner ℝ q u ≤ vectorSupport (L : Set (Euc d)) u - r := by linarith
    _ ≤ vectorSupport (L : Set (Euc d)) u - Metric.hausdorffDist (K n : Set (Euc d)) L := by
      exact le_of_lt (by linarith)
    _ ≤ vectorSupport (K n : Set (Euc d)) u := hlower

private theorem euclidean_volume_real_tendsto (K : ℕ → ConvexBody (Euc d)) (L : ConvexBody (Euc d))
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set (Euc d)) (L : Set (Euc d)))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ volume.real (K n : Set (Euc d))) atTop (𝓝 (volume.real (L : Set (Euc d)))) := by
  let U : Set (Euc d) := {u | ‖u‖ = 1}
  have hrepK : ∀ n, (K n : Set (Euc d)) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K n) u} := by
    intro n
    simpa only [U, vectorSupport] using ConvexBody.eq_iInter_halfSpaces (K n)
  have hrepL : (L : Set (Euc d)) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport L u} := by
    simpa only [U, vectorSupport] using ConvexBody.eq_iInter_halfSpaces L
  obtain ⟨R, hR, hcompact⟩ := L.isCompact.exists_isCompact_cthickening
  let C : Set (Euc d) := Metric.cthickening R (L : Set (Euc d))
  have hsubset : ∀ᶠ n in atTop, (K n : Set (Euc d)) ⊆ C := by
    filter_upwards [hlim.eventually (gt_mem_nhds hR)] with n hn p hp
    obtain ⟨q, hq, hpq⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hp hn
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
    exact Metric.mem_cthickening_of_dist_le p q R L hq hpq.le
  have hpointwise : ∀ p ∉ frontier (L : Set (Euc d)),
      Tendsto (fun n ↦ (K n : Set (Euc d)).indicator (fun _ ↦ (1 : ℝ)) p) atTop
        (𝓝 ((L : Set (Euc d)).indicator (fun _ ↦ (1 : ℝ)) p)) := by
    intro p hpfrontier
    by_cases hpL : p ∈ (L : Set (Euc d))
    · have hpint : p ∈ interior (L : Set (Euc d)) := by
        by_contra hp
        exact hpfrontier ((mem_frontier_iff_notMem_interior hpL).mpr hp)
      obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
        (mem_interior_iff_mem_nhds.mp hpint)
      have hmargin : ∀ u ∈ U, inner ℝ p u + r ≤ vectorSupport L u := by
        intro u hu
        rw [hrepL] at hball
        exact ball_support_margin U L p u r hr.le hu hu hball
      have hev := eventually_ball_center_mem U p r hr K L hrepK hlim hmargin
        (fun _ hu ↦ hu)
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [hev] with n hn
      simp [hn, hpL]
    · have hdist : 0 < Metric.infDist p (L : Set (Euc d)) := by
        exact (Metric.infDist_pos_iff_notMem_closure L.nonempty).mp (by
          rwa [L.isClosed.closure_eq])
      have hev : ∀ᶠ n in atTop, p ∉ (K n : Set (Euc d)) := by
        filter_upwards [hlim.eventually (gt_mem_nhds hdist)] with n hn hpn
        have hle := Metric.infDist_le_hausdorffDist_of_mem hpn
          (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
            (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
        linarith
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [hev] with n hn
      simp [hn, hpL]
  have hfrontier : MeasureTheory.volume (frontier (L : Set (Euc d))) = 0 :=
    L.convex.addHaar_frontier MeasureTheory.volume
  have hmeas : ∀ n, MeasurableSet (K n : Set (Euc d)) := fun n ↦ (K n).isCompact.measurableSet
  have hCmeas : MeasurableSet C := hcompact.measurableSet
  have hCint : MeasureTheory.Integrable (C.indicator fun _ ↦ (1 : ℝ)) := by
    exact (MeasureTheory.integrableOn_const hcompact.measure_lt_top.ne).integrable_indicator hCmeas
  have htendsto := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume)
    (F := fun n ↦ (K n : Set (Euc d)).indicator fun _ ↦ (1 : ℝ))
    (f := (L : Set (Euc d)).indicator fun _ ↦ (1 : ℝ))
    (C.indicator fun _ ↦ (1 : ℝ))
    (Filter.Eventually.of_forall fun n ↦
      (measurable_const.indicator (hmeas n)).aestronglyMeasurable)
    (by
      filter_upwards [hsubset] with n hn
      filter_upwards [] with p
      by_cases hp : p ∈ (K n : Set (Euc d))
      · have hpC := hn hp
        simp [hp, hpC]
      · by_cases hpC : p ∈ C <;> simp [hp, hpC])
    hCint
    (by
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hfrontier] with p hp
      exact hpointwise p hp)
  have heqK : ∀ n, (∫ p, (K n : Set (Euc d)).indicator (fun _ ↦ (1 : ℝ)) p) =
      MeasureTheory.volume.real (K n : Set (Euc d)) := by
    intro n
    change (∫ p, (K n : Set (Euc d)).indicator 1 p) = _
    exact MeasureTheory.integral_indicator_one (μ := MeasureTheory.volume) (hmeas n)
  have heqL : (∫ p, (L : Set (Euc d)).indicator (fun _ ↦ (1 : ℝ)) p) =
      MeasureTheory.volume.real (L : Set (Euc d)) := by
    change (∫ p, (L : Set (Euc d)).indicator 1 p) = _
    exact MeasureTheory.integral_indicator_one (μ := MeasureTheory.volume)
      L.isCompact.measurableSet
  simp_rw [heqK] at htendsto
  rw [heqL] at htendsto
  exact htendsto


/-- The all-dimensional Euclidean version, including lower-dimensional limits. -/
private theorem euclidean_volume_tendsto
    (K : ℕ → ConvexBody (Euc d)) (L : ConvexBody (Euc d))
    (hlim : Tendsto K atTop (𝓝 L)) :
    Tendsto (fun n ↦ volume (K n : Set (Euc d))) atTop
      (𝓝 (volume (L : Set (Euc d)))) := by
  have hdist : Tendsto
      (fun n ↦ Metric.hausdorffDist (K n : Set (Euc d)) (L : Set (Euc d)))
      atTop (𝓝 0) := by
    simpa only [ConvexBody.hausdorffDist_coe] using
      (tendsto_iff_dist_tendsto_zero.mp hlim)
  have hreal := euclidean_volume_real_tendsto K L hdist
  have hof := ENNReal.continuous_ofReal.tendsto (volume.real (L : Set (Euc d))) |>.comp hreal
  have hfinite (B : ConvexBody (Euc d)) :
      ENNReal.ofReal (volume.real (B : Set (Euc d))) = volume (B : Set (Euc d)) := by
    exact ENNReal.ofReal_toReal B.isCompact.measure_lt_top.ne
  simpa only [Function.comp_def, hfinite] using hof

private def asNonemptyCompacts {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (K : ConvexBody E) :
    NonemptyCompacts E :=
  ⟨⟨(K : Set E), K.isCompact⟩, K.nonempty⟩

private theorem asNonemptyCompacts_tendsto_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : ℕ → ConvexBody E} {L : ConvexBody E} :
    Tendsto (fun n ↦ asNonemptyCompacts (K n)) atTop (𝓝 (asNonemptyCompacts L)) ↔
      Tendsto K atTop (𝓝 L) := by
  constructor <;> intro h
  · apply tendsto_iff_dist_tendsto_zero.mpr
    have hd := tendsto_iff_dist_tendsto_zero.mp h
    simpa only [asNonemptyCompacts, Metric.NonemptyCompacts.dist_eq,
      NonemptyCompacts.coe_mk, Compacts.coe_mk, ConvexBody.hausdorffDist_coe] using hd
  · apply tendsto_iff_dist_tendsto_zero.mpr
    have hd := tendsto_iff_dist_tendsto_zero.mp h
    simpa only [asNonemptyCompacts, Metric.NonemptyCompacts.dist_eq,
      NonemptyCompacts.coe_mk, Compacts.coe_mk, ConvexBody.hausdorffDist_coe] using hd

private def mapBody {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (K : ConvexBody E) : ConvexBody F :=
  ⟨e '' (K : Set E), K.convex.linear_image e.toLinearMap,
    K.isCompact.image e.continuous, K.nonempty.image e⟩

private theorem mapBody_tendsto {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) {K : ℕ → ConvexBody E} {L : ConvexBody E}
    (hK : Tendsto K atTop (𝓝 L)) :
    Tendsto (fun n ↦ mapBody e (K n)) atTop (𝓝 (mapBody e L)) := by
  apply asNonemptyCompacts_tendsto_iff.mp
  have h := (e.continuous.nonemptyCompacts_map.tendsto
      (asNonemptyCompacts L)).comp (asNonemptyCompacts_tendsto_iff.mpr hK)
  convert h using 1
  · funext n
    apply NonemptyCompacts.ext
    rfl
  · congr 1

/-- Hausdorff convergence implies volume convergence in the author's Pi norm.
No positive-volume, nonempty-interior, or nondegeneracy assumption is added. -/
theorem convexBody_volume_tendsto
    {K : ℕ → ConvexBody (Fin d → ℝ)} {L : ConvexBody (Fin d → ℝ)}
    (hK : Tendsto K atTop (𝓝 L)) :
    Tendsto (fun n ↦ volume (K n : Set (Fin d → ℝ))) atTop
      (𝓝 (volume (L : Set (Fin d → ℝ)))) := by
  let e : (Fin d → ℝ) ≃L[ℝ] Euc d :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)).symm
  have he : MeasurePreserving e := PiLp.volume_preserving_toLp (Fin d)
  have hvol (B : ConvexBody (Fin d → ℝ)) :
      volume (mapBody e B : Set (Euc d)) = volume (B : Set (Fin d → ℝ)) := by
    have h := he.measure_preimage (mapBody e B).isCompact.measurableSet.nullMeasurableSet
    change volume (e ⁻¹' (e '' (B : Set (Fin d → ℝ)))) =
      volume (mapBody e B : Set (Euc d)) at h
    rw [Set.preimage_image_eq _ e.injective] at h
    exact h.symm
  have h := euclidean_volume_tendsto (fun n ↦ mapBody e (K n)) (mapBody e L)
    (mapBody_tendsto e hK)
  simpa only [hvol] using h

end Erdos131Research

#print axioms Erdos131Research.blaschke_selection
#print axioms Erdos131Research.convexBody_volume_tendsto

