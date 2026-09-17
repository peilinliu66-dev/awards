/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/HullVertex.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions

noncomputable section
namespace Horton

/-- A point of minimal abscissa is never interior to the convex hull of a subset. -/
theorem exists_hull_vertex (S : Finset Point) (hS : S.Nonempty) :
    ∃ p ∈ S, ∀ T : Finset Point, T ⊆ S →
      p ∉ interior (convexHull ℝ (T : Set Point)) := by
  obtain ⟨p, hpS, hmin⟩ := S.exists_min_image Prod.fst hS
  refine ⟨p, hpS, fun T hTS hp => ?_⟩
  set H : Set Point := {q | p.1 ≤ q.1} with hH
  have hconv : Convex ℝ H := by
    intro x hx y hy a b ha hb hab
    simp only [hH, Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at hx hy ⊢
    have h1 := mul_le_mul_of_nonneg_left hx ha
    have h2 := mul_le_mul_of_nonneg_left hy hb
    have h3 : (a + b) * p.1 = p.1 := by rw [hab, one_mul]
    linarith
  have hsub : convexHull ℝ (T : Set Point) ⊆ H :=
    convexHull_min (fun x hx => hmin x (hTS hx)) hconv
  have hpH : H ∈ nhds p := mem_interior_iff_mem_nhds.mp (interior_mono hsub hp)
  have htend : Filter.Tendsto (fun t : ℝ => ((p.1 - t, p.2) : Point)) (nhds 0) (nhds p) := by
    have hc : Continuous (fun t : ℝ => ((p.1 - t, p.2) : Point)) := by fun_prop
    simpa using hc.tendsto 0
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((p.1 - t, p.2) : Point) ∈ H :=
    eventually_nhdsWithin_of_eventually_nhds (htend.eventually hpH)
  have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioi (0 : ℝ) :=
    self_mem_nhdsWithin
  obtain ⟨t, ht, htpos⟩ := (hev.and hpos).exists
  simp only [hH, Set.mem_ofPred_eq] at ht
  have : (0 : ℝ) < t := htpos
  linarith

end Horton
