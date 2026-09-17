/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Certificate.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions

noncomputable section
namespace Horton

/-- The orientation is affine in its third argument: it is compatible with convex combinations. -/
theorem orient_smul_add (u v x y : Point) (a b : ℝ) (hab : a + b = 1) :
    orient u v (a • x + b • y) = a * orient u v x + b * orient u v y := by
  have hb : b = 1 - a := by linarith
  subst hb
  simp only [orient, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The closed half-plane to the left of the directed line through `u` and `v` is convex. -/
theorem convex_halfplane (u v : Point) : Convex ℝ {q : Point | 0 ≤ orient u v q} := by
  intro x hx y hy a b ha hb hab
  show 0 ≤ orient u v (a • x + b • y)
  rw [orient_smul_add u v x y a b hab]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

/-- A closed half-plane bounded by the line through two distinct points contains the convex hull
of every set it contains, and no point on or beyond its boundary line is interior to that hull. -/
theorem not_mem_interior_convexHull_of_halfplane (V : Finset Point) (u v p : Point)
    (huv : u ≠ v) (hV : ∀ x ∈ V, 0 ≤ orient u v x) (hp : orient u v p ≤ 0) :
    p ∉ interior (convexHull ℝ (V : Set Point)) := by
  intro hmem
  have hsub : convexHull ℝ (V : Set Point) ⊆ {q : Point | 0 ≤ orient u v q} :=
    convexHull_min (fun x hx => hV x (Finset.mem_coe.mp hx)) (convex_halfplane u v)
  have hnhds : {q : Point | 0 ≤ orient u v q} ∈ nhds p :=
    mem_interior_iff_mem_nhds.mp (interior_mono hsub hmem)
  set n : Point := (v.2 - u.2, -(v.1 - u.1)) with hn
  have hcont : Filter.Tendsto (fun t : ℝ => p + t • n) (nhds 0) (nhds p) := by
    have hc : Continuous (fun t : ℝ => p + t • n) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using hc.tendsto 0
  have hev : ∀ᶠ t : ℝ in nhds 0, 0 ≤ orient u v (p + t • n) := hcont hnhds
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hpos : 0 < (v.1 - u.1) ^ 2 + (v.2 - u.2) ^ 2 := by
    by_contra hle
    have hle' := not_lt.mp hle
    have h1 : (v.1 - u.1) ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (v.2 - u.2)]) (sq_nonneg _)
    have h2 : (v.2 - u.2) ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (v.1 - u.1)]) (sq_nonneg _)
    apply huv
    ext
    · linarith [sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)]
    · linarith [sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)]
  have hkey := hball (y := ε / 2)
    (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have hcalc : orient u v (p + (ε / 2) • n) =
      orient u v p - (ε / 2) * ((v.1 - u.1) ^ 2 + (v.2 - u.2) ^ 2) := by
    simp only [orient, hn, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hcalc] at hkey
  nlinarith

/-- Vertices each separated from the others by a supporting line are convex independent. -/
theorem convexIndependent_of_separated (V : Finset Point)
    (h : ∀ v ∈ V, ∃ u ∈ V, ∃ w ∈ V, u ≠ w ∧ orient u w v < 0 ∧
      ∀ x ∈ V, x ≠ v → 0 ≤ orient u w x) :
    ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)) := by
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
  intro v hv hmem
  obtain ⟨u, -, w, -, -, hneg, hsep⟩ := h v (Finset.mem_coe.mp hv)
  have hsub : convexHull ℝ ((V : Set Point) \ {v}) ⊆ {q : Point | 0 ≤ orient u w q} :=
    convexHull_min (fun x hx => hsep x (Finset.mem_coe.mp hx.1) hx.2) (convex_halfplane u w)
  exact absurd (hsub hmem) (not_le.mpr hneg)

/-- A member lying in the convex hull of three other members destroys convex independence. -/
theorem not_convexIndependent_of_mem_convexHull_triple (V : Finset Point) (a b c p : Point)
    (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hp : p ∈ V)
    (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c)
    (hmem : p ∈ convexHull ℝ ({a, b, c} : Set Point)) :
    ¬ ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)) := by
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
  intro hind
  refine hind p (Finset.mem_coe.mpr hp) (convexHull_mono ?_ hmem)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  refine ⟨?_, ?_⟩
  · rcases hx with rfl | rfl | rfl
    · exact Finset.mem_coe.mpr ha
    · exact Finset.mem_coe.mpr hb
    · exact Finset.mem_coe.mpr hc
  · rcases hx with rfl | rfl | rfl
    · exact fun hx => hpa hx.symm
    · exact fun hx => hpb hx.symm
    · exact fun hx => hpc hx.symm

end Horton
