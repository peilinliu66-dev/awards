/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/ExtremeHull.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions

noncomputable section
namespace Horton

/-- A convex-independent vertex is an extreme point of the convex hull of the vertex set. -/
theorem mem_extremePoints_of_convexIndependent (V : Finset Point)
    (hV : ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)))
    (a : Point) (ha : a ∈ V) :
    a ∈ (convexHull ℝ (V : Set Point)).extremePoints ℝ := by
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hV
  have haK : a ∉ convexHull ℝ ((V : Set Point) \ {a}) := hV a (Finset.mem_coe.mpr ha)
  have haV : a ∈ convexHull ℝ (V : Set Point) := subset_convexHull ℝ _ (Finset.mem_coe.mpr ha)
  rw [mem_extremePoints_iff_left]
  refine ⟨haV, fun x₁ hx₁ x₂ hx₂ hx => ?_⟩
  by_cases hne : ((V : Set Point) \ {a}).Nonempty
  · have hins : insert a ((V : Set Point) \ {a}) = (V : Set Point) :=
      Set.insert_sdiff_singleton.trans (Set.insert_eq_of_mem (Finset.mem_coe.mpr ha))
    rw [← hins, convexHull_insert hne, mem_convexJoin] at hx₁ hx₂
    obtain ⟨a₁, ha₁, y₁, hy₁, hx₁⟩ := hx₁
    obtain ⟨a₂, ha₂, y₂, hy₂, hx₂⟩ := hx₂
    rw [Set.mem_singleton_iff] at ha₁ ha₂
    subst a₁ a₂
    rw [segment_eq_image'] at hx₁ hx₂
    obtain ⟨s, ⟨hs0, -⟩, rfl⟩ := hx₁
    obtain ⟨t, ⟨ht0, -⟩, rfl⟩ := hx₂
    obtain ⟨μ, ν, hμ, hν, hμν, hsum⟩ := hx
    by_cases hs : s = 0
    · simp [hs]
    exfalso
    have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hσ : 0 < μ * s + ν * t := by positivity
    have h1 := congrArg Prod.fst hsum
    have h2 := congrArg Prod.snd hsum
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul] at h1 h2
    have hα : 0 ≤ μ * s / (μ * s + ν * t) := by positivity
    have hβ : 0 ≤ ν * t / (μ * s + ν * t) := by positivity
    have hαβ : μ * s / (μ * s + ν * t) + ν * t / (μ * s + ν * t) = 1 := by
      rw [← add_div, div_self hσ.ne']
    have hmem := (convex_convexHull ℝ ((V : Set Point) \ {a})) hy₁ hy₂ hα hβ hαβ
    have heq :
        (μ * s / (μ * s + ν * t)) • y₁ + (ν * t / (μ * s + ν * t)) • y₂ = a := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        field_simp
        linear_combination h1 - a.1 * hμν
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        field_simp
        linear_combination h2 - a.2 * hμν
    rw [heq] at hmem
    exact haK hmem
  · have hsub : (V : Set Point) ⊆ {a} :=
      Set.sdiff_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp hne)
    exact convexHull_min hsub (convex_singleton a) hx₁

/-- A point collinear with two distinct points lies on the line through them. -/
theorem exists_eq_add_smul_of_orient_eq_zero (a b p : Point) (hab : a ≠ b)
    (hcol : orient a b p = 0) : ∃ t : ℝ, p = a + t • (b - a) := by
  unfold orient at hcol
  by_cases h1 : b.1 - a.1 = 0
  · have h2 : b.2 - a.2 ≠ 0 := by
      intro h2
      exact hab (Prod.ext (by linarith) (by linarith))
    have hp1 : (b.2 - a.2) * (p.1 - a.1) = 0 := by
      linear_combination (p.2 - a.2) * h1 - hcol
    have hp1' : p.1 - a.1 = 0 := (mul_eq_zero.mp hp1).resolve_left h2
    refine ⟨(p.2 - a.2) / (b.2 - a.2), Prod.ext ?_ ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      rw [h1, mul_zero, add_zero]
      linarith
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      field_simp
      ring
  · refine ⟨(p.1 - a.1) / (b.1 - a.1), Prod.ext ?_ ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      field_simp
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      field_simp
      linear_combination hcol

/-- A convex-independent vertex is never in the hull of finitely many other hull points. -/
theorem not_mem_convexHull_of_convexIndependent (V : Finset Point)
    (hV : ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)))
    (a : Point) (ha : a ∈ V) (T : Finset Point)
    (hT : (T : Set Point) ⊆ convexHull ℝ (V : Set Point)) (haT : a ∉ T) :
    a ∉ convexHull ℝ (T : Set Point) := by
  intro h
  have hext := mem_extremePoints_of_convexIndependent V hV a ha
  have hsub : convexHull ℝ (T : Set Point) ⊆ convexHull ℝ (V : Set Point) :=
    convexHull_min hT (convex_convexHull ℝ _)
  have hT' : a ∈ (convexHull ℝ (T : Set Point)).extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset hsub ⟨h, hext⟩
  exact haT (Finset.mem_coe.mp (extremePoints_convexHull_subset hT'))

/-- The line through two convex-independent vertices meets the hull only in their segment. -/
theorem mem_segment_of_collinear_of_mem_convexHull (V : Finset Point)
    (hV : ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)))
    (a b : Point) (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) (p : Point)
    (hp : p ∈ convexHull ℝ (V : Set Point)) (hcol : orient a b p = 0) :
    p ∈ segment ℝ a b := by
  obtain ⟨t, rfl⟩ := exists_eq_add_smul_of_orient_eq_zero a b p hab hcol
  have haV : a ∈ convexHull ℝ (V : Set Point) := subset_convexHull ℝ _ (Finset.mem_coe.mpr ha)
  have hbV : b ∈ convexHull ℝ (V : Set Point) := subset_convexHull ℝ _ (Finset.mem_coe.mpr hb)
  rcases lt_or_ge t 0 with ht | ht0
  · -- `a` lies strictly between `p` and `b`, so `p = a` by extremality of `a`.
    have haext := mem_extremePoints_of_convexIndependent V hV a ha
    rw [mem_extremePoints_iff_left] at haext
    have hopen : a ∈ openSegment ℝ (a + t • (b - a)) b := by
      rw [openSegment_eq_image']
      refine ⟨t / (t - 1), ⟨div_pos_of_neg_of_neg ht (by linarith), ?_⟩, ?_⟩
      · rw [div_lt_one_of_neg (by linarith)]
        linarith
      · have ht1 : t - 1 ≠ 0 := by linarith
        refine Prod.ext ?_ ?_
        · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
          field_simp
          ring
        · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
          field_simp
          ring
    rw [haext.2 _ hp _ hbV hopen]
    exact left_mem_segment ℝ a b
  rcases le_or_gt t 1 with ht1 | ht1
  · rw [segment_eq_image']
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
  · -- `b` lies strictly between `a` and `p`, contradicting extremality of `b`.
    exfalso
    have hbext := mem_extremePoints_of_convexIndependent V hV b hb
    rw [mem_extremePoints_iff_left] at hbext
    have ht : 0 < t := by linarith
    have hopen : b ∈ openSegment ℝ a (a + t • (b - a)) := by
      rw [openSegment_eq_image']
      refine ⟨1 / t, ⟨one_div_pos.mpr ht, (div_lt_one ht).mpr ht1⟩, ?_⟩
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
        field_simp
        ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
        field_simp
        ring
    exact hab (hbext.2 _ haV _ hp hopen)

end Horton
