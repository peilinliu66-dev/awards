/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Quad.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.ExtremeHull
import EmptyPentagon.Certificate
import EmptyPentagon.Interp
import EmptyPentagon.Signs
import EmptyPentagon.Beam

noncomputable section
namespace Horton

/-- The open half-plane strictly left of the directed line through `u` and `v` is convex. -/
theorem convex_strict_halfplane (u v : Point) : Convex ℝ {q : Point | 0 < orient u v q} := by
  intro x hx y hy a b ha hb hab
  have hx' : 0 < orient u v x := hx
  have hy' : 0 < orient u v y := hy
  show 0 < orient u v (a • x + b • y)
  rw [orient_smul_add u v x y a b hab]
  rcases ha.lt_or_eq with ha' | ha'
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx') (mul_nonneg hb hy'.le)
  · subst ha'
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hy'

/-- If every point of `T` is strictly left of the line `p q` and `z` is on the line, then the
only point of the hull of `insert z T` on the line is `z` itself. -/
theorem eq_of_mem_convexHull_insert_of_orient_zero (p q z : Point) (hz : orient p q z = 0)
    (T : Set Point) (hT : ∀ x ∈ T, 0 < orient p q x) (r : Point)
    (hr : r ∈ convexHull ℝ (insert z T)) (h0 : orient p q r = 0) : r = z := by
  by_cases hne : T.Nonempty
  · rw [convexHull_insert hne, mem_convexJoin] at hr
    obtain ⟨z', hz', y, hy, s, t, hs, ht, hst, rfl⟩ := hr
    rw [Set.mem_singleton_iff] at hz'
    subst hz'
    have hy' : 0 < orient p q y :=
      convexHull_min (fun x hx => hT x hx) (convex_strict_halfplane p q) hy
    rw [orient_smul_add p q _ y s t hst, hz] at h0
    have ht0 : t = 0 := by
      rcases ht.lt_or_eq with ht' | ht'
      · exact absurd h0 (by nlinarith [mul_pos ht' hy'])
      · exact ht'.symm
    subst ht0
    have hs1 : s = 1 := by linarith
    subst hs1
    simp
  · have hT0 : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst hT0
    simpa using hr

/-- Three vertices of a convex-independent set strictly on one side of the line through two
points of its hull form, together with those two points, a set in convex position. -/
theorem convexIndependent_line_five (V : Finset Point)
    (hV : ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)))
    (a b c p q : Point) (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hp : p ∈ convexHull ℝ (V : Set Point)) (hq : q ∈ convexHull ℝ (V : Set Point)) (hpq : p ≠ q)
    (h1 : 0 < orient p q a) (h2 : 0 < orient p q b) (h3 : 0 < orient p q c) :
    ConvexIndependent ℝ
      (fun x : (({a, b, c, p, q} : Finset Point) : Set Point) => (x : Point)) := by
  have hpp : orient p q p = 0 := orient_left_self p q
  have hqq : orient p q q = 0 := orient_right_self p q
  set V' : Finset Point := {a, b, c, p, q} with hV'
  have hV'hull : ∀ x ∈ V', x ∈ convexHull ℝ (V : Set Point) := by
    intro x hx
    simp only [hV', Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr ha)
    · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hb)
    · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hc)
    · exact hp
    · exact hq
  have hvert : ∀ v ∈ V, v ∉ convexHull ℝ ((V'.erase v : Finset Point) : Set Point) :=
    fun v hv => not_mem_convexHull_of_convexIndependent V hV v hv (V'.erase v)
      (fun x hx => hV'hull x (Finset.mem_of_mem_erase (Finset.mem_coe.mp hx)))
      (Finset.notMem_erase v V')
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
  intro v hv
  rw [Finset.mem_coe] at hv
  rw [← Finset.coe_erase]
  simp only [hV', Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv | hv | hv | hv <;> rw [hv]
  · exact hvert a ha
  · exact hvert b hb
  · exact hvert c hc
  · -- `v = p`: the hull of the others meets the line only at `q`
    intro hmem
    have hsub : ((V'.erase p : Finset Point) : Set Point) ⊆
        insert q {x : Point | 0 < orient p q x} := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_erase] at hx
      obtain ⟨hxp, hx⟩ := hx
      simp only [hV', Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact Or.inr h1
      · exact Or.inr h2
      · exact Or.inr h3
      · exact absurd rfl hxp
      · exact Or.inl rfl
    exact hpq (eq_of_mem_convexHull_insert_of_orient_zero p q q hqq _ (fun x hx => hx) p
      (convexHull_mono hsub hmem) hpp)
  · -- `v = q`: the hull of the others meets the line only at `p`
    intro hmem
    have hsub : ((V'.erase q : Finset Point) : Set Point) ⊆
        insert p {x : Point | 0 < orient p q x} := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_erase] at hx
      obtain ⟨hxq, hx⟩ := hx
      simp only [hV', Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact Or.inr h1
      · exact Or.inr h2
      · exact Or.inr h3
      · exact Or.inl rfl
      · exact absurd rfl hxq
    exact hpq (eq_of_mem_convexHull_insert_of_orient_zero p q p hpp _ (fun x hx => hx) q
      (convexHull_mono hsub hmem) hqq).symm

/-- Orientation along the affine line through `a` and `b`. -/
theorem orient_add_smul (u v a b : Point) (s : ℝ) :
    orient u v (a + s • (b - a)) = (1 - s) * orient u v a + s * orient u v b := by
  simp only [orient, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub, smul_eq_mul]
  ring

/-- The diagonals of a counterclockwise convex quadrilateral cross. -/
theorem exists_diagonal_crossing (w1 w2 w3 w4 : Point)
    (h1 : 0 < orient w1 w2 w3) (h2 : 0 < orient w2 w3 w4) (h3 : 0 < orient w3 w4 w1)
    (h4 : 0 < orient w4 w1 w2) :
    ∃ X : Point, X ∈ openSegment ℝ w1 w3 ∧ X ∈ openSegment ℝ w2 w4 := by
  have hA : 0 < orient w2 w4 w1 := by linarith [orient_cyc w2 w4 w1]
  have hB : orient w2 w4 w3 < 0 := by linarith [orient_swap_right w2 w3 w4]
  have hC : orient w1 w3 w2 < 0 := by linarith [orient_swap_right w1 w2 w3]
  have hD : 0 < orient w1 w3 w4 := by linarith [orient_cyc w1 w3 w4]
  have hAB : 0 < orient w2 w4 w1 - orient w2 w4 w3 := by linarith
  set t : ℝ := orient w2 w4 w1 / (orient w2 w4 w1 - orient w2 w4 w3) with ht
  have ht0 : 0 < t := div_pos hA hAB
  have ht1 : t < 1 := (div_lt_one hAB).mpr (by linarith)
  set X : Point := w1 + t • (w3 - w1) with hX
  have hX24 : orient w2 w4 X = 0 := by
    rw [hX, orient_add_smul, ht]
    field_simp
    ring
  have hX13 : orient w1 w3 X = 0 := by
    rw [hX, orient_add_smul, orient_left_self, orient_right_self]
    ring
  have h24 : w2 ≠ w4 := fun h => by
    rw [h, orient_left_self] at h2
    exact lt_irrefl _ h2
  obtain ⟨s, hs⟩ := exists_eq_add_smul_of_orient_eq_zero w2 w4 X h24 hX24
  have hXs : orient w1 w3 X = (1 - s) * orient w1 w3 w2 + s * orient w1 w3 w4 := by
    rw [hs, orient_add_smul]
  have hs0 : 0 < s := by
    by_contra hle
    have e1 : (1 - s) * orient w1 w3 w2 < 0 := mul_neg_of_pos_of_neg (by linarith) hC
    have e2 : s * orient w1 w3 w4 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hle) hD.le
    linarith
  have hs1 : s < 1 := by
    by_contra hle
    have e1 : 0 ≤ (1 - s) * orient w1 w3 w2 :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hC.le
    have e2 : 0 < s * orient w1 w3 w4 := mul_pos (by linarith) hD
    linarith
  refine ⟨X, ?_, ?_⟩
  · rw [openSegment_eq_image']
    exact ⟨t, ⟨ht0, ht1⟩, hX.symm⟩
  · rw [openSegment_eq_image']
    exact ⟨s, ⟨hs0, hs1⟩, hs.symm⟩

/-- A line cannot separate the vertices of a convex quadrilateral alternately. -/
theorem not_alternating (w1 w2 w3 w4 z1 z2 : Point)
    (h1 : 0 < orient w1 w2 w3) (h2 : 0 < orient w2 w3 w4) (h3 : 0 < orient w3 w4 w1)
    (h4 : 0 < orient w4 w1 w2)
    (hl : orient z1 z2 w1 < 0 ∧ 0 < orient z1 z2 w2 ∧ orient z1 z2 w3 < 0 ∧ 0 < orient z1 z2 w4) :
    False := by
  obtain ⟨X, hX13, hX24⟩ := exists_diagonal_crossing w1 w2 w3 w4 h1 h2 h3 h4
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hX13
  obtain ⟨c, d, hc, hd, hcd, hX⟩ := hX24
  have e1 : orient z1 z2 (a • w1 + b • w3) < 0 := by
    rw [orient_smul_add _ _ _ _ a b hab]
    exact add_neg (mul_neg_of_pos_of_neg ha hl.1) (mul_neg_of_pos_of_neg hb hl.2.2.1)
  have e2 : 0 < orient z1 z2 (c • w2 + d • w4) := by
    rw [orient_smul_add _ _ _ _ c d hcd]
    exact add_pos (mul_pos hc hl.2.1) (mul_pos hd hl.2.2.2)
  rw [hX] at e2
  exact lt_asymm e1 e2

/-- A nonvanishing orientation forces its three points to be pairwise distinct. -/
theorem ne_of_orient_ne_zero {u v x : Point} (h : orient u v x ≠ 0) :
    u ≠ v ∧ u ≠ x ∧ v ≠ x := by
  refine ⟨fun e => h ?_, fun e => h ?_, fun e => h ?_⟩
  · rw [e, orient_self_pair]
  · rw [← e, orient_left_self]
  · rw [← e, orient_right_self]

/-- A point of a closed counterclockwise triangle lies in every closed half-plane containing the
three vertices. -/
theorem orient_nonneg_of_triangle (a b c u v y : Point) (habc : 0 < orient a b c)
    (ha : 0 ≤ orient a b y) (hb : 0 ≤ orient b c y) (hc : 0 ≤ orient c a y)
    (hu : 0 ≤ orient u v a) (hv : 0 ≤ orient u v b) (hw : 0 ≤ orient u v c) :
    0 ≤ orient u v y := by
  have key : orient a b c * orient u v y =
      orient b c y * orient u v a + orient c a y * orient u v b + orient a b y * orient u v c := by
    simp only [orient]
    ring
  refine le_of_mul_le_mul_left ?_ habc
  rw [mul_zero, key]
  exact add_nonneg (add_nonneg (mul_nonneg hb hu) (mul_nonneg hc hv)) (mul_nonneg ha hw)

/-- A point outside a counterclockwise convex quadrilateral differs from its vertices. -/
theorem ne_vertices_of_outside (w1 w2 w3 w4 y : Point)
    (h1 : 0 < orient w1 w2 w3) (h2 : 0 < orient w2 w3 w4) (h3 : 0 < orient w3 w4 w1)
    (h4 : 0 < orient w4 w1 w2)
    (hy : orient w1 w2 y < 0 ∨ orient w2 w3 y < 0 ∨ orient w3 w4 y < 0 ∨ orient w4 w1 y < 0) :
    y ≠ w1 ∧ y ≠ w2 ∧ y ≠ w3 ∧ y ≠ w4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> rcases hy with h | h | h | h <;>
    simp only [orient] at h h1 h2 h3 h4 <;> linarith

/-- A point of the cone at an interior point `z` through consecutive vertices `w1, w2` of a
counterclockwise convex quadrilateral that lies outside the closed quadrilateral is strictly
beyond the side `w1 w2`. -/
theorem orient_neg_of_mem_cone (w1 w2 w3 w4 z y : Point)
    (h1 : 0 < orient w1 w2 w3) (h2 : 0 < orient w2 w3 w4) (h3 : 0 < orient w3 w4 w1)
    (h4 : 0 < orient w4 w1 w2)
    (hz : 0 < orient w1 w2 z ∧ 0 < orient w2 w3 z ∧ 0 < orient w3 w4 z ∧ 0 < orient w4 w1 z)
    (hy : orient w1 w2 y < 0 ∨ orient w2 w3 y < 0 ∨ orient w3 w4 y < 0 ∨ orient w4 w1 y < 0)
    (hc1 : 0 < orient z w1 y) (hc2 : 0 < orient z y w2) : orient w1 w2 y < 0 := by
  by_contra hle
  have h0 : 0 ≤ orient w1 w2 y := not_lt.mp hle
  have hT : 0 < orient z w1 w2 := by linarith [orient_cyc z w1 w2]
  have hc2' : 0 ≤ orient w2 z y := by linarith [orient_cyc z y w2, orient_cyc y w2 z]
  have key : ∀ u v : Point, 0 ≤ orient u v z → 0 ≤ orient u v w1 → 0 ≤ orient u v w2 →
      0 ≤ orient u v y :=
    fun u v hu hv hw => orient_nonneg_of_triangle z w1 w2 u v y hT hc1.le h0 hc2' hu hv hw
  rcases hy with h | h | h | h
  · exact absurd (key w1 w2 hz.1.le (orient_left_self _ _).ge (orient_right_self _ _).ge)
      (not_le.mpr h)
  · exact absurd (key w2 w3 hz.2.1.le (by linarith [orient_cyc w1 w2 w3])
      (orient_left_self _ _).ge) (not_le.mpr h)
  · exact absurd (key w3 w4 hz.2.2.1.le h3.le (by linarith [orient_cyc w2 w3 w4]))
      (not_le.mpr h)
  · exact absurd (key w4 w1 hz.2.2.2.le (orient_right_self _ _).ge h4.le) (not_le.mpr h)

/-- Indexed general position of an injective five-tuple drawn from a set in general position. -/
theorem indexedGP_of_generalPosition (S : Finset Point) (hgp : GeneralPosition S)
    (p : Fin 5 → Point) (hmem : ∀ i, p i ∈ S) (hinj : Function.Injective p) : IndexedGP p :=
  fun i j k hij hik hjk =>
    hgp _ (hmem i) _ (hmem j) _ (hmem k) (hinj.ne hij) (hinj.ne hik) (hinj.ne hjk)

/-- A five-tuple of pairwise distinct points is injective. -/
theorem injective_vec5 {a b c d e : Point} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Function.Injective ![a, b, c, d, e] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

/-- Cone covering for a counterclockwise convex quadrilateral with an interior point `z`: a
point `y` outside the closed quadrilateral lies in one of the four cones at `z` through
consecutive vertices, strictly beyond the corresponding side. -/
theorem cone_cover4 (w1 w2 w3 w4 z y : Point)
    (hgp : GeneralPosition ({w1, w2, w3, w4, z, y} : Finset Point))
    (h1 : 0 < orient w1 w2 w3) (h2 : 0 < orient w2 w3 w4) (h3 : 0 < orient w3 w4 w1)
    (h4 : 0 < orient w4 w1 w2)
    (hz : 0 < orient w1 w2 z ∧ 0 < orient w2 w3 z ∧ 0 < orient w3 w4 z ∧ 0 < orient w4 w1 z)
    (hy : orient w1 w2 y < 0 ∨ orient w2 w3 y < 0 ∨ orient w3 w4 y < 0 ∨ orient w4 w1 y < 0) :
    (0 < orient z w1 y ∧ 0 < orient z y w2 ∧ orient w1 w2 y < 0) ∨
    (0 < orient z w2 y ∧ 0 < orient z y w3 ∧ orient w2 w3 y < 0) ∨
    (0 < orient z w3 y ∧ 0 < orient z y w4 ∧ orient w3 w4 y < 0) ∨
    (0 < orient z w4 y ∧ 0 < orient z y w1 ∧ orient w4 w1 y < 0) := by
  obtain ⟨h12, h13, h23⟩ := ne_of_orient_ne_zero h1.ne'
  obtain ⟨-, -, h34⟩ := ne_of_orient_ne_zero h2.ne'
  obtain ⟨-, -, h41⟩ := ne_of_orient_ne_zero h3.ne'
  obtain ⟨-, h1z, h2z⟩ := ne_of_orient_ne_zero hz.1.ne'
  obtain ⟨-, -, h3z⟩ := ne_of_orient_ne_zero hz.2.1.ne'
  obtain ⟨-, -, h4z⟩ := ne_of_orient_ne_zero hz.2.2.1.ne'
  obtain ⟨hy1, hy2, hy3, hy4⟩ := ne_vertices_of_outside w1 w2 w3 w4 y h1 h2 h3 h4 hy
  have hzy : z ≠ y := by
    rintro rfl
    rcases hy with h | h | h | h <;> linarith [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
  have hz2y : orient z w2 y ≠ 0 :=
    hgp z (by simp) w2 (by simp) y (by simp) h2z.symm hzy hy2.symm
  have hz4y : orient z w4 y ≠ 0 :=
    hgp z (by simp) w4 (by simp) y (by simp) h4z.symm hzy hy4.symm
  have h13z : orient w1 w3 z ≠ 0 := hgp w1 (by simp) w3 (by simp) z (by simp) h13 h1z h3z
  rcases lt_or_gt_of_ne h13z with hA | hA
  · -- `z` lies inside the triangle `w1 w2 w3`
    have hz3 : 0 < orient w3 w1 z := by
      rw [orient_swap_left]
      exact neg_pos.2 hA
    have hgp' : IndexedGP ![w1, w2, w3, z, y] :=
      indexedGP_of_generalPosition _ hgp _ (by intro i; fin_cases i <;> simp)
        (injective_vec5 h12 h13 h1z hy1.symm h23 h2z hy2.symm h3z hy3.symm hzy)
    have hyT : orient w1 w2 y < 0 ∨ orient w2 w3 y < 0 ∨ orient w3 w1 y < 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨c1, c2, c3⟩ := hcon
      have k3 : 0 ≤ orient w3 w4 y :=
        orient_nonneg_of_triangle w1 w2 w3 w3 w4 y h1 c1 c2 c3 h3.le
          (by linarith [orient_cyc w2 w3 w4]) (orient_left_self _ _).ge
      have k4 : 0 ≤ orient w4 w1 y :=
        orient_nonneg_of_triangle w1 w2 w3 w4 w1 y h1 c1 c2 c3 (orient_right_self _ _).ge h4.le
          (by linarith [orient_cyc w3 w4 w1])
      rcases hy with h | h | h | h <;> linarith
    have hc : (0 < orient z w1 y ∧ 0 < orient z y w2 ∧ orient w1 w2 y < 0) ∨
        (0 < orient z w2 y ∧ 0 < orient z y w3 ∧ orient w2 w3 y < 0) ∨
        (0 < orient z w3 y ∧ 0 < orient z y w1 ∧ orient w3 w1 y < 0) :=
      cone_cover ![w1, w2, w3, z, y] hgp' h1 hz.1 hz.2.1 hz3 hyT
    rcases hc with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, -⟩
    · exact Or.inl ⟨a, b, c⟩
    · exact Or.inr (Or.inl ⟨a, b, c⟩)
    · rcases lt_or_gt_of_ne hz4y with hd | hd
      · have hd' : 0 < orient z y w4 := by
          rw [orient_swap_right]
          exact neg_pos.2 hd
        exact Or.inr (Or.inr (Or.inl ⟨a, hd', orient_neg_of_mem_cone w3 w4 w1 w2 z y h3 h4 h1 h2
          ⟨hz.2.2.1, hz.2.2.2, hz.1, hz.2.1⟩ (by tauto) a hd'⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hd, b, orient_neg_of_mem_cone w4 w1 w2 w3 z y h4 h1 h2 h3
          ⟨hz.2.2.2, hz.1, hz.2.1, hz.2.2.1⟩ (by tauto) hd b⟩))
  · -- `z` lies inside the triangle `w1 w3 w4`
    have hT : 0 < orient w1 w3 w4 := by linarith [orient_cyc w1 w3 w4]
    have hgp' : IndexedGP ![w1, w3, w4, z, y] :=
      indexedGP_of_generalPosition _ hgp _ (by intro i; fin_cases i <;> simp)
        (injective_vec5 h13 h41.symm h1z hy1.symm h34 h3z hy3.symm h4z hy4.symm hzy)
    have hyT : orient w1 w3 y < 0 ∨ orient w3 w4 y < 0 ∨ orient w4 w1 y < 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨c1, c2, c3⟩ := hcon
      have k1 : 0 ≤ orient w1 w2 y :=
        orient_nonneg_of_triangle w1 w3 w4 w1 w2 y hT c1 c2 c3 (orient_left_self _ _).ge h1.le
          (by linarith [orient_cyc w4 w1 w2])
      have k2 : 0 ≤ orient w2 w3 y :=
        orient_nonneg_of_triangle w1 w3 w4 w2 w3 y hT c1 c2 c3 (by linarith [orient_cyc w1 w2 w3])
          (orient_right_self _ _).ge h2.le
      rcases hy with h | h | h | h <;> linarith
    have hc : (0 < orient z w1 y ∧ 0 < orient z y w3 ∧ orient w1 w3 y < 0) ∨
        (0 < orient z w3 y ∧ 0 < orient z y w4 ∧ orient w3 w4 y < 0) ∨
        (0 < orient z w4 y ∧ 0 < orient z y w1 ∧ orient w4 w1 y < 0) :=
      cone_cover ![w1, w3, w4, z, y] hgp' hT hA hz.2.2.1 hz.2.2.2 hyT
    rcases hc with ⟨a, b, -⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
    · rcases lt_or_gt_of_ne hz2y with hd | hd
      · have hd' : 0 < orient z y w2 := by
          rw [orient_swap_right]
          exact neg_pos.2 hd
        exact Or.inl ⟨a, hd', orient_neg_of_mem_cone w1 w2 w3 w4 z y h1 h2 h3 h4 hz hy a hd'⟩
      · exact Or.inr (Or.inl ⟨hd, b, orient_neg_of_mem_cone w2 w3 w4 w1 z y h2 h3 h4 h1
          ⟨hz.2.1, hz.2.2.1, hz.2.2.2, hz.1⟩ (by tauto) hd b⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, c⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨a, b, c⟩))

end Horton
