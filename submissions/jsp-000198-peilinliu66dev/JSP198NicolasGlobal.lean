/-
Copyright (c) 2026. Released under the MIT license.

Global finite geometry for the Nicolas empty-hexagon argument.
Imports the unchanged local module and its attributed EmptyPentagon dependencies.
Mathematical source: C. M. Nicolas, The Empty Hexagon Theorem (2007).

This module constructs actual supporting edges and a single boundary cycle,
and proves ray-fan coverage from a finite maximum, not from a coverage premise.
See the accompanying status file for the exact scope of the endpoints.
-/
import Mathlib
import JSP198NicolasLocal

noncomputable section
open Classical Horton

namespace JSP198.Nicolas

/-! ## Actual supporting edges and the cyclic order of a convex finite set -/

/-- Clockwise supporting edge of the actual point set. -/
def BoundaryEdge (Q : Finset Point) (a b : Point) : Prop :=
  a ∈ Q ∧ b ∈ Q ∧ a ≠ b ∧ ∀ x ∈ Q, orient a b x ≤ 0

def boundaryEdges (Q : Finset Point) : Finset (Point × Point) :=
  (Q.product Q).filter (fun e => BoundaryEdge Q e.1 e.2)

@[simp] theorem mem_boundaryEdges {Q : Finset Point} {e : Point × Point} :
    e ∈ boundaryEdges Q ↔ BoundaryEdge Q e.1 e.2 := by
  simp only [boundaryEdges, Finset.mem_filter, Finset.mem_product]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Finset.mem_product.mpr ⟨h.1, h.2.1⟩, h⟩

lemma BoundaryEdge.strict {Q : Finset Point} {a b x : Point}
    (h : BoundaryEdge Q a b) (hgp : GeneralPosition Q)
    (hx : x ∈ Q) (hxa : x ≠ a) (hxb : x ≠ b) :
    orient a b x < 0 := by
  have hn := hgp a h.1 b h.2.1 x hx h.2.2.1 hxa.symm hxb.symm
  exact lt_of_le_of_ne (h.2.2.2 x hx) hn

/-- At an extreme vertex, the determinant order of the remaining points is
transitive. A directed three-cycle would put the vertex inside their triangle. -/
lemma orient_pos_trans_at_vertex
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (o a b c : Point) (ho : o ∈ Q) (ha : a ∈ Q) (hb : b ∈ Q) (hc : c ∈ Q)
    (hab : 0 < orient o a b) (hbc : 0 < orient o b c) :
    0 < orient o a c := by
  have hoa : o ≠ a := by rintro rfl; simp [orient, mul_comm] at hab
  have hob : o ≠ b := by rintro rfl; simp [orient, mul_comm] at hab
  have hoc : o ≠ c := by rintro rfl; simp [orient, mul_comm] at hbc
  have hac : a ≠ c := by
    intro he
    subst c
    have hh : orient o b a = -orient o a b := by unfold orient; ring
    rw [hh] at hbc
    linarith
  have hne := hgp o ho a ha c hc hoa hoc hac
  by_contra hn
  have hneg : orient o a c < 0 := lt_of_le_of_ne (le_of_not_gt hn) hne
  have h1 : 0 < orient a b o := by
    rw [← orient_rotate o a b]
    exact hab
  have h2 : 0 < orient b c o := by
    rw [← orient_rotate o b c]
    exact hbc
  have h3 : 0 < orient c a o := by
    have hh : orient c a o = -orient o a c := by unfold orient; ring
    rw [hh]
    linarith
  have hsum : orient a b c = orient a b o + orient b c o + orient c a o := by
    unfold orient; ring
  have hp := mem_interior_triangle_of_orient_pos a b c o (by linarith) h1 h2 h3
  have hCI := (convexIndependent_set_iff_notMem_convexHull_sdiff.mp hQ) o ho
  apply hCI
  apply convexHull_mono _ (interior_subset hp)
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact ⟨ha, hoa.symm⟩
  · exact ⟨hb, hob.symm⟩
  · exact ⟨hc, hoc.symm⟩

def leftOfAt (Q : Finset Point) (o a : Point) : Finset Point :=
  (Q.erase o).filter (fun b => 0 < orient o a b)

lemma leftOfAt_card_lt
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (o a b : Point) (ho : o ∈ Q) (ha : a ∈ Q) (hb : b ∈ Q)
    (hab : 0 < orient o a b) :
    (leftOfAt Q o b).card < (leftOfAt Q o a).card := by
  have hbo : b ≠ o := by rintro rfl; simp [orient, mul_comm] at hab
  have hbL : b ∈ leftOfAt Q o a := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hbo, hb⟩, hab⟩
  have hsub : leftOfAt Q o b ⊆ (leftOfAt Q o a).erase b := by
    intro c hc
    obtain ⟨hcQ, hbc⟩ := Finset.mem_filter.mp hc
    have hcb : c ≠ b := by rintro rfl; simp [orient, mul_comm] at hbc
    refine Finset.mem_erase.mpr ⟨hcb, Finset.mem_filter.mpr ⟨hcQ, ?_⟩⟩
    exact orient_pos_trans_at_vertex Q hQ hgp o a b c ho ha hb
      (Finset.mem_erase.mp hcQ).2 hab hbc
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hbL] at hcard
  have hpos : 0 < (leftOfAt Q o a).card := Finset.card_pos.mpr ⟨b, hbL⟩
  omega

/-- A genuine outgoing hull edge at every hull vertex. The chosen endpoint
minimizes a finite angular rank; no supporting-line existence is assumed. -/
theorem exists_boundaryEdge_from
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (h2 : 2 ≤ Q.card) (a : Point) (ha : a ∈ Q) :
    ∃ b : Point, BoundaryEdge Q a b := by
  have hne : (Q.erase a).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b, hb, hmin⟩ :=
    Finset.exists_min_image (Q.erase a) (fun b => (leftOfAt Q a b).card) hne
  have hbQ := (Finset.mem_erase.mp hb).2
  have hba := (Finset.mem_erase.mp hb).1
  refine ⟨b, ha, hbQ, hba.symm, ?_⟩
  intro c hc
  by_contra hn
  have hpos : 0 < orient a b c := lt_of_not_ge hn
  have hca : c ≠ a := by rintro rfl; simp [orient, mul_comm] at hpos
  have hlt := leftOfAt_card_lt Q hQ hgp a b c ha hbQ hc hpos
  have hle := hmin c (Finset.mem_erase.mpr ⟨hca, hc⟩)
  omega

lemma boundaryEdge_right_unique
    {Q : Finset Point} (hgp : GeneralPosition Q) {a b c : Point}
    (hab : BoundaryEdge Q a b) (hac : BoundaryEdge Q a c) : b = c := by
  by_contra hbc
  have h1 := hab.2.2.2 c hac.2.1
  have h2 := hac.2.2.2 b hab.2.1
  have hh : orient a c b = -orient a b c := by unfold orient; ring
  rw [hh] at h2
  have hn := hgp a hab.1 b hab.2.1 c hac.2.1 hab.2.2.1 hac.2.2.1 hbc
  apply hn
  linarith

lemma boundaryEdge_left_unique
    {Q : Finset Point} (hgp : GeneralPosition Q) {a b c : Point}
    (hac : BoundaryEdge Q a c) (hbc : BoundaryEdge Q b c) : a = b := by
  by_contra hab
  have h1 := hac.2.2.2 b hbc.1
  have h2 := hbc.2.2.2 a hac.1
  have hh : orient b c a = -orient a c b := by unfold orient; ring
  rw [hh] at h2
  have hn := hgp a hac.1 c hac.2.1 b hbc.1 hac.2.2.1 hab hbc.2.2.1.symm
  apply hn
  linarith

/-- The number of actual clockwise edges is at most the number of vertices. -/
theorem card_boundaryEdges_le (Q : Finset Point) (hgp : GeneralPosition Q) :
    (boundaryEdges Q).card ≤ Q.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro e he
    exact (mem_boundaryEdges.mp he).1
  · intro e he f hf hfst
    apply Prod.ext hfst
    have he' := mem_boundaryEdges.mp he
    have hf' := mem_boundaryEdges.mp hf
    rw [← hfst] at hf'
    exact boundaryEdge_right_unique hgp he' hf'

noncomputable def boundaryNext
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (h2 : 2 ≤ Q.card) (a : (Q : Set Point)) : (Q : Set Point) :=
  ⟨Classical.choose (exists_boundaryEdge_from Q hQ hgp h2 a a.property),
    (Classical.choose_spec (exists_boundaryEdge_from Q hQ hgp h2 a a.property)).2.1⟩

lemma boundaryNext_edge
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (h2 : 2 ≤ Q.card) (a : (Q : Set Point)) :
    BoundaryEdge Q a (boundaryNext Q hQ hgp h2 a) :=
  Classical.choose_spec (exists_boundaryEdge_from Q hQ hgp h2 a a.property)

lemma boundaryNext_injective
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (h2 : 2 ≤ Q.card) : Function.Injective (boundaryNext Q hQ hgp h2) := by
  intro a b hab
  apply Subtype.ext
  have ha := boundaryNext_edge Q hQ hgp h2 a
  have hb := boundaryNext_edge Q hQ hgp h2 b
  rw [hab] at ha
  exact boundaryEdge_left_unique hgp ha hb

noncomputable def boundaryPerm
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (h2 : 2 ≤ Q.card) : Equiv.Perm (Q : Set Point) :=
  Equiv.ofBijective (boundaryNext Q hQ hgp h2)
    ⟨boundaryNext_injective Q hQ hgp h2,
      Finite.surjective_of_injective (boundaryNext_injective Q hQ hgp h2)⟩

lemma boundaryPerm_edge
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (h2 : 2 ≤ Q.card) (a : (Q : Set Point)) :
    BoundaryEdge Q a (boundaryPerm Q hQ hgp h2 a) :=
  boundaryNext_edge Q hQ hgp h2 a

/-- A recursion rather than library-specific iterate notation. -/
def orbit {α : Type*} (f : α → α) (x : α) : ℕ → α
  | 0 => x
  | j + 1 => f (orbit f x j)

/-- Along the boundary, the finite determinant rank strictly increases until
the chosen origin is reached. -/
lemma boundary_rank_increases
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (o a b : Point) (ho : o ∈ Q) (he : BoundaryEdge Q a b)
    (hao : a ≠ o) (hbo : b ≠ o) :
    (leftOfAt Q o a).card < (leftOfAt Q o b).card := by
  have hh := he.strict hgp ho hao.symm hbo.symm
  have hpos : 0 < orient o b a := by
    have hEq : orient o b a = -orient a b o := by unfold orient; ring
    rw [hEq]
    linarith
  exact leftOfAt_card_lt Q hQ hgp o b a ho he.2.1 he.1 hpos

/-- The constructed permutation is one cycle: from any vertex one reaches
any other in at most `Q.card` steps. This rules out disjoint spurious cycles. -/
theorem boundaryPerm_reaches
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (h2 : 2 ≤ Q.card) (x y : (Q : Set Point)) :
    ∃ j : ℕ, j ≤ Q.card ∧ orbit (boundaryPerm Q hQ hgp h2) x j = y := by
  let f := boundaryPerm Q hQ hgp h2
  let z : ℕ → (Q : Set Point) := orbit f x
  by_contra hn
  have havoid : ∀ j : ℕ, j ≤ Q.card → z j ≠ y := by
    intro j hj he
    exact hn ⟨j, hj, he⟩
  have hlower : ∀ j : ℕ, j ≤ Q.card →
      j ≤ (leftOfAt Q (y : Point) (z j : Point)).card := by
    intro j
    induction j with
    | zero => intro _; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have hj' : j ≤ Q.card := by omega
      have hl := ih hj'
      have ha : (z j : Point) ≠ (y : Point) := by
        intro hh
        exact havoid j hj' (Subtype.ext hh)
      have hb : (z (j + 1) : Point) ≠ (y : Point) := by
        intro hh
        exact havoid (j + 1) hj (Subtype.ext hh)
      have he : BoundaryEdge Q (z j) (z (j + 1)) :=
        boundaryPerm_edge Q hQ hgp h2 (z j)
      have hh := boundary_rank_increases Q hQ hgp y (z j)
        (z (j + 1)) y.property he ha hb
      omega
  have hlow := hlower Q.card le_rfl
  have hu := Finset.card_le_card
    (Finset.filter_subset (fun b => 0 < orient (y : Point)
      (z Q.card : Point) b) (Q.erase (y : Point)))
  change (leftOfAt Q (y : Point) (z Q.card : Point)).card ≤
    (Q.erase (y : Point)).card at hu
  rw [Finset.card_erase_of_mem y.property] at hu
  omega

/-- Every vertex also has an incoming edge, obtained from the proved permutation. -/
theorem exists_boundaryEdge_to
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (h2 : 2 ≤ Q.card) (a : Point) (ha : a ∈ Q) :
    ∃ b : Point, BoundaryEdge Q b a := by
  let f := boundaryPerm Q hQ hgp h2
  let aa : (Q : Set Point) := ⟨a, ha⟩
  refine ⟨(f.symm aa : Point), ?_⟩
  have hh := boundaryPerm_edge Q hQ hgp h2 (f.symm aa)
  simpa only [f, Equiv.apply_symm_apply] using hh

/-! ## Ray intersection, selected by a finite maximum -/

def raySide (o x a : Point) : ℝ := orient o x a

def rayDen (o x a b : Point) : ℝ := raySide o x a - raySide o x b

def rayCut (o x a b : Point) : ℝ := -orient o a b / rayDen o x a b

def rayPairs (Q : Finset Point) (o x : Point) : Finset (Point × Point) :=
  (Q.product Q).filter (fun e => 0 < raySide o x e.1 ∧ raySide o x e.2 < 0)

lemma rayDen_pos {o x a b : Point}
    (ha : 0 < raySide o x a) (hb : raySide o x b < 0) :
    0 < rayDen o x a b := by
  dsimp [rayDen]
  linarith

/-- The determinant identity governing all ray-intersection comparisons. -/
lemma ray_plucker (o x a b y : Point) :
    rayDen o x a b * orient o b y +
      (raySide o x y - raySide o x b) * orient o a b =
      -raySide o x b * orient a b y := by
  unfold rayDen raySide orient
  ring

lemma ray_plucker_left (o x a b y : Point) :
    rayDen o x a b * orient o a y -
      (raySide o x a - raySide o x y) * orient o a b =
      -raySide o x a * orient a b y := by
  unfold rayDen raySide orient
  ring

lemma ray_edge_value (o x a b : Point) :
    orient a b x = orient o a b + rayDen o x a b := by
  unfold rayDen raySide orient
  ring

/-- Affine barycentric identity for the intersection of a chord with the ray line. -/
lemma rayCut_affine (o x a b : Point) (hD : rayDen o x a b ≠ 0) :
    o + rayCut o x a b • (x - o) =
      ((-raySide o x b) / rayDen o x a b) • a +
      (raySide o x a / rayDen o x a b) • b := by
  unfold rayCut
  ext <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;>
    field_simp [hD] <;>
    unfold rayDen raySide orient <;> ring

lemma rayCut_mem_hull {Q : Finset Point} {o x a b : Point}
    (haQ : a ∈ Q) (hbQ : b ∈ Q)
    (ha : 0 < raySide o x a) (hb : raySide o x b < 0) :
    o + rayCut o x a b • (x - o) ∈ convexHull ℝ (Q : Set Point) := by
  have hD := rayDen_pos ha hb
  rw [rayCut_affine o x a b (ne_of_gt hD)]
  apply (convex_convexHull ℝ (Q : Set Point))
    (subset_convexHull ℝ _ haQ) (subset_convexHull ℝ _ hbQ)
  · exact div_nonneg (le_of_lt (neg_pos.mpr hb)) hD.le
  · exact div_nonneg ha.le hD.le
  · rw [← add_div]
    have hnum : -raySide o x b + raySide o x a = rayDen o x a b := by
      unfold rayDen
      ring
    rw [hnum, div_self (ne_of_gt hD)]

/-- A maximal chord/ray intersection supports every point not on the ray line.
The proof uses two explicit 2x2 determinant identities, with no angle sorting. -/
lemma maximal_rayPair_support
    (Q : Finset Point) (o x a b : Point)
    (hab : (a,b) ∈ rayPairs Q o x)
    (hmax : ∀ e ∈ rayPairs Q o x, rayCut o x e.1 e.2 ≤ rayCut o x a b)
    (y : Point) (hy : y ∈ Q) (hyn : raySide o x y ≠ 0) :
    orient a b y ≤ 0 := by
  obtain ⟨habQ, ha,hb⟩ := Finset.mem_filter.mp hab
  obtain ⟨haQ,hbQ⟩ := Finset.mem_product.mp habQ
  have hD := rayDen_pos ha hb
  rcases lt_or_gt_of_ne hyn with hyneg | hypos
  · have hay : (a,y) ∈ rayPairs Q o x := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haQ,hy⟩,ha,hyneg⟩
    have hD' := rayDen_pos ha hyneg
    have hm := hmax (a,y) hay
    change -orient o a y / rayDen o x a y ≤
      -orient o a b / rayDen o x a b at hm
    have hm' := (div_le_div_iff₀ hD' hD).mp hm
    have hid := ray_plucker_left o x a b y
    dsimp [rayDen] at hm' hid
    have hp : raySide o x a * orient a b y ≤ 0 := by nlinarith
    by_contra hh
    have ht := mul_pos ha (lt_of_not_ge hh)
    linarith
  · have hyb : (y,b) ∈ rayPairs Q o x := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy,hbQ⟩,hypos,hb⟩
    have hD' := rayDen_pos hypos hb
    have hm := hmax (y,b) hyb
    change -orient o y b / rayDen o x y b ≤
      -orient o a b / rayDen o x a b at hm
    have hm' := (div_le_div_iff₀ hD' hD).mp hm
    have hrev : orient o y b = -orient o b y := by unfold orient; ring
    rw [hrev] at hm'
    have hid := ray_plucker o x a b y
    dsimp [rayDen] at hm' hid
    have hp : 0 ≤ raySide o x b * orient a b y := by nlinarith
    have hnb : 0 < -raySide o x b := neg_pos.mpr hb
    have hp' : (-raySide o x b) * orient a b y ≤ 0 := by nlinarith
    by_contra hh
    have ht := mul_pos hnb (lt_of_not_ge hh)
    linarith

lemma orient_nonpos_on_hull {Q : Finset Point} {a b : Point}
    (hside : ∀ q ∈ Q, orient a b q ≤ 0) {x : Point}
    (hx : x ∈ convexHull ℝ (Q : Set Point)) : orient a b x ≤ 0 := by
  have hs : (Q : Set Point) ⊆ {z : Point | 0 ≤ orient b a z} := by
    intro z hz
    change 0 ≤ orient b a z
    rw [orient_reverse]
    exact neg_nonneg.mpr (hside z hz)
  have hh := convexHull_min hs (convex_halfplane b a)
  have h := hh hx
  change 0 ≤ orient b a x at h
  rw [orient_reverse] at h
  linarith

/-- If an actual chord crosses the ray line, an exterior target lies before
that chord only if it is in the hull. This proves the strict outward side. -/
lemma rayPair_outward
    (Q : Finset Point) (o x a b : Point)
    (ho : o ∈ convexHull ℝ (Q : Set Point))
    (hx : x ∉ convexHull ℝ (Q : Set Point))
    (haQ : a ∈ Q) (hbQ : b ∈ Q)
    (ha : 0 < raySide o x a) (hb : raySide o x b < 0) :
    0 < orient a b x := by
  by_contra hn
  have hle : orient a b x ≤ 0 := le_of_not_gt hn
  have hD := rayDen_pos ha hb
  have hid := ray_edge_value o x a b
  have ht : 1 ≤ rayCut o x a b := by
    apply (le_div_iff₀ hD).mpr
    change 1 * rayDen o x a b ≤ -orient o a b
    linarith
  have htpos : 0 < rayCut o x a b := by linarith
  have hz := rayCut_mem_hull haQ hbQ ha hb
  let t := rayCut o x a b
  have hweights : 0 ≤ 1 - t⁻¹ ∧ 0 ≤ t⁻¹ ∧ (1 - t⁻¹) + t⁻¹ = 1 := by
    have hi0 : 0 ≤ t⁻¹ := inv_nonneg.mpr htpos.le
    have hi1 : t⁻¹ ≤ 1 := (inv_le_one₀ htpos).mpr ht
    exact ⟨by linarith, hi0, by ring⟩
  have hmem := (convex_convexHull ℝ (Q : Set Point)) ho hz
    hweights.1 hweights.2.1 hweights.2.2
  have htne : t ≠ 0 := ne_of_gt htpos
  have hEq : (1 - t⁻¹) • o + t⁻¹ • (o + t • (x - o)) = x := by
    ext <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;>
      field_simp [htne] <;> ring
  apply hx
  change (1 - t⁻¹) • o + t⁻¹ • (o + t • (x - o)) ∈
    convexHull ℝ (Q : Set Point) at hmem
  rwa [hEq] at hmem

/-- Strict halfplanes are used only to obtain both signs at an interior anchor. -/
lemma convex_strict_orient (o x : Point) :
    Convex ℝ {a : Point | 0 < orient o x a} := by
  intro a ha b hb s t hs ht hst
  change 0 < orient o x (s • a + t • b)
  rw [orient_smul_add o x a b s t hst]
  by_cases hs0 : s = 0
  · have ht1 : t = 1 := by linarith
    simpa [hs0,ht1] using hb
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    exact add_pos_of_pos_of_nonneg (mul_pos hspos ha) (mul_nonneg ht hb.le)

lemma rayPairs_nonempty_of_hull
    (Q : Finset Point) (o x : Point)
    (ho : o ∈ convexHull ℝ (Q : Set Point))
    (hgen : ∀ a ∈ Q, raySide o x a ≠ 0) :
    (rayPairs Q o x).Nonempty := by
  have hplus : ∃ a ∈ Q, 0 < raySide o x a := by
    by_contra hn
    push_neg at hn
    have hs : (Q : Set Point) ⊆ {a : Point | 0 < orient x o a} := by
      intro a ha
      have hh : raySide o x a < 0 := lt_of_le_of_ne (hn a ha) (hgen a ha)
      change 0 < orient x o a
      rw [orient_reverse]
      exact neg_pos.mpr hh
    have hh := convexHull_min hs (convex_strict_orient x o) ho
    change 0 < orient x o o at hh
    simp [orient, mul_comm] at hh
  have hminus : ∃ b ∈ Q, raySide o x b < 0 := by
    by_contra hn
    push_neg at hn
    have hs : (Q : Set Point) ⊆ {a : Point | 0 < orient o x a} := by
      intro a ha
      exact lt_of_le_of_ne (hn a ha) (hgen a ha).symm
    have hh := convexHull_min hs (convex_strict_orient o x) ho
    change 0 < orient o x o at hh
    simp [orient, mul_comm] at hh
  obtain ⟨a,ha,ha'⟩ := hplus
  obtain ⟨b,hb,hb'⟩ := hminus
  exact ⟨(a,b), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨ha,hb⟩,ha',hb'⟩⟩

/-- An exterior point is in the unique outward fan at some genuine hull edge.
Existence is proved constructively by maximizing a finite list of ray cuts. -/
theorem exists_boundary_fan
    (Q : Finset Point) (o x : Point)
    (ho : o ∈ convexHull ℝ (Q : Set Point))
    (hx : x ∉ convexHull ℝ (Q : Set Point))
    (hgen : ∀ a ∈ Q, raySide o x a ≠ 0) :
    ∃ a b : Point, BoundaryEdge Q a b ∧
      0 < orient a o x ∧ 0 < orient o b x ∧ 0 < orient a b x := by
  have hne := rayPairs_nonempty_of_hull Q o x ho hgen
  obtain ⟨e,he,hmax⟩ := Finset.exists_max_image (rayPairs Q o x)
    (fun e => rayCut o x e.1 e.2) hne
  rcases e with ⟨a,b⟩
  obtain ⟨habQ,ha,hb⟩ := Finset.mem_filter.mp he
  obtain ⟨haQ,hbQ⟩ := Finset.mem_product.mp habQ
  have hab : a ≠ b := by intro h; subst b; linarith
  have hside : ∀ y ∈ Q, orient a b y ≤ 0 := by
    intro y hy
    exact maximal_rayPair_support Q o x a b he hmax y hy (hgen y hy)
  refine ⟨a,b,⟨haQ,hbQ,hab,hside⟩,?_,?_,?_⟩
  · have hEq : orient a o x = raySide o x a := by unfold raySide orient; ring
    rwa [hEq]
  · have hEq : orient o b x = -raySide o x b := by unfold raySide orient; ring
    rw [hEq]
    exact neg_pos.mpr hb
  · exact rayPair_outward Q o x a b ho hx haQ hbQ ha hb

/-! The fan is a partition, not merely a presumed cover. -/

lemma rayCut_eq_mul (o x a b : Point) (hD : rayDen o x a b ≠ 0) :
    rayCut o x a b * rayDen o x a b = -orient o a b := by
  dsimp [rayCut]
  field_simp [hD]

lemma orient_rayPoint (a b o x : Point) (t : ℝ) :
    orient a b (o + t • (x - o)) =
      orient o a b + t * rayDen o x a b := by
  unfold rayDen raySide orient
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  ring

lemma rayCut_le_of_edge
    (Q : Finset Point) (o x a b c d : Point)
    (he : BoundaryEdge Q a b)
    (ha : 0 < raySide o x a) (hb : raySide o x b < 0)
    (hcQ : c ∈ Q) (hdQ : d ∈ Q)
    (hc : 0 < raySide o x c) (hd : raySide o x d < 0) :
    rayCut o x c d ≤ rayCut o x a b := by
  have hD := rayDen_pos ha hb
  have hz := rayCut_mem_hull hcQ hdQ hc hd
  have hh := orient_nonpos_on_hull he.2.2.2 hz
  rw [orient_rayPoint] at hh
  have heq := rayCut_eq_mul o x a b (ne_of_gt hD)
  nlinarith

lemma rayCut_on_edge (o x a b : Point)
    (hD : rayDen o x a b ≠ 0) :
    orient a b (o + rayCut o x a b • (x - o)) = 0 := by
  rw [orient_rayPoint]
  have heq := rayCut_eq_mul o x a b hD
  linarith

/-- Uniqueness of the actual ray-exit edge, including its orientation. -/
theorem boundary_fan_unique
    (Q : Finset Point) (hgp : GeneralPosition Q) (o x a b c d : Point)
    (hab : BoundaryEdge Q a b) (hcd : BoundaryEdge Q c d)
    (ha : 0 < raySide o x a) (hb : raySide o x b < 0)
    (hc : 0 < raySide o x c) (hd : raySide o x d < 0) :
    a = c ∧ b = d := by
  have hD := rayDen_pos ha hb
  have hD' := rayDen_pos hc hd
  have ht : rayCut o x a b = rayCut o x c d :=
    le_antisymm
      (rayCut_le_of_edge Q o x c d a b hcd hc hd hab.1 hab.2.1 ha hb)
      (rayCut_le_of_edge Q o x a b c d hab ha hb hcd.1 hcd.2.1 hc hd)
  have hz : orient c d (o + rayCut o x a b • (x - o)) = 0 := by
    rw [ht]
    exact rayCut_on_edge o x c d (ne_of_gt hD')
  have hw : (-raySide o x b) / rayDen o x a b +
      raySide o x a / rayDen o x a b = 1 := by
    rw [← add_div]
    have hnum : -raySide o x b + raySide o x a = rayDen o x a b := by
      unfold rayDen
      ring
    rw [hnum, div_self (ne_of_gt hD)]
  rw [rayCut_affine o x a b (ne_of_gt hD),
    orient_smul_add c d a b _ _ hw] at hz
  have hpa : 0 < (-raySide o x b) / rayDen o x a b :=
    div_pos (neg_pos.mpr hb) hD
  have hpb : 0 < raySide o x a / rayDen o x a b := div_pos ha hD
  have hna := hcd.2.2.2 a hab.1
  have hnb := hcd.2.2.2 b hab.2.1
  have hza : orient c d a = 0 := by
    by_contra hn
    have hlt : orient c d a < 0 := lt_of_le_of_ne hna hn
    have hsum : ((-raySide o x b) / rayDen o x a b) * orient c d a +
        (raySide o x a / rayDen o x a b) * orient c d b < 0 :=
      add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hpa hlt)
        (mul_nonpos_of_nonneg_of_nonpos hpb.le hnb)
    linarith
  have haz : a = c ∨ a = d := by
    by_contra hn
    push_neg at hn
    exact (hgp c hcd.1 d hcd.2.1 a hab.1 hcd.2.2.1
      hn.1.symm hn.2.symm) hza
  have hac : a = c := by
    rcases haz with h | h
    · exact h
    · subst a
      linarith
  subst a
  exact ⟨rfl, boundaryEdge_right_unique hgp hab hcd⟩

/-- The determinant fan condition used by the previously proved local cone rule. -/
def InFan (o a b x : Point) : Prop :=
  0 < orient a o x ∧ 0 < orient o b x

lemma inFan_iff_raySides (o a b x : Point) :
    InFan o a b x ↔ 0 < raySide o x a ∧ raySide o x b < 0 := by
  have h1 : orient a o x = raySide o x a := by unfold raySide orient; ring
  have h2 : orient o b x = -raySide o x b := by unfold raySide orient; ring
  unfold InFan
  rw [h1,h2]
  constructor <;> rintro ⟨h,h'⟩ <;> exact ⟨h,by linarith⟩

/-- A fan at a boundary vertex covers the exterior, except for the two actual
incident-edge caps. This is the finite fan used in the three-layer finish. -/
theorem boundary_vertex_fan_cover
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (h2 : 2 ≤ Q.card) (o x : Point) (ho : o ∈ Q)
    (hx : x ∉ convexHull ℝ (Q : Set Point))
    (hgen : ∀ a ∈ Q, a ≠ o → raySide o x a ≠ 0) :
    (∃ a b : Point, BoundaryEdge Q a b ∧ (a = o ∨ b = o) ∧
      0 < orient a b x) ∨
    (∃ a b : Point, BoundaryEdge Q a b ∧ a ≠ o ∧ b ≠ o ∧ InFan o a b x) := by
  obtain ⟨v,hov⟩ := exists_boundaryEdge_from Q hQ hgp h2 o ho
  obtain ⟨u,huo⟩ := exists_boundaryEdge_to Q hQ hgp h2 o ho
  by_cases hvx : 0 < orient o v x
  · exact Or.inl ⟨o,v,hov,Or.inl rfl,hvx⟩
  by_cases hux : 0 < orient u o x
  · exact Or.inl ⟨u,o,huo,Or.inr rfl,hux⟩
  have hvne := hgen v hov.2.1 hov.2.2.1.symm
  have hune := hgen u huo.1 huo.2.2.1
  have hvpos : 0 < raySide o x v := by
    have he : orient o v x = -raySide o x v := by unfold raySide orient; ring
    rw [he] at hvx
    exact lt_of_le_of_ne (by linarith) hvne.symm
  have huneg : raySide o x u < 0 := by
    have he : orient u o x = raySide o x u := by unfold raySide orient; ring
    rw [he] at hux
    exact lt_of_le_of_ne (le_of_not_gt hux) hune
  have huv : u ≠ v := by intro h; subst u; linarith
  have hpair : (v,u) ∈ rayPairs Q o x :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hov.2.1,huo.1⟩,hvpos,huneg⟩
  have hbase : orient o v u < 0 := hov.strict hgp huo.1 huo.2.2.1 huv
  have htpos : 0 < rayCut o x v u :=
    div_pos (neg_pos.mpr hbase) (rayDen_pos hvpos huneg)
  obtain ⟨e,he,hmax⟩ := Finset.exists_max_image (rayPairs Q o x)
    (fun e => rayCut o x e.1 e.2) ⟨(v,u),hpair⟩
  rcases e with ⟨a,b⟩
  obtain ⟨habQ,ha,hb⟩ := Finset.mem_filter.mp he
  obtain ⟨haQ,hbQ⟩ := Finset.mem_product.mp habQ
  have hD := rayDen_pos ha hb
  have htpos' : 0 < rayCut o x a b := lt_of_lt_of_le htpos (hmax _ hpair)
  have ha0 : a ≠ o := by rintro rfl; simp [raySide,orient] at ha
  have hb0 : b ≠ o := by rintro rfl; simp [raySide,orient] at hb
  have hab : a ≠ b := by intro h; subst b; linarith
  have hside : ∀ y ∈ Q, orient a b y ≤ 0 := by
    intro y hy
    by_cases hyo : y = o
    · subst y
      have hid := rayCut_eq_mul o x a b (ne_of_gt hD)
      have hp := mul_pos htpos' hD
      have hrot : orient a b o = orient o a b := by unfold orient; ring
      rw [hrot]
      linarith
    · exact maximal_rayPair_support Q o x a b he hmax y hy (hgen y hy hyo)
  exact Or.inr ⟨a,b,⟨haQ,hbQ,hab,hside⟩,ha0,hb0,
    (inFan_iff_raySides o a b x).mpr ⟨ha,hb⟩⟩

/-! ## Applying the proved cover to actual convex layers -/

lemma boundaryEdge_hull_support {S : Finset Point} {a b : Point}
    (he : BoundaryEdge (hullVertices S) a b) :
    ∀ x ∈ S, orient a b x ≤ 0 := by
  intro x hx
  apply orient_nonpos_on_hull he.2.2.2
  rw [convexHull_hullVertices]
  exact subset_convexHull ℝ _ hx

lemma outer_not_mem_inner_hull (P : Finset Point) {x : Point}
    (hx : x ∈ hullVertices P) :
    x ∉ convexHull ℝ (inner P : Set Point) := by
  apply hull_vertex_not_mem_hull
    (show (inner P : Set Point) ⊆ convexHull ℝ (P : Set Point) from
      fun y hy => subset_convexHull ℝ _ (Finset.mem_sdiff.mp hy).1) hx
  exact fun hh => (Finset.mem_sdiff.mp hh).2 hx

lemma inner_hull_point (P : Finset Point) {x : Point} (hx : x ∈ inner P) :
    x ∈ convexHull ℝ ((hullVertices (inner P) : Finset Point) : Set Point) := by
  rw [convexHull_hullVertices]
  exact subset_convexHull ℝ _ hx

lemma nested_inner_subset (P : Finset Point) : inner (inner P) ⊆ inner P :=
  Finset.sdiff_subset

lemma layer_ray_general_position
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner P))
    (x : Point) (hx : x ∈ hullVertices P) :
    ∀ a ∈ hullVertices (inner P), raySide o x a ≠ 0 := by
  intro a ha
  have hoI := (Finset.mem_sdiff.mp ho).1
  have hoP := (Finset.mem_sdiff.mp hoI).1
  have haI := hullVertices_subset (inner P) ha
  have haP := (Finset.mem_sdiff.mp haI).1
  have hxo : o ≠ x := by
    intro he
    exact (Finset.mem_sdiff.mp hoI).2 (by simpa only [he] using hx)
  have hoa : o ≠ a := by
    intro he
    exact (Finset.mem_sdiff.mp ho).2 (by simpa only [he] using ha)
  have hxa : x ≠ a := by
    intro he
    exact (Finset.mem_sdiff.mp haI).2 (by simpa only [he] using hx)
  exact hgp o hoP x (hullVertices_subset P hx) a haP hxo hoa hxa

def outerFan (P : Finset Point) (o : Point) (e : Point × Point) : Finset Point :=
  (hullVertices P).filter (fun x => InFan o e.1 e.2 x)

/-- The cover is produced from the actual hull, not supplied as a hypothesis. -/
theorem outer_fan_cover
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner P)) :
    ∀ x ∈ hullVertices P,
      ∃ e ∈ boundaryEdges (hullVertices (inner P)), x ∈ outerFan P o e := by
  intro x hx
  have hoQ := inner_hull_point P (Finset.mem_sdiff.mp ho).1
  have hxQ : x ∉ convexHull ℝ
      ((hullVertices (inner P) : Finset Point) : Set Point) := by
    rw [convexHull_hullVertices]
    exact outer_not_mem_inner_hull P hx
  obtain ⟨a,b,he,h1,h2,-⟩ := exists_boundary_fan
    (hullVertices (inner P)) o x hoQ hxQ (layer_ray_general_position P hgp o ho x hx)
  exact ⟨(a,b), mem_boundaryEdges.mpr he, Finset.mem_filter.mpr ⟨hx,h1,h2⟩⟩

/-- The old local empty-hexagon lemma bounds every cell of the new actual cover. -/
theorem outerFan_card_le_two
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner P) (e : Point × Point)
    (he : BoundaryEdge (hullVertices (inner P)) e.1 e.2)
    (hon : o ≠ e.1) (hom : o ≠ e.2) :
    (outerFan P o e).card ≤ 2 := by
  have hu := hullVertices_subset (inner P) he.1
  have hv := hullVertices_subset (inner P) he.2.1
  have hinner := boundaryEdge_hull_support he
  have hneq := hgp e.1 (Finset.mem_sdiff.mp hu).1
    e.2 (Finset.mem_sdiff.mp hv).1 o (Finset.mem_sdiff.mp ho).1
    he.2.2.1 hon.symm hom.symm
  have hneg : orient e.1 e.2 o < 0 := lt_of_le_of_ne (hinner o ho) hneq
  by_contra hn
  have h3 : 3 ≤ (outerFan P o e).card := by omega
  apply hno
  exact hasEmptySix_of_three_in_cone P (outerFan P o e) hgp e.1 e.2 o
    hu hv ho hneg hinner (Finset.filter_subset _ _) (by
      intro x hx
      exact (Finset.mem_filter.mp hx).2) h3

lemma card_le_sum_of_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (I : Finset β) (cells : β → Finset α)
    (hcover : ∀ x ∈ S, ∃ i ∈ I, x ∈ cells i) :
    S.card ≤ ∑ i ∈ I, (cells i).card := by
  have hs : S ⊆ I.biUnion cells := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨i,hi,hxi⟩
  exact (Finset.card_le_card hs).trans Finset.card_biUnion_le

/-- Global interior-apex fan bound, used both for Theorem 4's sectors and for
the three-layer finish. It has no presumed matching or coverage premise. -/
theorem outer_card_le_twice_second_of_third_nonempty
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (hdeep : (inner (inner P)).Nonempty) :
    (hullVertices P).card ≤ 2 * (hullVertices (inner P)).card := by
  obtain ⟨o,ho⟩ := hdeep
  have hoI := (Finset.mem_sdiff.mp ho).1
  have hcov := outer_fan_cover P hgp o ho
  have hsum := card_le_sum_of_cover (hullVertices P)
    (boundaryEdges (hullVertices (inner P))) (outerFan P o) hcov
  have hcell : ∀ e ∈ boundaryEdges (hullVertices (inner P)),
      (outerFan P o e).card ≤ 2 := by
    intro e he
    have he' := mem_boundaryEdges.mp he
    apply outerFan_card_le_two P hgp hno o hoI e he'
    · intro hh
      exact (Finset.mem_sdiff.mp ho).2 (by simpa only [hh] using he'.1)
    · intro hh
      exact (Finset.mem_sdiff.mp ho).2 (by simpa only [hh] using he'.2.1)
  have hs := Finset.sum_le_sum hcell
  have hecount := card_boundaryEdges_le (hullVertices (inner P))
    (gp_subset hgp ((hullVertices_subset (inner P)).trans Finset.sdiff_subset))
  have hsum2 : (∑ e ∈ boundaryEdges (hullVertices (inner P)), (2 : ℕ)) =
      2 * (boundaryEdges (hullVertices (inner P))).card := by
    simp [mul_comm]
  rw [hsum2] at hs
  omega

/-- Cap upper bound without the minimality hypothesis used for the lower bound. -/
theorem outer_cap_card_le_three
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (a b : Point) (he : BoundaryEdge (hullVertices (inner P)) a b) :
    (cap P a b).card ≤ 3 := by
  have ha := hullVertices_subset (inner P) he.1
  have hb := hullVertices_subset (inner P) he.2.1
  have hinner := boundaryEdge_hull_support he
  by_contra hn
  have h4 : 4 ≤ (cap P a b).card := by omega
  obtain ⟨K,hK,hK4⟩ := Finset.exists_subset_card_eq h4
  have hKA : K ⊆ hullVertices P := hK.trans (Finset.filter_subset _ _)
  have hpos : ∀ x ∈ K, 0 < orient a b x := by
    intro x hx
    obtain ⟨hxA,hxle⟩ := Finset.mem_filter.mp (hK hx)
    have hax : a ≠ x := by
      intro hh
      exact (Finset.mem_sdiff.mp ha).2 (by simpa only [hh] using hxA)
    have hbx : b ≠ x := by
      intro hh
      exact (Finset.mem_sdiff.mp hb).2 (by simpa only [hh] using hxA)
    have hh := hgp a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1
      x (hullVertices_subset P hxA) he.2.2.1 hax hbx
    exact lt_of_le_of_ne hxle hh.symm
  have hempty := empty_polygon_edge_cap P K a b ha hb he.2.2.1 hKA hpos hinner
  have hd : Disjoint K ({a,b} : Finset Point) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxab
    simp only [Finset.mem_insert,Finset.mem_singleton] at hxab
    rcases hxab with rfl | rfl
    · exact (Finset.mem_sdiff.mp ha).2 (hKA hx)
    · exact (Finset.mem_sdiff.mp hb).2 (hKA hx)
  apply hno
  refine ⟨K ∪ {a,b},?_,hempty⟩
  rw [Finset.card_union_of_disjoint hd]
  simp [hK4,he.2.2.1]

def Incident (o : Point) (e : Point × Point) : Prop := e.1 = o ∨ e.2 = o

def vertexFanCell (P : Finset Point) (o : Point) (e : Point × Point) : Finset Point :=
  if Incident o e then cap P e.1 e.2 else outerFan P o e

lemma incident_edges_card_le_two
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (h2 : 2 ≤ Q.card) (o : Point) (ho : o ∈ Q) :
    ((boundaryEdges Q).filter (Incident o)).card ≤ 2 := by
  obtain ⟨v,hov⟩ := exists_boundaryEdge_from Q hQ hgp h2 o ho
  obtain ⟨u,huo⟩ := exists_boundaryEdge_to Q hQ hgp h2 o ho
  have hs : (boundaryEdges Q).filter (Incident o) ⊆ {(o,v),(u,o)} := by
    intro e he
    obtain ⟨he,hi⟩ := Finset.mem_filter.mp he
    have hedge := mem_boundaryEdges.mp he
    rcases e with ⟨a,b⟩
    rcases hi with ha | hb
    · change a = o at ha
      subst a
      have hEq := boundaryEdge_right_unique hgp hedge hov
      change b = v at hEq
      subst b
      simp
    · change b = o at hb
      subst b
      have hEq := boundaryEdge_left_unique hgp hedge huo
      change a = u at hEq
      subst a
      simp
  calc
    ((boundaryEdges Q).filter (Incident o)).card ≤ ({(o,v),(u,o)} : Finset _).card :=
      Finset.card_le_card hs
    _ ≤ ({(u,o)} : Finset _).card + 1 := Finset.card_insert_le _ _
    _ = 2 := by simp

lemma sum_two_plus_indicator {α : Type*} [DecidableEq α]
    (S : Finset α) (p : α → Prop) [DecidablePred p] :
    (∑ x ∈ S, (2 + if p x then 1 else 0 : ℕ)) = 2 * S.card + (S.filter p).card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have haf : a ∉ S.filter p := fun h => ha (Finset.mem_filter.mp h).1
    simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Finset.filter_insert]
    by_cases hp : p a
    · simp only [if_pos hp, Finset.card_insert_of_notMem haf, ih]
      omega
    · simp only [if_neg hp, ih]
      omega

/-- Exterior cover anchored at an actual vertex of the second layer, with only
two exceptional cap cells. All geometry is discharged by boundary_vertex_fan_cover. -/
theorem outer_card_le_twice_second_add_two
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (h2 : 2 ≤ (hullVertices (inner P)).card) :
    (hullVertices P).card ≤ 2 * (hullVertices (inner P)).card + 2 := by
  let Q := hullVertices (inner P)
  have hQ : InConvexPosition Q := convexIndependent_hullVertices (inner P)
  have hQgp : GeneralPosition Q :=
    gp_subset hgp ((hullVertices_subset (inner P)).trans Finset.sdiff_subset)
  have hQne : Q.Nonempty := Finset.card_pos.mp (by
    change 0 < (hullVertices (inner P)).card
    omega)
  obtain ⟨o,ho⟩ := hQne
  have hoI := hullVertices_subset (inner P) ho
  have hcover : ∀ x ∈ hullVertices P,
      ∃ e ∈ boundaryEdges Q, x ∈ vertexFanCell P o e := by
    intro x hx
    have hxH : x ∉ convexHull ℝ (Q : Set Point) := by
      dsimp [Q]
      rw [convexHull_hullVertices]
      exact outer_not_mem_inner_hull P hx
    have hgen : ∀ a ∈ Q, a ≠ o → raySide o x a ≠ 0 := by
      intro a ha hao
      have haI := hullVertices_subset (inner P) ha
      have hox : o ≠ x := by
        intro hh
        exact (Finset.mem_sdiff.mp hoI).2 (by simpa only [hh] using hx)
      have hxa : x ≠ a := by
        intro hh
        exact (Finset.mem_sdiff.mp haI).2 (by simpa only [hh] using hx)
      exact hgp o (Finset.mem_sdiff.mp hoI).1 x (hullVertices_subset P hx)
        a (Finset.mem_sdiff.mp haI).1 hox hao.symm hxa
    rcases boundary_vertex_fan_cover Q hQ hQgp h2 o x ho hxH hgen with hh | hh
    · obtain ⟨a,b,he,hi,hpos⟩ := hh
      refine ⟨(a,b),mem_boundaryEdges.mpr he,?_⟩
      have hi' : Incident o (a,b) := hi
      simp only [vertexFanCell,if_pos hi']
      exact Finset.mem_filter.mpr ⟨hx,hpos.le⟩
    · obtain ⟨a,b,he,hao,hbo,hfan⟩ := hh
      refine ⟨(a,b),mem_boundaryEdges.mpr he,?_⟩
      have hi : ¬Incident o (a,b) := by
        intro hh
        exact hh.elim hao hbo
      simp only [vertexFanCell,if_neg hi]
      exact Finset.mem_filter.mpr ⟨hx,hfan⟩
  have hcell : ∀ e ∈ boundaryEdges Q,
      (vertexFanCell P o e).card ≤ 2 + if Incident o e then 1 else 0 := by
    intro e he
    have hedge := mem_boundaryEdges.mp he
    by_cases hi : Incident o e
    · simp only [vertexFanCell,if_pos hi]
      exact outer_cap_card_le_three P hgp hno e.1 e.2 hedge
    · simp only [vertexFanCell,if_neg hi,Nat.add_zero]
      have hne : o ≠ e.1 ∧ o ≠ e.2 := by
        constructor
        · intro hh; exact hi (Or.inl hh.symm)
        · intro hh; exact hi (Or.inr hh.symm)
      exact outerFan_card_le_two P hgp hno o hoI e hedge hne.1 hne.2
  have h1 := card_le_sum_of_cover (hullVertices P) (boundaryEdges Q)
    (vertexFanCell P o) hcover
  have h2' := Finset.sum_le_sum hcell
  rw [sum_two_plus_indicator] at h2'
  have h3 := incident_edges_card_le_two Q hQ hQgp h2 o ho
  have h4 := card_boundaryEdges_le Q hQgp
  change (hullVertices P).card ≤ 2 * Q.card + 2
  omega

/-! Small inner layers: these do not require a polygon of size at least three. -/

lemma inner_empty_hull_eq (S : Finset Point) (h : inner S = ∅) : hullVertices S = S := by
  apply Finset.Subset.antisymm (hullVertices_subset S)
  intro x hx
  by_contra hn
  have hh : x ∈ inner S := Finset.mem_sdiff.mpr ⟨hx,hn⟩
  rw [h] at hh
  exact Finset.notMem_empty _ hh

lemma empty_polygon_of_inner_empty (S : Finset Point) (h : inner S = ∅) :
    EmptyConvexPolygon S S := by
  refine ⟨Finset.Subset.refl S,?_,?_⟩
  · have hc := convexIndependent_hullVertices S
    rwa [inner_empty_hull_eq S h] at hc
  · intro x hx hn
    exact (hn hx).elim

lemma card_le_one_of_hull_card_le_one
    (S : Finset Point) (h : (hullVertices S).card ≤ 1) : S.card ≤ 1 := by
  rcases S.eq_empty_or_nonempty with hs | ⟨x,hx⟩
  · simp [hs]
  have hV : (hullVertices S).Nonempty := by
    by_contra hn
    have hv0 : hullVertices S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hxH : x ∈ convexHull ℝ ((hullVertices S : Finset Point) : Set Point) := by
      rw [convexHull_hullVertices]
      exact subset_convexHull ℝ _ hx
    simp [hv0] at hxH
  have hc : (hullVertices S).card = 1 := by
    have hp := Finset.card_pos.mpr hV
    omega
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hc
  apply Finset.card_le_one.mpr
  intro y hy z hz
  have hmem : ∀ t ∈ S, t = a := by
    intro t ht
    have hh : t ∈ convexHull ℝ ((hullVertices S : Finset Point) : Set Point) := by
      rw [convexHull_hullVertices]
      exact subset_convexHull ℝ _ ht
    simpa [ha] using hh
  exact (hmem y hy).trans (hmem z hz).symm

/-- With a single inner point, five outer points on a closed halfplane
through that point form a six-hole. The boundary outer point is included explicitly. -/
lemma single_inner_cap_le_four
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (p q : Point) (hI : inner P = {p}) (hq : q ∈ hullVertices P) :
    ((hullVertices P).filter (fun x => 0 ≤ orient p q x)).card ≤ 4 := by
  have hpI : p ∈ inner P := by simp [hI]
  have hpP := (Finset.mem_sdiff.mp hpI).1
  have hpq : p ≠ q := by
    intro hh
    exact (Finset.mem_sdiff.mp hpI).2 (by simpa only [hh] using hq)
  let C := (hullVertices P).filter (fun x => 0 ≤ orient p q x)
  have hqC : q ∈ C := by
    exact Finset.mem_filter.mpr ⟨hq,by rw [orient_refl_right]⟩
  by_contra hn
  have h5 : 5 ≤ C.card := by
    change ¬ C.card ≤ 4 at hn
    omega
  have h4 : 4 ≤ (C.erase q).card := by
    rw [Finset.card_erase_of_mem hqC]
    omega
  obtain ⟨T,hTC,hT4⟩ := Finset.exists_subset_card_eq h4
  let K := insert q T
  let W := insert p K
  have hTA : T ⊆ hullVertices P :=
    hTC.trans ((Finset.erase_subset _ _).trans (Finset.filter_subset _ _))
  have hqT : q ∉ T := fun h => (Finset.mem_erase.mp (hTC h)).1 rfl
  have hKA : K ⊆ hullVertices P := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hq
    · exact hTA hx
  have hpK : p ∉ K := fun h => (Finset.mem_sdiff.mp hpI).2 (hKA h)
  have hWP : W ⊆ P := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hpP
    · exact hullVertices_subset P (hKA hx)
  have hWconv : InConvexPosition W := by
    apply convex_position_outer_supported P W hWP
    intro x hx hxA
    have hxp : x = p := by
      rcases Finset.mem_insert.mp hx with hh | hh
      · exact hh
      · exact (hxA (hKA hh)).elim
    subst x
    refine ⟨q,by simp [W,K],p,by simp [W],hpq.symm,Or.inr rfl,?_⟩
    intro z hz hzq hzp
    have hzT : z ∈ T := by
      rcases Finset.mem_insert.mp hz with hh | hh
      · exact (hzp hh).elim
      · rcases Finset.mem_insert.mp hh with hh | hh
        · exact (hzq hh).elim
        · exact hh
    have hzC := (Finset.mem_erase.mp (hTC hzT)).2
    have hzside := (Finset.mem_filter.mp hzC).2
    have hne := hgp p hpP q (hullVertices_subset P hq)
      z (hullVertices_subset P (hTA hzT)) hpq hzp.symm hzq.symm
    have hpos : 0 < orient p q z := lt_of_le_of_ne hzside hne.symm
    rw [orient_reverse]
    exact neg_lt_zero.mpr hpos
  have hWempty : EmptyConvexPolygon P W := by
    refine ⟨hWP,hWconv,?_⟩
    intro x hxP hxW hxint
    by_cases hxA : x ∈ hullVertices P
    · exact hull_vertex_not_mem_hull
        (fun y hy => subset_convexHull ℝ _ (hWP hy)) hxA hxW
        (interior_subset hxint)
    · have hxI : x ∈ inner P := Finset.mem_sdiff.mpr ⟨hxP,hxA⟩
      have hxp : x = p := by simpa [hI] using hxI
      subst x
      exact hxW (by simp [W])
  apply hno
  refine ⟨W,?_,hWempty⟩
  simp [W,K,Finset.card_insert_of_notMem,hpK,hqT,hT4]

/-- Uniform small-inner-layer bound, with no nonemptiness convention hidden. -/
theorem outer_card_le_eight_of_second_small
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (hsmall : (hullVertices (inner P)).card ≤ 1) :
    (hullVertices P).card ≤ 8 := by
  have hI : (inner P).card ≤ 1 := card_le_one_of_hull_card_le_one (inner P) hsmall
  by_cases he : inner P = ∅
  · have hcard : P.card ≤ 5 := by
      by_contra hn
      apply hno
      exact hasEmptySix_of_large_empty (empty_polygon_of_inner_empty P he) (by omega)
    exact (Finset.card_le_card (hullVertices_subset P)).trans (by omega)
  · have hIpos : 0 < (inner P).card := Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr he)
    obtain ⟨p,hp⟩ := Finset.card_eq_one.mp (show (inner P).card = 1 by omega)
    rcases (hullVertices P).eq_empty_or_nonempty with hA | ⟨q,hq⟩
    · simp [hA]
    have hleft := single_inner_cap_le_four P hgp hno p q hp hq
    -- Reflect the plane by reversing the halfplane normal; the same finite
    -- gluing proof is applied through a negative-side variant below.
    have hright : ((hullVertices P).filter (fun x => orient p q x ≤ 0)).card ≤ 4 := by
      by_contra hn
      let C := (hullVertices P).filter (fun x => orient p q x ≤ 0)
      have hpI : p ∈ inner P := by simp [hp]
      have hpP := (Finset.mem_sdiff.mp hpI).1
      have hpq : p ≠ q := by
        intro hh
        exact (Finset.mem_sdiff.mp hpI).2 (by simpa only [hh] using hq)
      have hqC : q ∈ C := Finset.mem_filter.mpr ⟨hq,by rw [orient_refl_right]⟩
      have h4 : 4 ≤ (C.erase q).card := by
        rw [Finset.card_erase_of_mem hqC]
        change ¬C.card ≤ 4 at hn
        omega
      obtain ⟨T,hTC,hT4⟩ := Finset.exists_subset_card_eq h4
      let K := insert q T
      let W := insert p K
      have hTA : T ⊆ hullVertices P :=
        hTC.trans ((Finset.erase_subset _ _).trans (Finset.filter_subset _ _))
      have hqT : q ∉ T := fun h => (Finset.mem_erase.mp (hTC h)).1 rfl
      have hKA : K ⊆ hullVertices P := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hq
        · exact hTA hx
      have hpK : p ∉ K := fun h => (Finset.mem_sdiff.mp hpI).2 (hKA h)
      have hWP : W ⊆ P := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hpP
        · exact hullVertices_subset P (hKA hx)
      have hWconv : InConvexPosition W := by
        apply convex_position_outer_supported P W hWP
        intro x hx hxA
        have hxp : x = p := by
          rcases Finset.mem_insert.mp hx with hh | hh
          · exact hh
          · exact (hxA (hKA hh)).elim
        subst x
        refine ⟨p,by simp [W],q,by simp [W,K],hpq,Or.inl rfl,?_⟩
        intro z hz hzp hzq
        have hzT : z ∈ T := by
          rcases Finset.mem_insert.mp hz with hh | hh
          · exact (hzp hh).elim
          · rcases Finset.mem_insert.mp hh with hh | hh
            · exact (hzq hh).elim
            · exact hh
        have hzside := (Finset.mem_filter.mp (Finset.mem_erase.mp (hTC hzT)).2).2
        have hne := hgp p hpP q (hullVertices_subset P hq)
          z (hullVertices_subset P (hTA hzT)) hpq hzp.symm hzq.symm
        exact lt_of_le_of_ne hzside hne
      have hWempty : EmptyConvexPolygon P W := by
        refine ⟨hWP,hWconv,?_⟩
        intro x hxP hxW hxint
        by_cases hxA : x ∈ hullVertices P
        · exact hull_vertex_not_mem_hull
            (fun y hy => subset_convexHull ℝ _ (hWP hy)) hxA hxW
            (interior_subset hxint)
        · have hxI : x ∈ inner P := Finset.mem_sdiff.mpr ⟨hxP,hxA⟩
          have hxp : x = p := by simpa [hp] using hxI
          subst x
          exact hxW (by simp [W])
      apply hno
      refine ⟨W,?_,hWempty⟩
      simp [W,K,Finset.card_insert_of_notMem,hpK,hqT,hT4]
    have hcov : hullVertices P ⊆
        ((hullVertices P).filter (fun x => 0 ≤ orient p q x)) ∪
        ((hullVertices P).filter (fun x => orient p q x ≤ 0)) := by
      intro x hx
      rcases le_total 0 (orient p q x) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx,h⟩)
    have hc := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
    omega

/-- A full, unconditional three-layer finish. It does not assume a fan cover,
a cyclic ordering, a matching, or the four-layer theorem. -/
theorem hasEmptySix_of_three_layers
    (P : Finset Point) (hgp : GeneralPosition P)
    (houter : 25 ≤ (hullVertices P).card)
    (hthree : inner (inner (inner P)) = ∅) : HasEmptySix P := by
  by_contra hno
  let S := inner P
  let T := inner S
  have hSgp : GeneralPosition S := gp_subset hgp Finset.sdiff_subset
  have hTgp : GeneralPosition T := gp_subset hSgp Finset.sdiff_subset
  have hSno : ¬HasEmptySix S := fun h => hno (hasEmptySix_inner_transfer h)
  have hTno : ¬HasEmptySix T := fun h => hSno (hasEmptySix_inner_transfer h)
  have hTinner : inner T = ∅ := hthree
  have hTcard : T.card ≤ 5 := by
    by_contra hn
    apply hTno
    exact hasEmptySix_of_large_empty (empty_polygon_of_inner_empty T hTinner) (by omega)
  have hthird : (hullVertices T).card ≤ 5 :=
    (Finset.card_le_card (hullVertices_subset T)).trans hTcard
  have hScard : (hullVertices S).card ≤ 12 := by
    by_cases h2 : 2 ≤ (hullVertices T).card
    · have hh := outer_card_le_twice_second_add_two S hSgp hSno h2
      change (hullVertices S).card ≤ 2 * (hullVertices T).card + 2 at hh
      omega
    · have hh := outer_card_le_eight_of_second_small S hSgp hSno
          (show (hullVertices T).card ≤ 1 by omega)
      omega
  by_cases hTne : T.Nonempty
  · have hh := outer_card_le_twice_second_of_third_nonempty P hgp hno hTne
    change (hullVertices P).card ≤ 2 * (hullVertices S).card at hh
    omega
  · have hTe : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
    have hSI : inner S = ∅ := hTe
    have hScard' : S.card ≤ 5 := by
      by_contra hn
      apply hSno
      exact hasEmptySix_of_large_empty (empty_polygon_of_inner_empty S hSI) (by omega)
    have hsecond : (hullVertices S).card ≤ 5 :=
      (Finset.card_le_card (hullVertices_subset S)).trans hScard'
    by_cases h2 : 2 ≤ (hullVertices S).card
    · have hh := outer_card_le_twice_second_add_two P hgp hno h2
      change (hullVertices P).card ≤ 2 * (hullVertices S).card + 2 at hh
      omega
    · have hh := outer_card_le_eight_of_second_small P hgp hno
        (show (hullVertices S).card ≤ 1 by omega)
      omega

/-! ## Local-to-global matching: actual predecessor/successor and annular safety -/

lemma mem_triangle_of_weights (a b c : Point) (s t r : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hr : 0 ≤ r) (hSum : s+t+r=1) :
    s • a + t • b + r • c ∈ convexHull ℝ ({a,b,c} : Set Point) := by
  let w : Fin 3 → ℝ := ![s,t,r]
  let z : Fin 3 → Point := ![a,b,c]
  apply mem_convexHull_of_exists_fintype w z
  · intro i
    fin_cases i <;> simp [w,hs,ht,hr]
  · simpa [w,Fin.sum_univ_succ,add_assoc] using hSum
  · intro i
    fin_cases i <;> simp [z]
  · simp [w,z,Fin.sum_univ_succ,add_assoc]

lemma corner_affine (v u w y : Point) (hD : orient v u w ≠ 0) :
    y = (1 - orient v y w / orient v u w - orient v u y / orient v u w) • v +
      (orient v y w / orient v u w) • u + (orient v u y / orient v u w) • w := by
  ext <;>
    simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;>
    field_simp [hD] <;> unfold orient <;> ring

/-- The two boundary neighbors are different when there are at least three vertices. -/
lemma boundary_neighbors_ne
    (Q : Finset Point) (hgp : GeneralPosition Q) (h3 : 3 ≤ Q.card)
    (u v w : Point) (huv : BoundaryEdge Q u v) (hvw : BoundaryEdge Q v w) : u ≠ w := by
  intro he
  subst w
  have hsub : Q ⊆ {u,v} := by
    intro x hx
    by_cases hxu : x = u
    · simp [hxu]
    by_cases hxv : x = v
    · simp [hxv]
    have h1 := huv.2.2.2 x hx
    have h2 := hvw.2.2.2 x hx
    rw [orient_reverse] at h2
    have hn := hgp u huv.1 v huv.2.1 x hx huv.2.2.1 (Ne.symm hxu) (Ne.symm hxv)
    exact (hn (by linarith)).elim
  have hh := Finset.card_le_card hsub
  have hc : ({u,v} : Finset Point).card ≤ 2 := by
    calc
      ({u,v} : Finset Point).card ≤ ({v} : Finset Point).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp
  omega

/-- A halfplane cannot isolate a hull vertex from both its neighbors and still
contain another hull vertex. This is proved by actual barycentric coordinates. -/
theorem cap_isolated_by_neighbors
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (u v w a b : Point) (huv : BoundaryEdge Q u v) (hvw : BoundaryEdge Q v w)
    (huw : u ≠ w) (hV : 0 < orient a b v)
    (hU : orient a b u < 0) (hW : orient a b w < 0) :
    ∀ y ∈ Q, y ≠ v → orient a b y < 0 := by
  intro y hy hyv
  by_cases hyu : y = u
  · simpa [hyu] using hU
  by_cases hyw : y = w
  · simpa [hyw] using hW
  have hwside := huv.strict hgp hvw.2.1 huw.symm hvw.2.2.1.symm
  have hD : 0 < orient v u w := by
    rw [orient_reverse]
    linarith
  let B := orient v y w / orient v u w
  let C := orient v u y / orient v u w
  have hB : 0 ≤ B := by
    apply div_nonneg _ hD.le
    have hh := hvw.2.2.2 y hy
    have he : orient v y w = -orient v w y := by unfold orient; ring
    rw [he]
    linarith
  have hC : 0 ≤ C := by
    apply div_nonneg _ hD.le
    have hh := huv.2.2.2 y hy
    rw [orient_reverse]
    linarith
  have hyrep : y = (1-B-C) • v + B • u + C • w :=
    corner_affine v u w y (ne_of_gt hD)
  have hlarge : 1 < B+C := by
    by_contra hn
    have ha : 0 ≤ 1-B-C := by linarith
    have hyH : y ∈ convexHull ℝ ({v,u,w} : Set Point) := by
      rw [hyrep]
      exact mem_triangle_of_weights v u w (1-B-C) B C ha hB hC (by ring)
    have hCI := (convexIndependent_set_iff_notMem_convexHull_sdiff.mp hQ) y hy
    apply hCI
    apply convexHull_mono _ hyH
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with hz | hz | hz <;> subst z
    · exact ⟨huv.2.1,(Ne.symm hyv)⟩
    · exact ⟨huv.1,(Ne.symm hyu)⟩
    · exact ⟨hvw.2.1,(Ne.symm hyw)⟩
  have hA : 1-B-C < 0 := by linarith
  rw [hyrep,orient_affine_comb a b v u w (1-B-C) B C (by ring)]
  have h1 := mul_neg_of_neg_of_pos hA hV
  have h2 := mul_nonpos_of_nonneg_of_nonpos hB hU.le
  have h3 := mul_nonpos_of_nonneg_of_nonpos hC hW.le
  linarith

/-- From measured cap cardinality, construct a true adjacent matching choice.
The conclusion is not an assumed cyclic-order or matching axiom. -/
theorem boundary_neighbor_in_cap
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (h3 : 3 ≤ Q.card) (a b v : Point) (hv : v ∈ Q)
    (hvside : 0 < orient a b v)
    (hgen : ∀ y ∈ Q, orient a b y ≠ 0)
    (hcap : 2 ≤ (Q.filter (fun y => 0 < orient a b y)).card) :
    ∃ u w : Point, BoundaryEdge Q u v ∧ BoundaryEdge Q v w ∧
      (0 < orient a b u ∨ 0 < orient a b w) := by
  obtain ⟨u,huv⟩ := exists_boundaryEdge_to Q hQ hgp (by omega) v hv
  obtain ⟨w,hvw⟩ := exists_boundaryEdge_from Q hQ hgp (by omega) v hv
  refine ⟨u,w,huv,hvw,?_⟩
  by_contra hn
  push_neg at hn
  have huNeg : orient a b u < 0 := lt_of_le_of_ne hn.1 (hgen u huv.1)
  have hwNeg : orient a b w < 0 := lt_of_le_of_ne hn.2 (hgen w hvw.2.1)
  have hIso := cap_isolated_by_neighbors Q hQ hgp u v w a b huv hvw
    (boundary_neighbors_ne Q hgp h3 u v w huv hvw) hvside huNeg hwNeg
  have hs : Q.filter (fun y => 0 < orient a b y) ⊆ {v} := by
    intro y hy
    obtain ⟨hy,hpos⟩ := Finset.mem_filter.mp hy
    by_contra hny
    have hyv : y ≠ v := by simpa using hny
    have hh := hIso y hy hyv
    linarith
  have hc := Finset.card_le_card hs
  simp only [Finset.card_singleton] at hc
  omega

/-- The four orientation signs for two *actual* adjacent-layer edges whose
outer endpoints are on the outward side of the inner edge. -/
theorem boundary_match_four_signs
    (P : Finset Point) (hgp : GeneralPosition P)
    (u v c d : Point)
    (huv : BoundaryEdge (hullVertices (inner P)) u v)
    (hcd : BoundaryEdge (hullVertices (inner (inner P))) c d)
    (hcu : 0 < orient c d u) (hcv : 0 < orient c d v) :
    0 < orient u c d ∧ 0 < orient u c v ∧
    0 < orient u d v ∧ 0 < orient c d v := by
  have huI := hullVertices_subset (inner P) huv.1
  have hvI := hullVertices_subset (inner P) huv.2.1
  have hcII := hullVertices_subset (inner (inner P)) hcd.1
  have hdII := hullVertices_subset (inner (inner P)) hcd.2.1
  have hcI := (Finset.mem_sdiff.mp hcII).1
  have hdI := (Finset.mem_sdiff.mp hdII).1
  have huc : u ≠ c := by
    intro hh
    exact (Finset.mem_sdiff.mp hcII).2 (by simpa only [hh] using huv.1)
  have hvc : v ≠ c := by
    intro hh
    exact (Finset.mem_sdiff.mp hcII).2 (by simpa only [hh] using huv.2.1)
  have hud : u ≠ d := by
    intro hh
    exact (Finset.mem_sdiff.mp hdII).2 (by simpa only [hh] using huv.1)
  have hvd : v ≠ d := by
    intro hh
    exact (Finset.mem_sdiff.mp hdII).2 (by simpa only [hh] using huv.2.1)
  have hc0 := hgp u (Finset.mem_sdiff.mp huI).1 v (Finset.mem_sdiff.mp hvI).1
    c (Finset.mem_sdiff.mp hcI).1 huv.2.2.1 huc hvc
  have hd0 := hgp u (Finset.mem_sdiff.mp huI).1 v (Finset.mem_sdiff.mp hvI).1
    d (Finset.mem_sdiff.mp hdI).1 huv.2.2.1 hud hvd
  have hcneg := lt_of_le_of_ne (boundaryEdge_hull_support huv c hcI) hc0
  have hdneg := lt_of_le_of_ne (boundaryEdge_hull_support huv d hdI) hd0
  have h1 : orient u c d = orient c d u := by unfold orient; ring
  have h2 : orient u c v = -orient u v c := by unfold orient; ring
  have h3 : orient u d v = -orient u v d := by unfold orient; ring
  exact ⟨by rwa [h1],by rw [h2]; linarith,by rw [h3]; linarith,hcv⟩

/-- The annular-interior condition is proved, not passed in as a premise. -/
theorem boundary_match_annular
    (P : Finset Point) (u v c d : Point)
    (hcd : BoundaryEdge (hullVertices (inner (inner P))) c d)
    (hcu : 0 < orient c d u) (hcv : 0 < orient c d v) :
    Disjoint (interior (convexHull ℝ ({u,c,d,v} : Set Point)))
      (convexHull ℝ ((hullVertices (inner (inner P)) : Finset Point) : Set Point)) := by
  apply Set.disjoint_left.mpr
  intro z hzInt hzH
  have hzSide := orient_nonpos_on_hull hcd.2.2.2 hzH
  have hside : ∀ x ∈ ({u,c,d,v} : Finset Point), 0 ≤ orient c d x := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx <;> subst x
    · exact hcu.le
    · simp only [orient_refl_left,orient_refl_right,le_refl]
    · simp only [orient_refl_left,orient_refl_right,le_refl]
    · exact hcv.le
  apply not_mem_interior_convexHull_of_halfplane ({u,c,d,v} : Finset Point)
    c d z hcd.2.2.1 hside hzSide
  simpa only [Finset.coe_insert,Finset.coe_singleton] using hzInt

/-- Complete geometric matching endpoint: the quadrilateral is convex and
empty in the original ambient set, from supporting edges and two strict signs. -/
theorem boundary_match_empty_quad
    (P : Finset Point) (hgp : GeneralPosition P)
    (u v c d : Point)
    (huv : BoundaryEdge (hullVertices (inner P)) u v)
    (hcd : BoundaryEdge (hullVertices (inner (inner P))) c d)
    (hcu : 0 < orient c d u) (hcv : 0 < orient c d v) :
    EmptyConvexPolygon P ({u,c,d,v} : Finset Point) := by
  have huI := hullVertices_subset (inner P) huv.1
  have hvI := hullVertices_subset (inner P) huv.2.1
  have hcI := (Finset.mem_sdiff.mp
    (hullVertices_subset (inner (inner P)) hcd.1)).1
  have hdI := (Finset.mem_sdiff.mp
    (hullVertices_subset (inner (inner P)) hcd.2.1)).1
  have hsub : ({u,c,d,v} : Finset Point) ⊆ inner P := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx <;> subst x <;> assumption
  obtain ⟨h1,h2,h3,h4⟩ := boundary_match_four_signs P hgp u v c d huv hcd hcu hcv
  have hconv := quad_convex_of_four_signs P hgp u c d v
    (Finset.mem_sdiff.mp huI).1 (Finset.mem_sdiff.mp hcI).1
    (Finset.mem_sdiff.mp hdI).1 (Finset.mem_sdiff.mp hvI).1 h1 h2 h3 h4
  apply empty_polygon_of_annular_interior P {u,c,d,v} hsub hconv
  simpa only [Finset.coe_insert,Finset.coe_singleton] using
    boundary_match_annular P u v c d hcd hcu hcv

def matchChannel (P : Finset Point) (u v c d : Point) : Finset Point :=
  (hullVertices P).filter (fun x =>
    0 < orient u c x ∧ 0 < orient c d x ∧ 0 < orient d v x)

/-- Actual matching cells have capacity at most one in a six-hole-free set.
Neither convexity, annular avoidance, nor emptiness is left as an input. -/
theorem boundary_match_channel_le_one
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (u v c d : Point)
    (huv : BoundaryEdge (hullVertices (inner P)) u v)
    (hcd : BoundaryEdge (hullVertices (inner (inner P))) c d)
    (hcu : 0 < orient c d u) (hcv : 0 < orient c d v) :
    (matchChannel P u v c d).card ≤ 1 := by
  by_contra hn
  have hK2 : 2 ≤ (matchChannel P u v c d).card := by omega
  have huI := hullVertices_subset (inner P) huv.1
  have hvI := hullVertices_subset (inner P) huv.2.1
  have hcI := (Finset.mem_sdiff.mp
    (hullVertices_subset (inner (inner P)) hcd.1)).1
  have hdI := (Finset.mem_sdiff.mp
    (hullVertices_subset (inner (inner P)) hcd.2.1)).1
  obtain ⟨h1,h2,h3,h4⟩ := boundary_match_four_signs P hgp u v c d huv hcd hcu hcv
  apply hno
  apply hasEmptySix_of_quad_channel P (matchChannel P u v c d) hgp u c d v
    huI hcI hdI hvI h1 h2 h3 h4
    (boundary_match_empty_quad P hgp u v c d huv hcd hcu hcv)
    (boundaryEdge_hull_support huv) (Finset.filter_subset _ _) _ hK2
  intro x hx
  exact (Finset.mem_filter.mp hx).2

/-- In Theorem 4's setup the actual radial sectors contain at most two vertices
of layer two, unless there is an empty hexagon. This discharges Case II.C. -/
theorem third_layer_sector_card_le_two
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (e : Point × Point)
    (he : BoundaryEdge (hullVertices (inner (inner P))) e.1 e.2) :
    (outerFan (inner P) o e).card ≤ 2 := by
  have hSgp := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hSno : ¬HasEmptySix (inner P) := fun hh => hno (hasEmptySix_inner_transfer hh)
  apply outerFan_card_le_two (inner P) hSgp hSno o
    (Finset.mem_sdiff.mp ho).1 e he
  · intro hh
    exact (Finset.mem_sdiff.mp ho).2 (by simpa only [hh] using he.1)
  · intro hh
    exact (Finset.mem_sdiff.mp ho).2 (by simpa only [hh] using he.2.1)

/-- Normalization plus the complete three-layer branch. The four-layer branch
is deliberately not packaged as an unproved final theorem. -/
theorem convex25_three_layers
    (P : Finset Point) (hgp : GeneralPosition P)
    (S : Finset Point) (hSP : S ⊆ P) (hSconv : InConvexPosition S) (hS25 : S.card = 25)
    (hthree : inner (inner (inner (hullCut P S))) = ∅) : HasEmptySix P := by
  have hgp' := gp_subset hgp (hullCut_subset P S)
  have hH := hullVertices_hullCut hSP hSconv
  have h25 : 25 ≤ (hullVertices (hullCut P S)).card := by rw [hH,hS25]
  obtain ⟨V,hV6,hV⟩ := hasEmptySix_of_three_layers (hullCut P S) hgp' h25 hthree
  exact ⟨V,hV6,empty_polygon_hullCut_transfer hV⟩

/-! ## The actual finite sector assignment used by Nicolas's Cases I and II -/

lemma hullVertices_nonempty_of_nonempty (S : Finset Point) (hS : S.Nonempty) :
    (hullVertices S).Nonempty := by
  obtain ⟨x,hx⟩ := hS
  by_contra hn
  have he : hullVertices S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hxH : x ∈ convexHull ℝ ((hullVertices S : Finset Point) : Set Point) := by
    rw [convexHull_hullVertices]
    exact subset_convexHull ℝ _ hx
  simp [he] at hxH

lemma three_le_hull_of_inner_nonempty
    (S : Finset Point) (hgp : GeneralPosition S) (hI : (inner S).Nonempty) :
    3 ≤ (hullVertices S).card := by
  have hpos : 0 < (inner S).card := Finset.card_pos.mpr hI
  have hS : S.Nonempty := hI.mono Finset.sdiff_subset
  have hVpos := Finset.card_pos.mpr (hullVertices_nonempty_of_nonempty S hS)
  have hsum : (inner S).card + (hullVertices S).card = S.card :=
    Finset.card_sdiff_add_card_eq_card (hullVertices_subset S)
  by_contra hn
  have hSc : S.card ≤ 2 := by
    by_contra hnc
    have hh := three_le_card_hullVertices S hgp (by omega)
    omega
  have hVc : (hullVertices S).card ≤ 1 := by omega
  have hh := card_le_one_of_hull_card_le_one S hVc
  omega

/-- Sector edges are chosen from the proved ray-fan cover of the actual layers. -/
noncomputable def sectorEdge
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (r : ((hullVertices (inner P) : Finset Point) : Set Point)) :
    ((boundaryEdges (hullVertices (inner (inner P))) : Finset (Point × Point)) : Set (Point × Point)) :=
  let hcov := outer_fan_cover (inner P) (gp_subset hgp Finset.sdiff_subset) o ho r r.property
  ⟨Classical.choose hcov, (Classical.choose_spec hcov).1⟩

lemma sectorEdge_inFan
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (r : ((hullVertices (inner P) : Finset Point) : Set Point)) :
    InFan o (sectorEdge P hgp o ho r).val.1 (sectorEdge P hgp o ho r).val.2 r := by
  let hcov := outer_fan_cover (inner P) (gp_subset hgp Finset.sdiff_subset) o ho r r.property
  have hh := (Classical.choose_spec hcov).2
  exact (Finset.mem_filter.mp hh).2

lemma sectorEdge_unique
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (r : ((hullVertices (inner P) : Finset Point) : Set Point))
    (e : Point × Point)
    (he : BoundaryEdge (hullVertices (inner (inner P))) e.1 e.2)
    (hfan : InFan o e.1 e.2 r) :
    (sectorEdge P hgp o ho r).val = e := by
  let z := sectorEdge P hgp o ho r
  have hz := mem_boundaryEdges.mp z.property
  have hfz := sectorEdge_inFan P hgp o ho r
  obtain ⟨ha,hb⟩ := (inFan_iff_raySides o z.val.1 z.val.2 r).mp hfz
  obtain ⟨hc,hd⟩ := (inFan_iff_raySides o e.1 e.2 r).mp hfan
  have hgpQ : GeneralPosition (hullVertices (inner (inner P))) :=
    gp_subset hgp ((hullVertices_subset (inner (inner P))).trans
      (Finset.sdiff_subset.trans Finset.sdiff_subset))
  obtain ⟨h1,h2⟩ := boundary_fan_unique (hullVertices (inner (inner P))) hgpQ
    o r z.val.1 z.val.2 e.1 e.2 hz he ha hb hc hd
  exact Prod.ext h1 h2

/-- Every assigned inner edge really faces its assigned layer-two vertex. -/
lemma sectorEdge_outward
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (r : ((hullVertices (inner P) : Finset Point) : Set Point)) :
    0 < orient (sectorEdge P hgp o ho r).val.1
      (sectorEdge P hgp o ho r).val.2 r := by
  let e := sectorEdge P hgp o ho r
  have he := mem_boundaryEdges.mp e.property
  obtain ⟨ha,hb⟩ := (inFan_iff_raySides o e.val.1 e.val.2 r).mp
    (sectorEdge_inFan P hgp o ho r)
  have hoH := inner_hull_point (inner P) (Finset.mem_sdiff.mp ho).1
  have hrH : (r : Point) ∉ convexHull ℝ
      ((hullVertices (inner (inner P)) : Finset Point) : Set Point) := by
    rw [convexHull_hullVertices]
    exact outer_not_mem_inner_hull (inner P) r.property
  exact rayPair_outward (hullVertices (inner (inner P))) o r e.val.1 e.val.2
    hoH hrH he.1 he.2.1 ha hb

/-- The map's fibers, not only its geometric containing regions, have size at most two. -/
theorem sectorEdge_fiber_card_le_two
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (e : ((boundaryEdges (hullVertices (inner (inner P))) : Finset (Point × Point)) : Set (Point × Point))) :
    ((Finset.univ : Finset ((hullVertices (inner P) : Finset Point) : Set Point)).filter
      (fun r => sectorEdge P hgp o ho r = e)).card ≤ 2 := by
  have hsubcount :
      ((Finset.univ : Finset ((hullVertices (inner P) : Finset Point) : Set Point)).filter
        (fun r => sectorEdge P hgp o ho r = e)).card ≤
      (outerFan (inner P) o e.val).card := by
    apply Finset.card_le_card_of_injOn
      (fun r : ((hullVertices (inner P) : Finset Point) : Set Point) => (r : Point))
    · intro r hr
      have hre := (Finset.mem_filter.mp hr).2
      have hf := sectorEdge_inFan P hgp o ho r
      rw [hre] at hf
      exact Finset.mem_filter.mpr ⟨r.property,hf⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
  exact hsubcount.trans (third_layer_sector_card_le_two P hgp hno o ho e.val
    (mem_boundaryEdges.mp e.property))

/-- Boundary-vertex encoding of Nicolas's sector index, without postulating an
ordered polygon enumeration. Its successor is supplied by boundaryPerm. -/
noncomputable def sectorVertex
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (r : ((hullVertices (inner P) : Finset Point) : Set Point)) :
    ((hullVertices (inner (inner P)) : Finset Point) : Set Point) :=
  ⟨(sectorEdge P hgp o ho r).val.1,
    (mem_boundaryEdges.mp (sectorEdge P hgp o ho r).property).1⟩

/-- Both actual layers carry single boundary cycles; sector membership,
uniqueness, and capacity have already been discharged above. -/
theorem actual_layer_boundary_cycles
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) :
    ∃ f : Equiv.Perm ((hullVertices (inner P) : Finset Point) : Set Point),
    ∃ g : Equiv.Perm ((hullVertices (inner (inner P)) : Finset Point) : Set Point),
      (∀ r : ((hullVertices (inner P) : Finset Point) : Set Point),
        BoundaryEdge (hullVertices (inner P)) r (f r)) ∧
      (∀ q : ((hullVertices (inner (inner P)) : Finset Point) : Set Point),
        BoundaryEdge (hullVertices (inner (inner P))) q (g q)) ∧
      (∀ r s, ∃ j : ℕ, j ≤ (hullVertices (inner P)).card ∧ orbit f r j = s) ∧
      (∀ q t, ∃ j : ℕ, j ≤ (hullVertices (inner (inner P))).card ∧ orbit g q j = t) := by
  let R := hullVertices (inner P)
  let Q := hullVertices (inner (inner P))
  have hIgp : GeneralPosition (inner P) := gp_subset hgp Finset.sdiff_subset
  have hIIgp : GeneralPosition (inner (inner P)) := gp_subset hIgp Finset.sdiff_subset
  have hRgp : GeneralPosition R := gp_subset hIgp (hullVertices_subset _)
  have hQgp : GeneralPosition Q := gp_subset hIIgp (hullVertices_subset _)
  have hRc : InConvexPosition R := convexIndependent_hullVertices _
  have hQc : InConvexPosition Q := convexIndependent_hullVertices _
  have hQ3 : 3 ≤ Q.card :=
    three_le_hull_of_inner_nonempty (inner (inner P)) hIIgp ⟨o,ho⟩
  have hR3 : 3 ≤ R.card := three_le_hull_of_inner_nonempty (inner P) hIgp
    ⟨o,(Finset.mem_sdiff.mp ho).1⟩
  let f := boundaryPerm R hRc hRgp (by omega : 2 ≤ R.card)
  let g := boundaryPerm Q hQc hQgp (by omega : 2 ≤ Q.card)
  refine ⟨f,g,?_,?_,?_,?_⟩
  · intro r; exact boundaryPerm_edge R hRc hRgp _ r
  · intro q; exact boundaryPerm_edge Q hQc hQgp _ q
  · intro r s; exact boundaryPerm_reaches R hRc hRgp _ r s
  · intro q t; exact boundaryPerm_reaches Q hQc hQgp _ q t

end JSP198.Nicolas

#print axioms JSP198.Nicolas.boundaryPerm_reaches
#print axioms JSP198.Nicolas.exists_boundary_fan
#print axioms JSP198.Nicolas.boundary_fan_unique
#print axioms JSP198.Nicolas.convex25_three_layers
#print axioms JSP198.Nicolas.sectorEdge_fiber_card_le_two
#print axioms JSP198.Nicolas.actual_layer_boundary_cycles
