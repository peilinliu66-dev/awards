/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/CyclicLabel.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Certificate
import EmptyPentagon.TriangleInterior

noncomputable section
namespace Horton

/-- A strictly positive orientation forces the three points to be pairwise distinct. -/
theorem ne_of_orient_pos (a b c : Point) (h : 0 < orient a b c) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> unfold orient at h <;> nlinarith

/-- Transitivity of the angular order around a base point `o` for points weakly above `o`
(the middle point `r` being lexicographically above `o`). -/
theorem orient_pos_trans (o q r s : Point) (hq : o.2 ≤ q.2) (hs : o.2 ≤ s.2)
    (hr : o.2 < r.2 ∨ (o.2 = r.2 ∧ o.1 < r.1)) (hqs : orient o q s ≠ 0)
    (h1 : 0 < orient o q r) (h2 : 0 < orient o r s) : 0 < orient o q s := by
  have key : orient o q s * (r.2 - o.2) =
      orient o q r * (s.2 - o.2) + orient o r s * (q.2 - o.2) := by
    unfold orient
    ring
  rcases hr with hr | ⟨hr2, hr1⟩
  · have hnn : 0 ≤ orient o q s := by
      by_contra hneg
      rw [not_le] at hneg
      nlinarith [mul_neg_of_neg_of_pos hneg (sub_pos.mpr hr), mul_nonneg h1.le (sub_nonneg.mpr hs),
        mul_nonneg h2.le (sub_nonneg.mpr hq)]
    exact lt_of_le_of_ne hnn (Ne.symm hqs)
  · exfalso
    have e : orient o q r = -((q.2 - o.2) * (r.1 - o.1)) := by
      unfold orient
      rw [hr2]
      ring
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_pos.mpr hr1).le]

/-- In a convex-independent set in general position, three points seen in counterclockwise
angular order `b, c, d` from a fourth member `a` are themselves counterclockwise. -/
theorem orient_pos_of_angular_order (V : Finset Point) (hgp : GeneralPosition V)
    (hV : ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point))) (a b c d : Point)
    (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hd : d ∈ V)
    (habc : 0 < orient a b c) (hacd : 0 < orient a c d) (habd : 0 < orient a b d) :
    0 < orient b c d := by
  obtain ⟨-, hac, hbc⟩ := ne_of_orient_pos a b c habc
  obtain ⟨-, -, hcd⟩ := ne_of_orient_pos a c d hacd
  obtain ⟨-, -, hbd⟩ := ne_of_orient_pos a b d habd
  rcases lt_trichotomy (orient b c d) 0 with hneg | hzero | hpos
  · exfalso
    have e1 : orient b d c = -orient b c d := by
      unfold orient
      ring
    have e2 : orient d a c = orient a c d := by
      unfold orient
      ring
    have hmem := mem_interior_triangle_of_orient_pos a b d c habd habc (by linarith) (by linarith)
    exact not_convexIndependent_of_mem_convexHull_triple V a b d c ha hb hd hc hac.symm hbc.symm
      hcd (interior_subset hmem) hV
  · exact absurd hzero (hgp b hb c hc d hd hbc hbd hcd)
  · exact hpos

/-- A convex-independent 5-set in general position can be labelled counterclockwise: every
directed edge `P i → P (i+1)` sees the other three vertices strictly on its left. -/
theorem exists_cyclic_labeling (V : Finset Point) (hcard : V.card = 5) (hgp : GeneralPosition V)
    (hV : ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point))) :
    ∃ P : Fin 5 → Point, Function.Injective P ∧ (∀ i, P i ∈ V) ∧
      ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (P i) (P (i + 1)) (P j) := by
  classical
  have hne : V.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨P0, hP0V, hmin⟩ :=
    Finset.exists_min_image V (fun p : Point => toLex (p.2, p.1)) hne
  set W := V.erase P0 with hW
  have hWcard : W.card = 4 := by
    rw [hW, Finset.card_erase_of_mem hP0V, hcard]
  have hWmem : ∀ q ∈ W, q ∈ V ∧ q ≠ P0 :=
    fun q hq => ⟨Finset.mem_of_mem_erase hq, Finset.ne_of_mem_erase hq⟩
  have hAb : ∀ q ∈ W, P0.2 < q.2 ∨ (P0.2 = q.2 ∧ P0.1 < q.1) := by
    intro q hq
    have h := hmin q (hWmem q hq).1
    rw [Prod.Lex.toLex_le_toLex] at h
    rcases h with h | ⟨h2, h1⟩
    · exact Or.inl h
    · refine Or.inr ⟨h2, lt_of_le_of_ne h1 ?_⟩
      intro h1'
      exact (hWmem q hq).2 (Prod.ext h1'.symm h2.symm)
  have hAb' : ∀ q ∈ W, P0.2 ≤ q.2 := by
    intro q hq
    rcases hAb q hq with h | ⟨h, -⟩ <;> linarith
  have hnz : ∀ q ∈ W, ∀ r ∈ W, q ≠ r → orient P0 q r ≠ 0 := fun q hq r hr hqr =>
    hgp P0 hP0V q (hWmem q hq).1 r (hWmem r hr).1 (hWmem q hq).2.symm (hWmem r hr).2.symm hqr
  have hswap : ∀ q r : Point, orient P0 r q = -orient P0 q r := by
    intro q r
    unfold orient
    ring
  have htr : ∀ q ∈ W, ∀ r ∈ W, ∀ s ∈ W,
      0 < orient P0 q r → 0 < orient P0 r s → 0 < orient P0 q s := by
    intro q hq r hr s hs h1 h2
    have hqs : q ≠ s := by
      rintro rfl
      linarith [hswap q r]
    exact orient_pos_trans P0 q r s (hAb' q hq) (hAb' s hs) (hAb r hr) (hnz q hq s hs hqs) h1 h2
  let rank : Point → ℕ := fun q => (W.filter (fun r => 0 < orient P0 r q)).card
  have hrank_lt : ∀ q ∈ W, ∀ r ∈ W, 0 < orient P0 q r → rank q < rank r := by
    intro q hq r hr h
    apply Finset.card_lt_card
    have hsub : W.filter (fun x => 0 < orient P0 x q) ⊆
        W.filter (fun x => 0 < orient P0 x r) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, htr x hx.1 q hq r hr hx.2 h⟩
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨q, Finset.mem_filter.mpr ⟨hq, h⟩, fun hmem => ?_⟩
    have := (Finset.mem_filter.mp hmem).2
    linarith [hswap q q]
  have hrank_lt4 : ∀ q ∈ W, rank q < 4 := by
    intro q hq
    have hsub : W.filter (fun x => 0 < orient P0 x q) ⊆ W.erase q := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_erase]
      refine ⟨?_, hx.1⟩
      rintro rfl
      linarith [hx.2, hswap x x]
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hq, hWcard] at this
    show (W.filter (fun x => 0 < orient P0 x q)).card < 4
    omega
  have hord : ∀ q ∈ W, ∀ r ∈ W, rank q < rank r → 0 < orient P0 q r := by
    intro q hq r hr h
    have hqr : q ≠ r := by
      rintro rfl
      exact lt_irrefl _ h
    rcases lt_or_gt_of_ne (hnz q hq r hr hqr) with hneg | hpos
    · have := hrank_lt r hr q hq (by linarith [hswap q r])
      omega
    · exact hpos
  have hinj : Set.InjOn rank W := by
    intro q hq r hr hqr
    by_contra hne
    rcases lt_or_gt_of_ne (hnz q hq r hr hne) with hneg | hpos
    · have := hrank_lt r hr q hq (by linarith [hswap q r])
      omega
    · have := hrank_lt q hq r hr hpos
      omega
  have hsurj : Set.SurjOn rank W (Finset.range 4) :=
    Finset.surjOn_of_injOn_of_card_le rank
      (fun q hq => Finset.mem_coe.mpr (Finset.mem_range.mpr (hrank_lt4 q hq))) hinj
      (by rw [hWcard, Finset.card_range])
  obtain ⟨q1, hq1, hr1⟩ :=
    hsurj (Finset.mem_coe.mpr (Finset.mem_range.mpr (by norm_num : 0 < 4)))
  obtain ⟨q2, hq2, hr2⟩ :=
    hsurj (Finset.mem_coe.mpr (Finset.mem_range.mpr (by norm_num : 1 < 4)))
  obtain ⟨q3, hq3, hr3⟩ :=
    hsurj (Finset.mem_coe.mpr (Finset.mem_range.mpr (by norm_num : 2 < 4)))
  obtain ⟨q4, hq4, hr4⟩ :=
    hsurj (Finset.mem_coe.mpr (Finset.mem_range.mpr (by norm_num : 3 < 4)))
  have hq1W : q1 ∈ W := hq1
  have hq2W : q2 ∈ W := hq2
  have hq3W : q3 ∈ W := hq3
  have hq4W : q4 ∈ W := hq4
  have o12 : 0 < orient P0 q1 q2 := hord q1 hq1W q2 hq2W (by omega)
  have o13 : 0 < orient P0 q1 q3 := hord q1 hq1W q3 hq3W (by omega)
  have o14 : 0 < orient P0 q1 q4 := hord q1 hq1W q4 hq4W (by omega)
  have o23 : 0 < orient P0 q2 q3 := hord q2 hq2W q3 hq3W (by omega)
  have o24 : 0 < orient P0 q2 q4 := hord q2 hq2W q4 hq4W (by omega)
  have o34 : 0 < orient P0 q3 q4 := hord q3 hq3W q4 hq4W (by omega)
  have hq1V := (hWmem q1 hq1W).1
  have hq2V := (hWmem q2 hq2W).1
  have hq3V := (hWmem q3 hq3W).1
  have hq4V := (hWmem q4 hq4W).1
  have t123 := orient_pos_of_angular_order V hgp hV P0 q1 q2 q3 hP0V hq1V hq2V hq3V o12 o23 o13
  have t124 := orient_pos_of_angular_order V hgp hV P0 q1 q2 q4 hP0V hq1V hq2V hq4V o12 o24 o14
  have t134 := orient_pos_of_angular_order V hgp hV P0 q1 q3 q4 hP0V hq1V hq3V hq4V o13 o34 o14
  have t234 := orient_pos_of_angular_order V hgp hV P0 q2 q3 q4 hP0V hq2V hq3V hq4V o23 o34 o24
  have rot : ∀ a b c : Point, orient a b c = orient b c a ∧ orient a b c = orient c a b := by
    intro a b c
    unfold orient
    constructor <;> ring
  obtain ⟨n01, n02, n12⟩ := ne_of_orient_pos P0 q1 q2 o12
  obtain ⟨-, n03, n13⟩ := ne_of_orient_pos P0 q1 q3 o13
  obtain ⟨-, n04, n14⟩ := ne_of_orient_pos P0 q1 q4 o14
  obtain ⟨-, -, n23⟩ := ne_of_orient_pos P0 q2 q3 o23
  obtain ⟨-, -, n24⟩ := ne_of_orient_pos P0 q2 q4 o24
  obtain ⟨-, -, n34⟩ := ne_of_orient_pos P0 q3 q4 o34
  refine ⟨![P0, q1, q2, q3, q4], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [n01, n02, n03, n04, n12, n13, n14, n23, n24, n34, n01.symm, n02.symm, n03.symm,
        n04.symm, n12.symm, n13.symm, n14.symm, n23.symm, n24.symm, n34.symm] at hij ⊢
  · intro i
    fin_cases i <;> simp [hP0V, hq1V, hq2V, hq3V, hq4V]
  · intro i j hji hji1
    fin_cases i <;> fin_cases j <;> simp at hji hji1 ⊢ <;>
      linarith [o12, o13, o14, o23, o24, o34, t123, t124, t134, t234, (rot P0 q1 q2).1,
        (rot P0 q2 q3).1, (rot P0 q3 q4).1, (rot q1 q2 q3).1, (rot q1 q3 q4).1, (rot q2 q3 q4).1,
        (rot P0 q1 q4).2, (rot P0 q2 q4).2, (rot P0 q3 q4).2]

end Horton
