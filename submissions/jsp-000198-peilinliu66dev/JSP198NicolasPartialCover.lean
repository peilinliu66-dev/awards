/-
Copyright (c) 2026 JSP198 formalization contributors.
Released under the MIT license. See LICENSE.

Nicolas Theorem 4, Case I.A: the ACTUAL PARTIAL deletion-cap cover.
Mathematics: C. M. Nicolas, The Empty Hexagon Theorem (2007), Case I.A.
This finite viewing-rank implementation uses two narrow join triangles and
one common wide triangle. It does not use a full-cycle covering theorem.

Dependencies retain the MIT attribution of CollinYuanjieRen/awards,
commit b8bb4f7803f921a7970abc880291ad9372111360.
Target: Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Candidate source; not compiled in the authoring environment.
-/
import Mathlib
import JSP198NicolasCaseIRuns
import JSP198NicolasPartialCoverOrder

noncomputable section
open Classical Horton
namespace JSP198.Nicolas.PartialCover

/-! ## Actual triangles and viewing ranks -/

/-- Three strict clockwise side tests put the fourth point in the triangle.
The triangle's orientation is derived by the determinant sum identity. -/
lemma mem_triangle_of_three_negative
    (a b c z : Point)
    (h1 : orient a b z < 0) (h2 : orient b c z < 0)
    (h3 : orient c a z < 0) :
    z ∈ convexHull ℝ ({a, b, c} : Set Point) := by
  have hsum : orient a b c =
      orient a b z + orient b c z + orient c a z := by
    unfold orient
    ring
  have hbase : orient a b c < 0 := by linarith
  have hbase' : 0 < orient a c b := by
    have he : orient a c b = -orient a b c := by unfold orient; ring
    rw [he]
    linarith
  have hz1 : 0 < orient a c z := by
    rw [orient_reverse]
    linarith
  have hz2 : 0 < orient c b z := by
    rw [orient_reverse]
    linarith
  have hz3 : 0 < orient b a z := by
    rw [orient_reverse]
    linarith
  have hin := mem_interior_triangle_of_orient_pos a c b z hbase' hz1 hz2 hz3
  have he : ({a, c, b} : Set Point) = {a, b, c} := by
    ext y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [he] at hin
  exact interior_subset hin

lemma rank_triangle_strict
    (P : Finset Point) (hgp : GeneralPosition P)
    (x u v w z : Point) (hx : x ∈ hullVertices P)
    (hu : u ∈ inner P) (hv : v ∈ inner P)
    (hw : w ∈ inner P) (hz : z ∈ inner P)
    (hzu : z ≠ u) (hzv : z ≠ v) (hzw : z ≠ w)
    (hmem : z ∈ convexHull ℝ ({u, v, w} : Set Point)) :
    min (viewRank P x u) (min (viewRank P x v) (viewRank P x w)) < viewRank P x z ∧
    viewRank P x z < max (viewRank P x u) (max (viewRank P x v) (viewRank P x w)) := by
  exact viewRank_triangle_bounds P hgp x u v w z hx
    (Finset.mem_sdiff.mp hu).1 (Finset.mem_sdiff.mp hv).1
    (Finset.mem_sdiff.mp hw).1 (Finset.mem_sdiff.mp hz).1
    (chain_inner_ne_outer hu hx) (chain_inner_ne_outer hv hx)
    (chain_inner_ne_outer hw hx) (chain_inner_ne_outer hz hx)
    hzu hzv hzw hmem

/-- Weak bounds also cover the genuine shared-endpoint join d=a. -/
lemma rank_triangle_weak
    (P : Finset Point) (hgp : GeneralPosition P)
    (x u v w z : Point) (hx : x ∈ hullVertices P)
    (hu : u ∈ inner P) (hv : v ∈ inner P)
    (hw : w ∈ inner P) (hz : z ∈ inner P)
    (hmem : z ∈ convexHull ℝ ({u, v, w} : Set Point)) :
    min (viewRank P x u) (min (viewRank P x v) (viewRank P x w)) ≤ viewRank P x z ∧
    viewRank P x z ≤ max (viewRank P x u) (max (viewRank P x v) (viewRank P x w)) := by
  by_cases hzu : z = u
  · subst z
    constructor <;> omega
  by_cases hzv : z = v
  · subst z
    constructor <;> omega
  by_cases hzw : z = w
  · subst z
    constructor <;> omega
  obtain ⟨hl, hu'⟩ := rank_triangle_strict P hgp x u v w z hx
    hu hv hw hz hzu hzv hzw hmem
  exact ⟨hl.le, hu'.le⟩

lemma rank_lt_iff_orient
    (P : Finset Point) (hgp : GeneralPosition P)
    (x u v : Point) (hx : x ∈ hullVertices P)
    (hu : u ∈ inner P) (hv : v ∈ inner P) :
    viewRank P x u < viewRank P x v ↔ 0 < orient u v x := by
  have hh := outer_viewRank_lt_iff P hgp x u v hx
    (Finset.mem_sdiff.mp hu).1 (Finset.mem_sdiff.mp hv).1
    (chain_inner_ne_outer hu hx) (chain_inner_ne_outer hv hx)
  rw [orient_rotate x u v] at hh
  exact hh

lemma rank_ne_of_ne
    (P : Finset Point) (hgp : GeneralPosition P)
    (x u v : Point) (hx : x ∈ hullVertices P)
    (hu : u ∈ inner P) (hv : v ∈ inner P) (huv : u ≠ v) :
    viewRank P x u ≠ viewRank P x v := by
  exact outer_viewRank_ne P hgp x u v hx
    (Finset.mem_sdiff.mp hu).1 (Finset.mem_sdiff.mp hv).1
    (chain_inner_ne_outer hu hx) (chain_inner_ne_outer hv hx) huv

/-! ## The two narrow triangles and the wide triangle at a real join -/

/-- A coherent pair of REAL visible third-layer edges yields all rank constraints
used by the finite cover proof. Both narrow triangles may degenerate at d=a;
the common wide triangle never does. No triangle containment is an input. -/
theorem rankJoin_of_actual_edges
    (P : Finset Point) (hgp : GeneralPosition P)
    (x : Point) (hx : x ∈ hullVertices P)
    (v : ChainVertex P) (c d a b : Point)
    (hcd : BoundaryEdge (ChainThird P) c d)
    (hab : BoundaryEdge (ChainThird P) a b)
    (hface1 : 0 < orient c d (v : Point))
    (hface2 : 0 < orient a b (v : Point))
    (hgap : 0 ≤ orient (v : Point) d a) :
    RankJoin (viewRank P x c) (viewRank P x d) (viewRank P x v)
      (viewRank P x a) (viewRank P x b) := by
  have hc2 := chain_third_mem_inner2 hcd.1
  have hd2 := chain_third_mem_inner2 hcd.2.1
  have ha2 := chain_third_mem_inner2 hab.1
  have hb2 := chain_third_mem_inner2 hab.2.1
  have hcI := (Finset.mem_sdiff.mp hc2).1
  have hdI := (Finset.mem_sdiff.mp hd2).1
  have haI := (Finset.mem_sdiff.mp ha2).1
  have hbI := (Finset.mem_sdiff.mp hb2).1
  have hvI := chain_second_mem_inner v
  have hgpI : GeneralPosition (inner P) := gp_subset hgp Finset.sdiff_subset
  have hgpQ : GeneralPosition (ChainThird P) := gp_subset hgpI
    ((hullVertices_subset (inner (inner P))).trans Finset.sdiff_subset)
  have hvc : (v : Point) ≠ c := (chain_inner2_ne_second hc2 v).symm
  have hvd : (v : Point) ≠ d := (chain_inner2_ne_second hd2 v).symm
  have hva : (v : Point) ≠ a := (chain_inner2_ne_second ha2 v).symm
  have hvb : (v : Point) ≠ b := (chain_inner2_ne_second hb2 v).symm
  have hvcD : 0 < orient (v : Point) c d := by
    rw [orient_rotate (v : Point) c d]
    exact hface1
  have hvaB : 0 < orient (v : Point) a b := by
    rw [orient_rotate (v : Point) a b]
    exact hface2
  have hgapCases : d = a ∨ 0 < orient (v : Point) d a := by
    by_cases he : d = a
    · exact Or.inl he
    · right
      have hne := hgpI v hvI d hdI a haI hvd hva he
      exact lt_of_le_of_ne hgap hne.symm
  have hvcA : 0 < orient (v : Point) c a := by
    rcases hgapCases with he | hg
    · simpa only [← he] using hvcD
    · exact orient_pos_trans_from_hull_vertex (inner P) hgpI
        v c d a v.property hcI hdI haI hvcD hg
  have hvdB : 0 < orient (v : Point) d b := by
    rcases hgapCases with he | hg
    · simpa only [he] using hvaB
    · exact orient_pos_trans_from_hull_vertex (inner P) hgpI
        v d a b v.property hdI haI hbI hg hvaB
  have hvcB : 0 < orient (v : Point) c b :=
    orient_pos_trans_from_hull_vertex (inner P) hgpI
      v c d b v.property hcI hdI hbI hvcD hvdB
  have hca : c ≠ a := by
    intro he
    have hh := hvcA
    rw [he] at hh
    simp [orient, mul_comm] at hh
  have hdb : d ≠ b := by
    intro he
    have hh := hvdB
    rw [he] at hh
    simp [orient, mul_comm] at hh
  have hcb : c ≠ b := by
    intro he
    have hh := hvcB
    rw [he] at hh
    simp [orient, mul_comm] at hh
  have hdca : d ∈ convexHull ℝ ({c, (v : Point), a} : Set Point) := by
    rcases hgapCases with he | hg
    · rw [he]
      exact subset_convexHull ℝ _ (by simp)
    · have hda : d ≠ a := by
        intro he
        rw [he] at hg
        simp [orient, mul_comm] at hg
      apply mem_triangle_of_three_negative c v a d
      · have he : orient c v d = -orient c d v := by unfold orient; ring
        rw [he]
        linarith
      · have he : orient v a d = -orient v d a := by unfold orient; ring
        rw [he]
        linarith
      · have hh := hcd.strict hgpQ hab.1 hca.symm hda.symm
        have he : orient a c d = orient c d a := by unfold orient; ring
        rwa [he]
  have hadb : a ∈ convexHull ℝ ({d, (v : Point), b} : Set Point) := by
    rcases hgapCases with he | hg
    · rw [← he]
      exact subset_convexHull ℝ _ (by simp)
    · have hda : d ≠ a := by
        intro he
        rw [he] at hg
        simp [orient, mul_comm] at hg
      apply mem_triangle_of_three_negative d v b a
      · have he : orient d v a = -orient v d a := by unfold orient; ring
        rw [he]
        linarith
      · have he : orient v b a = -orient a b v := by unfold orient; ring
        rw [he]
        linarith
      · have hh := hab.strict hgpQ hcd.2.1 hda hdb
        have he : orient b d a = orient a b d := by unfold orient; ring
        rwa [he]
  have hdwide : d ∈ convexHull ℝ ({c, (v : Point), b} : Set Point) := by
    apply mem_triangle_of_three_negative c v b d
    · have he : orient c v d = -orient c d v := by unfold orient; ring
      rw [he]
      linarith
    · have he : orient v b d = -orient v d b := by unfold orient; ring
      rw [he]
      linarith
    · have hh := hcd.strict hgpQ hab.2.1 hcb.symm hdb.symm
      have he : orient b c d = orient c d b := by unfold orient; ring
      rwa [he]
  have hawide : a ∈ convexHull ℝ ({c, (v : Point), b} : Set Point) := by
    apply mem_triangle_of_three_negative c v b a
    · have he : orient c v a = -orient v c a := by unfold orient; ring
      rw [he]
      linarith
    · have he : orient v b a = -orient a b v := by unfold orient; ring
      rw [he]
      linarith
    · have hh := hab.strict hgpQ hcd.1 hca hcb
      have he : orient b c a = orient a b c := by unfold orient; ring
      rwa [he]
  obtain ⟨hdlo, hdhi⟩ := rank_triangle_weak P hgp x c v a d hx
    hcI hvI haI hdI hdca
  obtain ⟨halo, hahi⟩ := rank_triangle_weak P hgp x d v b a hx
    hdI hvI hbI haI hadb
  obtain ⟨hdwlo, hdwhi⟩ := rank_triangle_strict P hgp x c v b d hx
    hcI hvI hbI hdI hcd.2.2.1.symm hvd.symm hdb hdwide
  obtain ⟨hawlo, hawhi⟩ := rank_triangle_strict P hgp x c v b a hx
    hcI hvI hbI haI hca.symm hva.symm hab.2.2.1 hawide
  exact ⟨hdlo, hdhi, halo, hahi, hdwlo, hdwhi, hawlo, hawhi⟩

/-! ## The actual finite run and its actual deletion cap -/

variable {P : Finset Point} {hgp : GeneralPosition P}
  {o : Point} {ho : o ∈ inner (inner (inner P))}

def runPoint (R : ActualCaseIRun P hgp o ho) (j : ℕ) : ChainVertex P :=
  orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j

def runStart (R : ActualCaseIRun P hgp o ho) (j : ℕ) : Point :=
  matchStart P hgp o ho (runPoint R j)

def runEnd (R : ActualCaseIRun P hgp o ho) (j : ℕ) : Point :=
  matchEnd P hgp o ho (runPoint R j)

def beforeRun (R : ActualCaseIRun P hgp o ho) : ChainVertex P :=
  (chainCycle P hgp o ho).symm R.first

def afterRun (R : ActualCaseIRun P hgp o ho) : ChainVertex P :=
  chainCycle P hgp o ho R.last

/-- Exactly H(A,a0,...,ak,bk,B) intersected with C1, with strict signs.
No full-arc or full-cycle cap is substituted for this definition. -/
def deletionCap (R : ActualCaseIRun P hgp o ho) : Finset Point :=
  (hullVertices P).filter (fun x =>
    0 < orient (beforeRun R) (runStart R 0) x ∨
    (∃ j ∈ Finset.range R.length,
      0 < orient (runStart R j) (runStart R (j + 1)) x) ∨
    0 < orient (runStart R R.length) (runEnd R R.length) x ∨
    0 < orient (runEnd R R.length) (afterRun R) x)

def rightChannel (R : ActualCaseIRun P hgp o ho) (j : ℕ) : Finset Point :=
  matchChannel P (runPoint R j) (runPoint R (j + 1)) (runStart R j) (runEnd R j)

def coverCells (R : ActualCaseIRun P hgp o ho) : Finset Point :=
  (outerFan P (runStart R 0) (beforeRun R, runPoint R 0) ∪
    (Finset.range R.length).biUnion (rightChannel R)) ∪
    outerFan P (runEnd R R.length) (runPoint R R.length, afterRun R)

/-- Nicolas I.A's partial cover, from the actual run and only its local sector
changes. No continuous-arc certificate, cap convexity, global distinctness,
whole-circle cover, minimality, or absence of hexagons is assumed. -/
theorem actual_run_cap_cover
    (R : ActualCaseIRun P hgp o ho)
    (hchanges : ∀ j : ℕ, j < R.length →
      sectorEdge P hgp o ho (runPoint R j) ≠
        sectorEdge P hgp o ho (runPoint R (j + 1))) :
    deletionCap R ⊆ coverCells R := by
  let f := chainCycle P hgp o ho
  let k := R.length
  let r : ℕ → ChainVertex P := runPoint R
  let a : ℕ → Point := runStart R
  let b : ℕ → Point := runEnd R
  let A : ChainVertex P := beforeRun R
  let B : ChainVertex P := afterRun R
  have rzero : r 0 = R.first := rfl
  have rlast : r k = R.last := rfl
  have rstep : ∀ j : ℕ, r (j + 1) = f (r j) := fun _ => rfl
  have ha2 : ∀ j, a j ∈ inner (inner P) := fun j => matchStart_mem P hgp o ho (r j)
  have hb2 : ∀ j, b j ∈ inner (inner P) := fun j => matchEnd_mem P hgp o ho (r j)
  have haI : ∀ j, a j ∈ inner P := fun j => (Finset.mem_sdiff.mp (ha2 j)).1
  have hbI : ∀ j, b j ∈ inner P := fun j => (Finset.mem_sdiff.mp (hb2 j)).1
  have hrI : ∀ j, (r j : Point) ∈ inner P := fun j => chain_second_mem_inner (r j)
  have hAI := chain_second_mem_inner A
  have hBI := chain_second_mem_inner B
  have habEdge : ∀ j, BoundaryEdge (ChainThird P) (a j) (b j) :=
    fun j => matchStartEnd_edge P hgp o ho (r j)
  have hown : ∀ j, 0 < orient (a j) (b j) (r j : Point) :=
    fun j => sectorEdge_outward P hgp o ho (r j)
  have hAr : BoundaryEdge (ChainSecond P) A (r 0) := by
    have hh := chainCycle_edge P hgp o ho A
    simpa only [A, beforeRun, Equiv.apply_symm_apply, rzero] using hh
  have hrB : BoundaryEdge (ChainSecond P) (r k) B :=
    chainCycle_edge P hgp o ho (r k)
  have hgpI : GeneralPosition (inner P) := gp_subset hgp Finset.sdiff_subset
  have hstartNeg : orient (a 0) (b 0) (A : Point) < 0 := by
    have hn : ¬ 0 < orient (a 0) (b 0) (A : Point) := R.noLeft
    have hne := hgp (a 0) (Finset.mem_sdiff.mp (haI 0)).1
      (b 0) (Finset.mem_sdiff.mp (hbI 0)).1 A (Finset.mem_sdiff.mp hAI).1
      (habEdge 0).2.2.1 (chain_inner2_ne_second (ha2 0) A)
      (chain_inner2_ne_second (hb2 0) A)
    exact lt_of_le_of_ne (le_of_not_gt hn) hne
  have hendNeg : orient (a k) (b k) (B : Point) < 0 := by
    have hn : ¬ 0 < orient (a k) (b k) (B : Point) := R.noRight_end
    have hne := hgp (a k) (Finset.mem_sdiff.mp (haI k)).1
      (b k) (Finset.mem_sdiff.mp (hbI k)).1 B (Finset.mem_sdiff.mp hBI).1
      (habEdge k).2.2.1 (chain_inner2_ne_second (ha2 k) B)
      (chain_inner2_ne_second (hb2 k) B)
    exact lt_of_le_of_ne (le_of_not_gt hn) hne
  have hfirstTriangle : a 0 ∈ convexHull ℝ ({(A : Point), (r 0 : Point), b 0} : Set Point) := by
    apply mem_triangle_of_three_negative A (r 0) (b 0) (a 0)
    · have hh := boundaryEdge_inner_strict (inner P) hgpI (a 0) (ha2 0) A (r 0) hAr
      rwa [orient_rotate (a 0) A (r 0)] at hh
    · have he : orient (r 0) (b 0) (a 0) = -orient (a 0) (b 0) (r 0) := by
        unfold orient
        ring
      rw [he]
      have hh := hown 0
      linarith
    · have he : orient (b 0) A (a 0) = orient (a 0) (b 0) A := by unfold orient; ring
      rwa [he]
  have hlastTriangle : b k ∈ convexHull ℝ ({a k, (r k : Point), (B : Point)} : Set Point) := by
    apply mem_triangle_of_three_negative (a k) (r k) B (b k)
    · have he : orient (a k) (r k) (b k) = -orient (a k) (b k) (r k) := by unfold orient; ring
      rw [he]
      have hh := hown k
      linarith
    · have hh := boundaryEdge_inner_strict (inner P) hgpI (b k) (hb2 k) (r k) B hrB
      rwa [orient_rotate (b k) (r k) B] at hh
    · have he : orient B (a k) (b k) = orient (a k) (b k) B := by unfold orient; ring
      rwa [he]

  intro x hxCap
  obtain ⟨hx, hxStep⟩ := Finset.mem_filter.mp hxCap
  change x ∈ hullVertices P at hx
  have hlt : ∀ u v : Point, u ∈ inner P → v ∈ inner P →
      (viewRank P x u < viewRank P x v ↔ 0 < orient u v x) :=
    fun u v hu hv => rank_lt_iff_orient P hgp x u v hx hu hv
  have hfirst := rank_triangle_strict P hgp x A (r 0) (b 0) (a 0) hx
    hAI (hrI 0) (hbI 0) (haI 0)
    (chain_inner2_ne_second (ha2 0) A)
    (chain_inner2_ne_second (ha2 0) (r 0)) (habEdge 0).2.2.1 hfirstTriangle
  have hlast := rank_triangle_strict P hgp x (a k) (r k) B (b k) hx
    (haI k) (hrI k) hBI (hbI k) (habEdge k).2.2.1.symm
    (chain_inner2_ne_second (hb2 k) (r k))
    (chain_inner2_ne_second (hb2 k) B) hlastTriangle
  have hjoin : ∀ j, j < k →
      RankJoin (viewRank P x (a j)) (viewRank P x (b j)) (viewRank P x (r (j + 1)))
        (viewRank P x (a (j + 1))) (viewRank P x (b (j + 1))) := by
    intro j hj
    have hface : 0 < orient (a j) (b j) (r (j + 1)) := R.right_before j hj
    have hchange : sectorEdge P hgp o ho (r j) ≠ sectorEdge P hgp o ho (f (r j)) :=
      hchanges j hj
    have hgap : 0 ≤ orient (r (j + 1)) (b j) (a (j + 1)) :=
      right_radial_join_coherent P hgp o ho (r j) hchange (R.right_before j hj)
    exact rankJoin_of_actual_edges P hgp x hx (r (j + 1))
      (a j) (b j) (a (j + 1)) (b (j + 1))
      (habEdge j) (habEdge (j + 1)) hface (hown (j + 1)) hgap
  have hra : ∀ j, j ≤ k → viewRank P x (r j) ≠ viewRank P x (a j) := by
    intro j _
    exact rank_ne_of_ne P hgp x (r j) (a j) hx (hrI j) (haI j)
      (chain_inner2_ne_second (ha2 j) (r j)).symm
  have habRank : ∀ j, j ≤ k → viewRank P x (a j) ≠ viewRank P x (b j) := by
    intro j _
    exact rank_ne_of_ne P hgp x (a j) (b j) hx (haI j) (hbI j) (habEdge j).2.2.1
  have hbr : ∀ j, j < k → viewRank P x (b j) ≠ viewRank P x (r (j + 1)) := by
    intro j _
    exact rank_ne_of_ne P hgp x (b j) (r (j + 1)) hx (hbI j) (hrI (j + 1))
      (chain_inner2_ne_second (hb2 j) (r (j + 1)))
  have hrankCap : viewRank P x A < viewRank P x (a 0) ∨
      (∃ j, j < k ∧ viewRank P x (a j) < viewRank P x (a (j + 1))) ∨
      viewRank P x (a k) < viewRank P x (b k) ∨
      viewRank P x (b k) < viewRank P x B := by
    change 0 < orient A (a 0) x ∨
      (∃ j ∈ Finset.range k, 0 < orient (a j) (a (j + 1)) x) ∨
      0 < orient (a k) (b k) x ∨ 0 < orient (b k) B x at hxStep
    rcases hxStep with h | ⟨j, hj, h⟩ | h | h
    · exact Or.inl ((hlt A (a 0) hAI (haI 0)).mpr h)
    · exact Or.inr (Or.inl ⟨j, Finset.mem_range.mp hj,
        (hlt (a j) (a (j + 1)) (haI j) (haI (j + 1))).mpr h⟩)
    · exact Or.inr (Or.inr (Or.inl ((hlt (a k) (b k) (haI k) (hbI k)).mpr h)))
    · exact Or.inr (Or.inr (Or.inr ((hlt (b k) B (hbI k) hBI).mpr h)))
  have hh := partial_cover_order k (viewRank P x A) (viewRank P x B)
    (fun j => viewRank P x (r j)) (fun j => viewRank P x (a j))
    (fun j => viewRank P x (b j)) hra habRank hbr hfirst hlast hjoin hrankCap
  change x ∈ (outerFan P (a 0) (A, r 0) ∪
      (Finset.range k).biUnion (fun j => matchChannel P (r j) (r (j + 1)) (a j) (b j))) ∪
      outerFan P (b k) (r k, B)
  rcases hh with ⟨h1, h2⟩ | ⟨j, hj, h1, h2, h3⟩ | ⟨h1, h2⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨hx, ?_⟩
    change 0 < orient A (a 0) x ∧ 0 < orient (a 0) (r 0) x
    exact ⟨(hlt A (a 0) hAI (haI 0)).mp h1,
      (hlt (a 0) (r 0) (haI 0) (hrI 0)).mp h2⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_range.mpr hj, Finset.mem_filter.mpr ⟨hx, ?_⟩⟩
    exact ⟨(hlt (r j) (a j) (hrI j) (haI j)).mp h1,
      (hlt (a j) (b j) (haI j) (hbI j)).mp h2,
      (hlt (b j) (r (j + 1)) (hbI j) (hrI (j + 1))).mp h3⟩
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨hx, ?_⟩
    change 0 < orient (r k) (b k) x ∧ 0 < orient (b k) B x
    exact ⟨(hlt (r k) (b k) (hrI k) (hbI k)).mp h1,
      (hlt (b k) B (hbI k) hBI).mp h2⟩

/-- Cardinality consequence of the partial cover, using the already proved
local channel/fan bounds. This remains a LOCAL result, not Case I.A as a whole. -/
theorem actual_run_cap_card_le
    (R : ActualCaseIRun P hgp o ho)
    (hchanges : ∀ j : ℕ, j < R.length →
      sectorEdge P hgp o ho (runPoint R j) ≠
        sectorEdge P hgp o ho (runPoint R (j + 1)))
    (hno : ¬ HasEmptySix P) :
    (deletionCap R).card ≤ R.length + 4 := by
  let k := R.length
  let A := beforeRun R
  let B := afterRun R
  let r := runPoint R
  let a := runStart R
  let b := runEnd R
  have hAr : BoundaryEdge (ChainSecond P) A (r 0) := by
    have hh := chainCycle_edge P hgp o ho A
    simpa only [A, beforeRun, r, runPoint, orbit, Equiv.apply_symm_apply] using hh
  have hrB : BoundaryEdge (ChainSecond P) (r k) B :=
    chainCycle_edge P hgp o ho (r k)
  have hfirst : (outerFan P (a 0) (A, r 0)).card ≤ 2 := by
    have ha2 := matchStart_mem P hgp o ho (r 0)
    exact outerFan_card_le_two P hgp hno (a 0) (Finset.mem_sdiff.mp ha2).1
      (A, r 0) hAr (chain_inner2_ne_second ha2 A) (chain_inner2_ne_second ha2 (r 0))
  have hlast : (outerFan P (b k) (r k, B)).card ≤ 2 := by
    have hb2 := matchEnd_mem P hgp o ho (r k)
    exact outerFan_card_le_two P hgp hno (b k) (Finset.mem_sdiff.mp hb2).1
      (r k, B) hrB (chain_inner2_ne_second hb2 (r k)) (chain_inner2_ne_second hb2 B)
  have hright : ∀ j ∈ Finset.range k, (rightChannel R j).card ≤ 1 := by
    intro j hj
    have hjk := Finset.mem_range.mp hj
    exact boundary_match_channel_le_one P hgp hno (r j) (r (j + 1)) (a j) (b j)
      (chainCycle_edge P hgp o ho (r j)) (matchStartEnd_edge P hgp o ho (r j))
      (sectorEdge_outward P hgp o ho (r j)) (R.right_before j hjk)
  have hmid : ((Finset.range k).biUnion (rightChannel R)).card ≤ k := by
    calc
      ((Finset.range k).biUnion (rightChannel R)).card ≤
          ∑ j ∈ Finset.range k, (rightChannel R j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Finset.range k, (1 : ℕ) := Finset.sum_le_sum hright
      _ = k := by simp
  have hc := Finset.card_le_card (actual_run_cap_cover R hchanges)
  have h1 := Finset.card_union_le (outerFan P (a 0) (A, r 0))
    ((Finset.range k).biUnion (rightChannel R))
  have h2 := Finset.card_union_le
    (outerFan P (a 0) (A, r 0) ∪ (Finset.range k).biUnion (rightChannel R))
    (outerFan P (b k) (r k, B))
  change (deletionCap R).card ≤ k + 4
  change (deletionCap R).card ≤
    ((outerFan P (a 0) (A, r 0) ∪ (Finset.range k).biUnion (rightChannel R)) ∪
      outerFan P (b k) (r k, B)).card at hc
  omega


/-- The exact singleton-fiber condition returned by ScopeBridge discharges the
LOCAL change assumption. Vertices outside the run may share their sectors. -/
lemma local_changes_of_singleton_fibers
    (R : ActualCaseIRun P hgp o ho)
    (hsingle : ∀ j : ℕ, j ≤ R.length → ∀ s : ChainVertex P,
      sectorEdge P hgp o ho s = sectorEdge P hgp o ho (runPoint R j) →
      s = runPoint R j) :
    ∀ j : ℕ, j < R.length →
      sectorEdge P hgp o ho (runPoint R j) ≠
        sectorEdge P hgp o ho (runPoint R (j + 1)) := by
  intro j hj he
  have hs := hsingle j (by omega) (runPoint R (j + 1)) he.symm
  have hp := congrArg (fun v : ChainVertex P => (v : Point)) hs
  exact (chainCycle_edge P hgp o ho (runPoint R j)).2.2.1 hp.symm

theorem actual_run_cap_cover_of_singleton_fibers
    (R : ActualCaseIRun P hgp o ho)
    (hsingle : ∀ j : ℕ, j ≤ R.length → ∀ s : ChainVertex P,
      sectorEdge P hgp o ho s = sectorEdge P hgp o ho (runPoint R j) →
      s = runPoint R j) :
    deletionCap R ⊆ coverCells R :=
  actual_run_cap_cover R (local_changes_of_singleton_fibers R hsingle)

theorem actual_run_cap_card_le_of_singleton_fibers
    (R : ActualCaseIRun P hgp o ho)
    (hsingle : ∀ j : ℕ, j ≤ R.length → ∀ s : ChainVertex P,
      sectorEdge P hgp o ho s = sectorEdge P hgp o ho (runPoint R j) →
      s = runPoint R j)
    (hno : ¬ HasEmptySix P) :
    (deletionCap R).card ≤ R.length + 4 :=
  actual_run_cap_card_le R (local_changes_of_singleton_fibers R hsingle) hno

end JSP198.Nicolas.PartialCover

#print axioms JSP198.Nicolas.PartialCover.rankJoin_of_actual_edges
#print axioms JSP198.Nicolas.PartialCover.actual_run_cap_cover
#print axioms JSP198.Nicolas.PartialCover.actual_run_cap_card_le

#print axioms JSP198.Nicolas.PartialCover.actual_run_cap_card_le_of_singleton_fibers
