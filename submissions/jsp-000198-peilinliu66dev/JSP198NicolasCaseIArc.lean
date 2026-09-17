/-
Copyright (c) 2026 JSP198 formalization contributors.
Released under the MIT license.
Actual radial order for the remaining Nicolas Case I.A branch.
The actual arc is constructed below from run-local singleton fibers.
-/
import JSP198NicolasCaseIB
import JSP198NicolasCaseII

set_option maxHeartbeats 1200000
noncomputable section
open Classical Horton
namespace JSP198.Nicolas

abbrev ThirdVertex (P : Finset Point) := ((ChainThird P : Finset Point) : Set Point)

/-- A complete actual third-layer arc, including every intermediate cycle
vertex between the selected sector starts. Existence is proved below. -/
structure ActualCaseIArc
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho) where
  cycle : Equiv.Perm (ThirdVertex P)
  edge : ∀ q : ThirdVertex P, BoundaryEdge (ChainThird P) q (cycle q)
  reaches : ∀ a b : ThirdVertex P, ∃ i : ℕ,
    i ≤ (ChainThird P).card ∧ orbit cycle a i = b
  enumeration : Function.Bijective (fun i : Fin ((ChainThird P).card) =>
    orbit (α := ThirdVertex P) cycle (sectorVertex P hgp o ho R.first) i.val)
  closed : orbit (α := ThirdVertex P) cycle (sectorVertex P hgp o ho R.first)
    (ChainThird P).card = sectorVertex P hgp o ho R.first
  index : Fin (R.length+1) → ℕ
  zero : index ⟨0, by omega⟩ = 0
  strictMono : StrictMono index
  last_lt : index ⟨R.length, by omega⟩ + 1 < (ChainThird P).card
  start : ∀ j : Fin (R.length+1),
    (orbit (α := ThirdVertex P) cycle (sectorVertex P hgp o ho R.first) (index j) : Point) =
      matchStart P hgp o ho (orbit (chainCycle P hgp o ho) R.first j.val)
  finish : ∀ j : Fin (R.length+1),
    (orbit (α := ThirdVertex P) cycle (sectorVertex P hgp o ho R.first) (index j+1) : Point) =
      matchEnd P hgp o ho (orbit (chainCycle P hgp o ho) R.first j.val)

private def arcDot (o c x : Point) : ℝ :=
  (c.1-o.1)*(x.1-o.1) + (c.2-o.2)*(x.2-o.2)

/-- Clockwise angular order cut at the ray oc. The zero determinant class
comes first; general position later ensures this class contains only c. -/
def arcKey (o c x : Point) : ℕ ×ₗ ℝ :=
  if orient o c x = 0 then toLex (0,0) else
  if orient o c x < 0 then toLex (1,arcDot o c x / orient o c x)
  else toLex (2,arcDot o c x / orient o c x)

private lemma arc_dot_cross (o c x y : Point) :
    arcDot o c x * orient o c y - arcDot o c y * orient o c x =
      ((c.1-o.1)^2+(c.2-o.2)^2) * orient o x y := by
  unfold arcDot orient
  ring

private lemma arc_norm_pos (o c : Point) (hc : o ≠ c) :
    0 < (c.1-o.1)^2+(c.2-o.2)^2 := by
  have hn : c.1-o.1 ≠ 0 ∨ c.2-o.2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    apply Prod.ext <;> linarith
  rcases hn with hx | hy
  · have := sq_pos_of_ne_zero hx
    nlinarith [sq_nonneg (c.2-o.2)]
  · have := sq_pos_of_ne_zero hy
    nlinarith [sq_nonneg (c.1-o.1)]

private lemma arc_cross_lt (o c x y : Point) (hc : o ≠ c)
    (hxy : orient o x y < 0) :
    arcDot o c x * orient o c y < arcDot o c y * orient o c x := by
  have h := mul_neg_of_pos_of_neg (arc_norm_pos o c hc) hxy
  rw [← arc_dot_cross] at h
  linarith

/-- A clockwise step that does not cross the cut ray strictly increases the
actual angular key. This is proved from determinant signs, not injectivity. -/
lemma arcKey_lt_of_clockwise_no_cut (o c x y : Point) (hc : o ≠ c)
    (hxy : orient o x y < 0) (hy : orient o c y ≠ 0)
    (hcut : ¬ InFan o x y c) : arcKey o c x < arcKey o c y := by
  have hcross := arc_cross_lt o c x y hc hxy
  by_cases hx0 : orient o c x = 0
  · unfold arcKey
    rw [if_pos hx0, if_neg hy]
    split <;> simp [Prod.Lex.toLex_lt_toLex]
  by_cases hx : orient o c x < 0
  · by_cases hyneg : orient o c y < 0
    · have hratio : arcDot o c x / orient o c x < arcDot o c y / orient o c y := by
        have h := (div_lt_div_iff₀ (neg_pos.mpr hx) (neg_pos.mpr hyneg)).mpr
          (show -arcDot o c x * -orient o c y < -arcDot o c y * -orient o c x by nlinarith)
        simpa only [neg_div_neg_eq] using h
      simpa only [arcKey, if_neg hx0, if_neg hy, if_pos hx, if_pos hyneg,
        Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] using hratio
    · simp [arcKey, hx0, hy, hx, hyneg, Prod.Lex.toLex_lt_toLex]
  · have hxpos : 0 < orient o c x :=
      lt_of_le_of_ne (le_of_not_gt hx) (by intro h; exact hx0 h.symm)
    have hypos : 0 < orient o c y := by
      by_contra h
      have hyneg : orient o c y < 0 := lt_of_le_of_ne (le_of_not_gt h) hy
      apply hcut
      constructor
      · have he : orient x o c = orient o c x := by unfold orient; ring
        rw [he]; exact hxpos
      · have he : orient o y c = -orient o c y := by unfold orient; ring
        rw [he]; linarith
    have hratio := (div_lt_div_iff₀ hxpos hypos).mpr hcross
    simpa only [arcKey, if_neg hx0, if_neg hy, if_neg hx,
      if_neg (not_lt.mpr hypos.le), Prod.Lex.toLex_lt_toLex,
      lt_self_iff_false, true_and, false_or] using hratio

/-- The start of a non-wrapping fan is before every strict interior ray. -/
lemma arcKey_start_lt_of_fan (o c x y z : Point) (hc : o ≠ c)
    (hxy : orient o x y < 0) (hz : orient o c z ≠ 0)
    (hf : InFan o x y z) (hcut : ¬InFan o x y c) :
    arcKey o c x < arcKey o c z := by
  have hxz : orient o x z < 0 := by
    have h := hf.1
    have he : orient x o z = -orient o x z := by unfold orient; ring
    rw [he] at h; linarith
  apply arcKey_lt_of_clockwise_no_cut o c x z hc hxz hz
  intro hbad
  have hcx : 0 < orient o c x := by
    have h := hbad.1
    have he : orient x o c = orient o c x := by unfold orient; ring
    rwa [he] at h
  have hcz : orient o c z < 0 := by
    have h := hbad.2
    have he : orient o z c = -orient o c z := by unfold orient; ring
    rw [he] at h; linarith
  have hcy : 0 ≤ orient o c y := by
    by_contra h
    apply hcut
    constructor
    · have he : orient x o c = orient o c x := by unfold orient; ring
      rw [he]; exact hcx
    · have he : orient o y c = -orient o c y := by unfold orient; ring
      rw [he]; linarith
  have hp := mul_pos hcx hf.2
  have hn := mul_nonpos_of_nonneg_of_nonpos hcy hxz.le
  have hm := mul_pos_of_neg_of_neg hcz hxy
  have hid := radial_plucker o c x y z
  nlinarith

lemma arc_run_changes
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho) (hsingle : RunHasSingletonSectors R)
    (j : ℕ) (hj : j ≤ R.length) :
    sectorEdge P hgp o ho (orbit (chainCycle P hgp o ho) R.first j) ≠
      sectorEdge P hgp o ho
        (chainCycle P hgp o ho (orbit (chainCycle P hgp o ho) R.first j)) := by
  intro he
  have hh := hsingle j hj _ he.symm
  exact (chainCycle_edge P hgp o ho _).2.2.1
    (congrArg (fun z : ChainVertex P => (z : Point)) hh).symm

lemma arc_cut_in_incoming_edge
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho) (hsingle : RunHasSingletonSectors R) :
    InFan o ((chainCycle P hgp o ho).symm R.first) R.first
      (matchStart P hgp o ho R.first) := by
  let f := chainCycle P hgp o ho
  let p := f.symm R.first
  have hd : sectorEdge P hgp o ho p ≠ sectorEdge P hgp o ho (f p) := by
    intro he
    have he' : sectorEdge P hgp o ho p = sectorEdge P hgp o ho R.first := by
      simpa only [p, Equiv.apply_symm_apply] using he
    have hh := hsingle 0 (Nat.zero_le _) p he'
    have hedge := chainCycle_edge P hgp o ho p
    change BoundaryEdge (ChainSecond P) p (f p) at hedge
    have hneq := hedge.2.2.1
    apply hneq
    simpa only [p, Equiv.apply_symm_apply, orbit] using
      congrArg (fun z : ChainVertex P => (z : Point)) hh
  have hh := next_sector_start_in_swept_edge P hgp o ho p hd
  change InFan o p (f p) (matchStart P hgp o ho (f p)) at hh
  simpa only [p, Equiv.apply_symm_apply] using hh

/-- Every edge of the short run avoids the initial cut ray. Its unique
incoming crossing lies outside the run; this proves real non-wrapping. -/
theorem arc_run_avoids_cut
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho) (hsingle : RunHasSingletonSectors R)
    (hshort : R.length + 2 ≤ (ChainSecond P).card)
    (j : ℕ) (hj : j ≤ R.length) :
    ¬InFan o (orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j)
      (orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first (j+1))
      (matchStart P hgp o ho R.first) := by
  intro hfan
  let f := chainCycle P hgp o ho
  let r := orbit (α := ChainVertex P) f R.first j
  let p := f.symm R.first
  let c := matchStart P hgp o ho R.first
  have hf1 : InFan o r (f r) c := hfan
  have hf2 : InFan o p R.first c := arc_cut_in_incoming_edge R hsingle
  have he1 : BoundaryEdge (ChainSecond P) r (f r) := chainCycle_edge P hgp o ho r
  have he2 : BoundaryEdge (ChainSecond P) p R.first := by
    have hh := chainCycle_edge P hgp o ho p
    change BoundaryEdge (ChainSecond P) p (f p) at hh
    simpa only [p, Equiv.apply_symm_apply] using hh
  have hgpQ := gp_subset hgp
    ((hullVertices_subset (inner P)).trans Finset.sdiff_subset)
  obtain ⟨h1,h2⟩ := (inFan_iff_raySides o r (f r) c).mp hf1
  obtain ⟨h3,h4⟩ := (inFan_iff_raySides o p R.first c).mp hf2
  obtain ⟨_,heq⟩ := boundary_fan_unique (ChainSecond P) hgpQ o c
    r (f r) p R.first he1 he2 h1 h2 h3 h4
  have heq' : orbit (α := ChainVertex P) f R.first (j+1) = R.first :=
    Subtype.ext heq
  have hi := (ib_full_cycle_enumeration P hgp o ho R.first).1
  have hind : (⟨j+1,by omega⟩ : Fin ((ChainSecond P).card)) = ⟨0,by omega⟩ :=
    hi heq'
  have hh := congrArg Fin.val hind
  simp only at hh
  omega

private lemma arc_root_ne_third
    {P : Finset Point} {o c : Point} (ho : o ∈ inner (inner (inner P)))
    (hc : c ∈ ChainThird P) : o ≠ c := by
  intro he
  exact (Finset.mem_sdiff.mp ho).2 (by rw [he]; exact hc)

private lemma arc_general_cut
    {P : Finset Point} (hgp : GeneralPosition P) {o c x : Point}
    (ho : o ∈ inner (inner (inner P))) (hc : c ∈ ChainThird P)
    (hx : x ∈ P) (hox : o ≠ x) (hcx : c ≠ x) : orient o c x ≠ 0 := by
  have hoP : o ∈ P :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ho).1).1).1
  have hcP : c ∈ P :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (chain_third_mem_inner2 hc)).1).1
  exact hgp o hoP c hcP x hx (arc_root_ne_third ho hc) hox hcx

lemma arc_sector_start_key_lt
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (c : Point) (hc : c ∈ ChainThird P) (r : ChainVertex P) :
    arcKey o c (matchStart P hgp o ho r) < arcKey o c r := by
  have hgII := gp_subset hgp
    (show inner (inner P) ⊆ P from Finset.sdiff_subset.trans Finset.sdiff_subset)
  have he := matchStartEnd_edge P hgp o ho r
  have hturn := boundaryEdge_inner_strict (inner (inner P)) hgII o ho _ _ he
  have hgen := arc_general_cut hgp ho hc
    (Finset.mem_sdiff.mp (chain_second_mem_inner r)).1
    (chain_inner2_ne_second (Finset.mem_sdiff.mp ho).1 r)
    (chain_inner2_ne_second (chain_third_mem_inner2 hc) r)
  exact arcKey_start_lt_of_fan o c _ _ r (arc_root_ne_third ho hc) hturn hgen
    (sectorEdge_inFan P hgp o ho r)
    (CaseII.third_vertex_not_in_root_fan P hgp o ho _ _ c he hc)

/-- Adjacent selected sector starts strictly advance in the genuine radial
order cut at a0. Outside vertices may share sectors. -/
theorem arc_run_start_key_step
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho) (hsingle : RunHasSingletonSectors R)
    (hshort : R.length + 2 ≤ (ChainSecond P).card)
    (j : ℕ) (hj : j < R.length) :
    arcKey o (matchStart P hgp o ho R.first)
      (matchStart P hgp o ho (orbit (chainCycle P hgp o ho) R.first j)) <
    arcKey o (matchStart P hgp o ho R.first)
      (matchStart P hgp o ho (orbit (chainCycle P hgp o ho) R.first (j+1))) := by
  let f := chainCycle P hgp o ho
  let r := orbit (α := ChainVertex P) f R.first j
  let c := matchStart P hgp o ho R.first
  let a := matchStart P hgp o ho (f r)
  have hc : c ∈ ChainThird P := (matchStartEnd_edge P hgp o ho R.first).1
  have ha : a ∈ ChainThird P := (matchStartEnd_edge P hgp o ho (f r)).1
  have hfan : InFan o r (f r) a :=
    next_sector_start_in_swept_edge P hgp o ho r (arc_run_changes R hsingle j (by omega))
  have hcut : ¬InFan o r (f r) c := arc_run_avoids_cut R hsingle hshort j (by omega)
  have hca : c ≠ a := by
    intro he
    apply hcut
    rwa [he]
  have haP : a ∈ P :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (chain_third_mem_inner2 ha)).1).1
  have hgen := arc_general_cut hgp ho hc haP (arc_root_ne_third ho ha) hca
  have hturn := boundaryEdge_inner_strict (inner P) (gp_subset hgp Finset.sdiff_subset)
    o (Finset.mem_sdiff.mp ho).1 r (f r) (chainCycle_edge P hgp o ho r)
  have hstep := arcKey_start_lt_of_fan o c r (f r) a
    (arc_root_ne_third ho hc) hturn hgen hfan hcut
  exact (arc_sector_start_key_lt P hgp o ho c hc r).trans hstep

theorem arc_run_start_keys_strictMono
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho) (hsingle : RunHasSingletonSectors R)
    (hshort : R.length + 2 ≤ (ChainSecond P).card) :
    StrictMono (fun j : Fin (R.length+1) =>
      arcKey o (matchStart P hgp o ho R.first)
        (matchStart P hgp o ho (orbit (chainCycle P hgp o ho) R.first j.val))) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact arc_run_start_key_step R hsingle hshort i.val i.isLt

/-- The last selected sector cannot end at the initial cut vertex. This is
the strict endpoint bound's geometric content. -/
theorem arc_last_end_ne_first_start
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho) (hsingle : RunHasSingletonSectors R)
    (hshort : R.length + 2 ≤ (ChainSecond P).card) :
    matchEnd P hgp o ho R.last ≠ matchStart P hgp o ho R.first := by
  intro he
  have hfan := previous_sector_end_in_swept_edge P hgp o ho R.last
    (arc_run_changes R hsingle R.length (le_refl _))
  rw [he] at hfan
  exact arc_run_avoids_cut R hsingle hshort R.length (le_refl _) hfan

private lemma arc_cycle_enumeration
    {A : Type*} [Fintype A] [DecidableEq A]
    (f : Equiv.Perm A) (first : A) (hne : ∀ a, f a ≠ a)
    (hreach : ∀ a, ∃ j : ℕ, orbit f first j = a) :
    Function.Bijective (fun j : Fin (Fintype.card A) => orbit f first j.val) ∧
      orbit f first (Fintype.card A) = first := by
  let last := f.symm first
  have hfirst : first ≠ last := by
    intro he
    have hh := congrArg f he
    have hh' : f first = first := by
      simpa only [last, Equiv.apply_symm_apply] using hh
    exact hne first hh'
  obtain ⟨j, hj⟩ := hreach last
  have hevent : ∃ j : ℕ, ¬ (orbit f first j ≠ last) := ⟨j, fun h => h hj⟩
  obtain ⟨k, _, _, _, hstop, hinj⟩ :=
    exists_first_failure_prefix f first (fun a => a ≠ last) hfirst hevent
  have hend : orbit f first k = last := by
    by_contra h
    exact hstop h
  have hclose : f (orbit f first k) = first := by
    rw [hend]
    exact f.apply_symm_apply first
  have hsurj := ib_closed_prefix_surjective f first k hclose hreach
  have hcard := Fintype.card_of_bijective ⟨hinj, hsurj⟩
  have hsize : k+1 = Fintype.card A := by
    simpa only [Fintype.card_fin] using hcard
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a b hab
    have he := hinj (a₁ := ⟨a.val, by omega⟩) (a₂ := ⟨b.val, by omega⟩) hab
    exact Fin.ext (congrArg (fun z : Fin (k+1) => z.val) he)
  · intro a
    obtain ⟨j, hj⟩ := hsurj a
    exact ⟨⟨j.val, by have := j.isLt; omega⟩, hj⟩
  · rw [← hsize]
    exact hclose

private lemma arc_strictMono_fin_of_steps
    {A : Type*} [Preorder A] {m : ℕ} (a : Fin m → A)
    (hstep : ∀ i : ℕ, ∀ hi : i+1 < m,
      a ⟨i, by omega⟩ < a ⟨i+1, hi⟩) : StrictMono a := by
  intro i j hij
  have hle : ∀ d : ℕ, ∀ hbound : i.val+d < m,
      0 < d → a i < a ⟨i.val+d, hbound⟩ := by
    intro d
    induction d with
    | zero => intro _ hd; omega
    | succ d ih =>
      intro hbound _
      by_cases hd : d = 0
      · subst d
        simpa only [Nat.add_zero] using hstep i.val hbound
      · have hb : i.val+d < m := by omega
        have hlt := ih hb (by omega)
        exact hlt.trans (hstep (i.val+d) hbound)
  have hval : i.val + (j.val-i.val) = j.val := by omega
  have hh := hle (j.val-i.val) (by omega) (by omega)
  simpa only [hval] using hh

/-- A real third-layer boundary cycle, enumerated from the cut vertex, is
strictly increasing in the proved cut angular order until its final vertex. -/
private lemma arc_third_cycle_key_strictMono
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (g : Equiv.Perm (ThirdVertex P))
    (hedge : ∀ q : ThirdVertex P, BoundaryEdge (ChainThird P) q (g q))
    (first : ThirdVertex P)
    (hinj : Function.Injective (fun i : Fin ((ChainThird P).card) =>
      orbit (α := ThirdVertex P) g first i.val)) :
    StrictMono (fun i : Fin ((ChainThird P).card) =>
      arcKey o first (orbit (α := ThirdVertex P) g first i.val)) := by
  apply arc_strictMono_fin_of_steps
  intro i hi
  let x := orbit (α := ThirdVertex P) g first i
  let y := orbit (α := ThirdVertex P) g first (i+1)
  have he : BoundaryEdge (ChainThird P) x y := hedge x
  have hfy : (first : Point) ≠ (y : Point) := by
    intro hh
    have heq : (⟨0,by omega⟩ : Fin ((ChainThird P).card)) = ⟨i+1,hi⟩ :=
      hinj (Subtype.ext hh)
    have hv := congrArg Fin.val heq
    simp only at hv
    omega
  have hyP : (y : Point) ∈ P :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (chain_third_mem_inner2 y.property)).1).1
  have hgen := arc_general_cut hgp ho first.property hyP
    (arc_root_ne_third ho y.property) hfy
  have hgII := gp_subset hgp
    (show inner (inner P) ⊆ P from Finset.sdiff_subset.trans Finset.sdiff_subset)
  have hturn := boundaryEdge_inner_strict (inner (inner P)) hgII o ho x y he
  exact arcKey_lt_of_clockwise_no_cut o first x y
    (arc_root_ne_third ho first.property) hturn hgen
    (CaseII.third_vertex_not_in_root_fan P hgp o ho x y first he first.property)

/-- The complete actual arc is constructed from run-local singleton fibers.
Every intermediate third-layer point is given by the real cycle orbit; the
indices are ordered by proved geometry and cannot wrap around the cut. -/
theorem exists_actual_caseIArc
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (R : ActualCaseIRun P hgp o ho) (hsingle : RunHasSingletonSectors R)
    (hshort : R.length + 2 ≤ (ChainSecond P).card) :
    Nonempty (ActualCaseIArc R) := by
  obtain ⟨_,g,_,hedge,_,hreach⟩ := actual_layer_boundary_cycles P hgp o ho
  let first : ThirdVertex P := sectorVertex P hgp o ho R.first
  have hcard : Fintype.card (ThirdVertex P) = (ChainThird P).card := Fintype.card_coe _
  have hne : ∀ a : ThirdVertex P, g a ≠ a := by
    intro a he
    exact (hedge a).2.2.1
      (congrArg (fun z : ThirdVertex P => (z : Point)) he).symm
  obtain ⟨hbij,hclose⟩ := arc_cycle_enumeration (A := ThirdVertex P) g first hne (fun a => by
    obtain ⟨j,_,hj⟩ := hreach first a
    exact ⟨j,hj⟩)
  have hbij' : Function.Bijective (fun i : Fin ((ChainThird P).card) =>
      orbit (α := ThirdVertex P) g first i.val) := by
    constructor
    · intro a b hab
      have he := hbij.1
        (a₁ := ⟨a.val, by have := a.isLt; omega⟩)
        (a₂ := ⟨b.val, by have := b.isLt; omega⟩) hab
      exact Fin.ext (congrArg (fun z : Fin (Fintype.card (ThirdVertex P)) => z.val) he)
    · intro a
      obtain ⟨i, hi⟩ := hbij.2 a
      exact ⟨⟨i.val, by have := i.isLt; omega⟩, hi⟩
  have hclose' : orbit (α := ThirdVertex P) g first (ChainThird P).card = first := by
    simpa only [hcard] using hclose
  have hkeys := arc_third_cycle_key_strictMono P hgp o ho g hedge first hbij'.1
  let a : Fin (R.length+1) → ThirdVertex P := fun j =>
    sectorVertex P hgp o ho (orbit (chainCycle P hgp o ho) R.first j.val)
  choose index hindex using (fun j : Fin (R.length+1) => hbij'.2 (a j))
  have hstart : ∀ j : Fin (R.length+1),
      (orbit (α := ThirdVertex P) g first (index j).val : Point) =
        matchStart P hgp o ho (orbit (chainCycle P hgp o ho) R.first j.val) := by
    intro j
    exact congrArg (fun z : ThirdVertex P => (z : Point)) (hindex j)
  have hz : (index ⟨0,by omega⟩).val = 0 := by
    have hm : 0 < (ChainThird P).card := by
      have := (index ⟨0,by omega⟩).isLt
      omega
    have he : index ⟨0,by omega⟩ = (⟨0,hm⟩ : Fin ((ChainThird P).card)) := by
      apply hbij'.1
      exact hindex ⟨0,by omega⟩
    exact congrArg Fin.val he
  have hstrict : StrictMono (fun j : Fin (R.length+1) => (index j).val) := by
    intro i j hij
    have hs := arc_run_start_keys_strictMono R hsingle hshort hij
    have hs' : arcKey o first (orbit (α := ThirdVertex P) g first (index i).val) <
        arcKey o first (orbit (α := ThirdVertex P) g first (index j).val) := by
      rw [hstart i,hstart j]
      exact hs
    by_contra hn
    have hle : index j ≤ index i := Nat.le_of_not_gt hn
    exact (not_lt_of_ge (hkeys.monotone hle)) hs'
  have hfinish : ∀ j : Fin (R.length+1),
      (orbit (α := ThirdVertex P) g first ((index j).val+1) : Point) =
        matchEnd P hgp o ho (orbit (chainCycle P hgp o ho) R.first j.val) := by
    intro j
    have he := hedge (orbit (α := ThirdVertex P) g first (index j).val)
    have he' := matchStartEnd_edge P hgp o ho
      (orbit (chainCycle P hgp o ho) R.first j.val)
    change BoundaryEdge (ChainThird P)
      (orbit (α := ThirdVertex P) g first (index j).val)
      (orbit (α := ThirdVertex P) g first ((index j).val+1)) at he
    rw [hstart j] at he
    exact boundaryEdge_right_unique
      (gp_subset hgp ((hullVertices_subset (inner (inner P))).trans
        (Finset.sdiff_subset.trans Finset.sdiff_subset))) he he'
  have hlast : (index ⟨R.length,by omega⟩).val+1 < (ChainThird P).card := by
    have hlt := (index ⟨R.length,by omega⟩).isLt
    by_contra hn
    have heq : (index ⟨R.length,by omega⟩).val+1 = (ChainThird P).card := by omega
    have hh := hfinish ⟨R.length,by omega⟩
    rw [heq,hclose'] at hh
    exact arc_last_end_ne_first_start R hsingle hshort hh.symm
  exact ⟨⟨g,hedge,hreach,hbij',hclose',(fun j => (index j).val),hz,hstrict,hlast,hstart,hfinish⟩⟩

end JSP198.Nicolas

#print axioms JSP198.Nicolas.arcKey_lt_of_clockwise_no_cut
#print axioms JSP198.Nicolas.arcKey_start_lt_of_fan
#print axioms JSP198.Nicolas.arc_run_avoids_cut
#print axioms JSP198.Nicolas.arc_run_start_keys_strictMono
#print axioms JSP198.Nicolas.arc_last_end_ne_first_start
#print axioms JSP198.Nicolas.exists_actual_caseIArc
