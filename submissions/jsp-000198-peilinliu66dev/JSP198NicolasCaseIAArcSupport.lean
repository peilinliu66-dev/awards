/- Released under the MIT license. Support propagation along the actual arc. -/
import JSP198NicolasCaseIAPropagation
import JSP198NicolasCaseIAChord
noncomputable section
open Classical Horton
namespace JSP198.Nicolas

lemma ia_fan_first_support (X a b y z : Point)
    (haby : orient a b y < 0) (habz : orient a b z < 0)
    (hayz : orient a y z < 0) (hXab : orient X a b < 0)
    (hXaz : orient X a z < 0) : orient X a y < 0 := by
  have he : orient X a b * orient a y z - orient X a y * orient a b z +
      orient X a z * orient a b y = 0 := by unfold orient; ring
  by_contra hn
  have hp := mul_pos_of_neg_of_neg hXab hayz
  have hq := mul_nonpos_of_nonneg_of_nonpos (le_of_not_gt hn) habz.le
  have hr := mul_pos_of_neg_of_neg hXaz haby
  linarith only [he,hp,hq,hr]

lemma ia_fan_last_support (X a x c z : Point)
    (haxz : orient a x z < 0) (hacz : orient a c z < 0)
    (hxcz : orient x c z < 0) (hXaz : orient X a z < 0)
    (hXcz : orient X c z < 0) : orient X x z < 0 := by
  have he : orient X x z * orient a c z =
      orient X a z * orient x c z + orient X c z * orient a x z := by unfold orient; ring
  by_contra hn
  have hp := mul_nonpos_of_nonneg_of_nonpos (le_of_not_gt hn) hacz.le
  have hq := mul_pos_of_neg_of_neg hXaz hxcz
  have hr := mul_pos_of_neg_of_neg hXcz haxz
  linarith only [he,hp,hq,hr]

theorem caseI_selected_chord_supported
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (run : ActualCaseIRun P hgp o ho) (arc : ActualCaseIArc run)
    (X : ChainVertex P)
    (hfirst : orient (matchStart P hgp o ho run.first) (matchEnd P hgp o ho run.first) X < 0)
    (hlast : orient (matchStart P hgp o ho run.last) (matchEnd P hgp o ho run.last) X < 0)
    (hchord : orient (matchStart P hgp o ho run.first) (matchEnd P hgp o ho run.last) X < 0)
    (j : ℕ) (hj : j < run.length) :
    orient (matchStart P hgp o ho (orbit (chainCycle P hgp o ho) run.first j))
      (matchStart P hgp o ho (orbit (chainCycle P hgp o ho) run.first (j+1))) X < 0 := by
  let n := (ChainThird P).card
  let qv : ℕ → ThirdVertex P := orbit (α := ThirdVertex P) arc.cycle (sectorVertex P hgp o ho run.first)
  let q : ℕ → Point := fun i => qv i
  let C := arc.index ⟨run.length,by omega⟩
  let i := arc.index ⟨j,by omega⟩
  let l := arc.index ⟨j+1,by omega⟩
  have hC : C+1 < n := arc.last_lt
  have hil : i < l := arc.strictMono (show (⟨j,by omega⟩ : Fin (run.length+1)) < ⟨j+1,by omega⟩ from by change j < j+1; omega)
  have hlC : l ≤ C := arc.strictMono.monotone
    (show (⟨j+1,by omega⟩ : Fin (run.length+1)) ≤ ⟨run.length,by omega⟩ from by change j+1 ≤ run.length; omega)
  have q0 : q 0 = matchStart P hgp o ho run.first := rfl
  have q1 : q 1 = matchEnd P hgp o ho run.first := by
    have hh := arc.finish ⟨0,by omega⟩
    change (arc.cycle (sectorVertex P hgp o ho run.first) : Point) = _
    simpa only [arc.zero,zero_add,orbit] using hh
  have qc : q C = matchStart P hgp o ho run.last := arc.start ⟨run.length,by omega⟩
  have qz : q (C+1) = matchEnd P hgp o ho run.last := arc.finish ⟨run.length,by omega⟩
  have qi : q i = matchStart P hgp o ho (orbit (chainCycle P hgp o ho) run.first j) := arc.start ⟨j,by omega⟩
  have ql : q l = matchStart P hgp o ho (orbit (chainCycle P hgp o ho) run.first (j+1)) := arc.start ⟨j+1,by omega⟩
  have hiq : Function.Injective (fun k : Fin n => q k.val) := by
    intro u v h; exact arc.enumeration.1 (Subtype.ext h)
  have gpQ := gp_subset hgp ((hullVertices_subset (inner (inner P))).trans
    (Finset.sdiff_subset.trans Finset.sdiff_subset))
  have turn := ia_cycle_triple_neg (ChainThird P) (convexIndependent_hullVertices (inner (inner P)))
    gpQ n q (fun k => (qv k).property) (fun k => arc.edge (qv k)) hiq
  have hX1 : orient (X : Point) (q 0) (q 1) < 0 := by
    rw [q0,q1]
    convert hfirst using 1 <;> unfold orient <;> ring
  have hXC : orient (X : Point) (q C) (q (C+1)) < 0 := by
    rw [qc,qz]
    convert hlast using 1 <;> unfold orient <;> ring
  have hXz : orient (X : Point) (q 0) (q (C+1)) < 0 := by
    rw [q0,qz]
    convert hchord using 1 <;> unfold orient <;> ring
  suffices hh : orient (X : Point) (q i) (q l) < 0 by
    rw [qi,ql] at hh
    convert hh using 1 <;> unfold orient <;> ring
  have gpX (u v : ℕ) (hu : u < n) (hv : v < n) (huv : u ≠ v) :
      orient (X : Point) (q u) (q v) ≠ 0 := by
    have huI := chain_third_mem_inner2 (qv u).property
    have hvI := chain_third_mem_inner2 (qv v).property
    have hneq : q u ≠ q v := by
      intro he
      have hh : (⟨u,hu⟩ : Fin n) = ⟨v,hv⟩ := hiq he
      exact huv (congrArg Fin.val hh)
    exact (gp_subset hgp Finset.sdiff_subset) X (chain_second_mem_inner X)
      (q u) (Finset.sdiff_subset huI) (q v) (Finset.sdiff_subset hvI)
      (chain_inner2_ne_second huI X).symm (chain_inner2_ne_second hvI X).symm hneq
  by_cases hi0 : i = 0
  · rw [hi0]
    by_cases hl1 : l = 1
    · simpa only [hl1] using hX1
    · exact ia_fan_first_support X (q 0) (q 1) (q l) (q (C+1))
        (turn 0 1 l (by omega) (by omega) (by omega))
        (turn 0 1 (C+1) (by omega) (by omega) hC)
        (turn 0 l (C+1) (by omega) (by omega) hC) hX1 hXz
  · by_contra hn
    have hbad : 0 < orient (X : Point) (q i) (q l) :=
      lt_of_le_of_ne (le_of_not_gt hn) (gpX i l (by omega) (by omega) (by omega)).symm
    apply ia_arc_support_propagation_certificate X (q 0) (q 1) (q i) (q l) (q C) (q (C+1))
      (turn 0 1 l (by omega) (by omega) (by omega))
      (turn 0 1 C (by omega) (by omega) (by omega))
      (turn 0 1 (C+1) (by omega) (by omega) hC)
      (turn 0 i l (by omega) hil (by omega))
      (by
        have hh := turn 0 i C (by omega) (by omega) (by omega)
        have he : orient (q 0) (q C) (q i) = -orient (q 0) (q i) (q C) := by unfold orient; ring
        rw [he]; linarith)
      (turn 0 i (C+1) (by omega) (by omega) hC)
      (turn 0 l (C+1) (by omega) (by omega) hC)
      (turn 0 C (C+1) (by omega) (by omega) hC)
      (turn i l (C+1) hil (by omega) hC)
      (by
        have hh := turn i C (C+1) (by omega) (by omega) hC
        have he : orient (q C) (q i) (q (C+1)) = -orient (q i) (q C) (q (C+1)) := by unfold orient; ring
        rw [he]; linarith)
      hX1 hXC hXz hbad (gpX 0 C (by omega) (by omega) (by omega))
      (gpX 0 i (by omega) (by omega) (by omega))
      (gpX 0 l (by omega) (by omega) (by omega))
      (gpX C i (by omega) (by omega) (by omega))
      (gpX i (C+1) (by omega) hC (by omega))

end JSP198.Nicolas
#print axioms JSP198.Nicolas.caseI_selected_chord_supported
