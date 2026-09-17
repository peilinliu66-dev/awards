/-
Released under the MIT license.
Actual supporting edges of the Case I.A sampled replacement.
All pointwise support inputs are derived from the actual run and its real arc.
-/
import JSP198NicolasCaseIAArcSupport
import JSP198NicolasCaseIAEndpointsB
import JSP198NicolasCaseIAOuterJoin
import JSP198NicolasSampledCapAssembly

noncomputable section
open Classical Horton
namespace JSP198.Nicolas
open PartialCover SampledCapAssembly

private lemma sampled_entry_fan (q : ℕ → Point) (n C : ℕ) (X : Point)
    (hC : C+1 < n)
    (turn : ∀ i j k, i < j → j < k → k < n → orient (q i) (q j) (q k) < 0)
    (hfirst : orient X (q 0) (q 1) < 0)
    (hwhole : orient X (q 0) (q (C+1)) < 0)
    (i : ℕ) (hi : i ≤ C) : orient X (q 0) (q i) ≤ 0 := by
  by_cases h0 : i = 0
  · subst i; unfold orient; ring_nf; exact le_rfl
  by_cases h1 : i = 1
  · subst i; exact hfirst.le
  exact (ia_fan_first_support X (q 0) (q 1) (q i) (q (C+1))
    (turn 0 1 i (by omega) (by omega) (by omega))
    (turn 0 1 (C+1) (by omega) (by omega) hC)
    (turn 0 i (C+1) (by omega) (by omega) hC) hfirst hwhole).le

private lemma sampled_exit_fan (q : ℕ → Point) (n C : ℕ) (X : Point)
    (hC : C+1 < n)
    (turn : ∀ i j k, i < j → j < k → k < n → orient (q i) (q j) (q k) < 0)
    (hlast : orient X (q C) (q (C+1)) < 0)
    (hwhole : orient X (q 0) (q (C+1)) < 0)
    (i : ℕ) (hi : i ≤ C) : orient X (q i) (q (C+1)) ≤ 0 := by
  by_cases h0 : i = 0
  · subst i; exact hwhole.le
  by_cases hc : i = C
  · subst i; exact hlast.le
  exact (ia_fan_last_support X (q 0) (q i) (q C) (q (C+1))
    (turn 0 i (C+1) (by omega) (by omega) hC)
    (turn 0 C (C+1) (by omega) (by omega) hC)
    (turn i C (C+1) (by omega) (by omega) hC) hwhole hlast).le

variable {P : Finset Point} {hgp : GeneralPosition P}
  {o : Point} {ho : o ∈ inner (inner (inner P))}

private lemma sampled_match_edge_orient_ne (r X : ChainVertex P) :
    orient (matchStart P hgp o ho r) (matchEnd P hgp o ho r) X ≠ 0 := by
  have ha := matchStart_mem P hgp o ho r
  have hb := matchEnd_mem P hgp o ho r
  have he := matchStartEnd_edge P hgp o ho r
  exact (gp_subset hgp Finset.sdiff_subset)
    _ (Finset.sdiff_subset ha) _ (Finset.sdiff_subset hb) X (chain_second_mem_inner X)
    he.2.2.1 (chain_inner2_ne_second ha X) (chain_inner2_ne_second hb X)

/-- All four actual edge families support every actual sampled vertex. -/
theorem caseIA_sampled_edge_support
    (run : ActualCaseIRun P hgp o ho) (hsingle : RunHasSingletonSectors run)
    (hshort : run.length+3 ≤ (ChainSecond P).card) : SampledEdgeSupport run := by
  let arc := Classical.choice (exists_actual_caseIArc P hgp o ho run hsingle (by omega))
  let A : ChainVertex P := beforeRun run
  let B : ChainVertex P := afterRun run
  let a : ℕ → Point := runStart run
  let z := runEnd run run.length
  have hAf : orient (a 0) (runEnd run 0) A < 0 :=
    lt_of_le_of_ne (le_of_not_gt run.noLeft) (sampled_match_edge_orient_ne run.first A)
  have hAl : orient (a run.length) z A < 0 :=
    caseIA_first_outer_supports_last_edge run hsingle hshort
  have hAw : orient (a 0) z A < 0 :=
    caseIA_first_outer_supports_arc_chord run hsingle hshort
  have hBf : orient (a 0) (runEnd run 0) B < 0 :=
    caseIA_last_outer_supports_first_edge run hsingle hshort
  have hBl : orient (a run.length) z B < 0 :=
    lt_of_le_of_ne (le_of_not_gt run.noRight_end) (sampled_match_edge_orient_ne run.last B)
  have hBw : orient (a 0) z B < 0 :=
    caseIA_last_outer_supports_arc_chord run hsingle hshort
  have hjoin := caseIA_outer_join_support run hsingle hshort
  let n := (ChainThird P).card
  let qv : ℕ → ThirdVertex P := orbit (α := ThirdVertex P) arc.cycle (sectorVertex P hgp o ho run.first)
  let q : ℕ → Point := fun i => qv i
  let C := arc.index ⟨run.length,by omega⟩
  have hC : C+1 < n := arc.last_lt
  have q0 : q 0 = a 0 := rfl
  have q1 : q 1 = runEnd run 0 := by
    have hh := arc.finish ⟨0,by omega⟩
    change (arc.cycle (sectorVertex P hgp o ho run.first) : Point) = matchEnd P hgp o ho run.first
    simpa only [arc.zero,zero_add,orbit] using hh
  have qc : q C = a run.length := arc.start ⟨run.length,by omega⟩
  have qz : q (C+1) = z := arc.finish ⟨run.length,by omega⟩
  have qa (j : Fin (run.length+1)) : q (arc.index j) = a j.val := arc.start j
  have idx_le (j : Fin (run.length+1)) : arc.index j ≤ C :=
    arc.strictMono.monotone (show j ≤ ⟨run.length,by omega⟩ from Nat.le_of_lt_succ j.isLt)
  have hiq : Function.Injective (fun k : Fin n => q k.val) := by
    intro u v h; exact arc.enumeration.1 (Subtype.ext h)
  have gpQ := gp_subset hgp ((hullVertices_subset (inner (inner P))).trans
    (Finset.sdiff_subset.trans Finset.sdiff_subset))
  have turn := ia_cycle_triple_neg (ChainThird P) (convexIndependent_hullVertices (inner (inner P)))
    gpQ n q (fun k => (qv k).property) (fun k => arc.edge (qv k)) hiq
  have entry (j : Fin (run.length+1)) : orient (A : Point) (a 0) (a j.val) ≤ 0 := by
    have hf : orient (A : Point) (q 0) (q 1) < 0 := by
      rw [q0,q1]; convert hAf using 1 <;> unfold orient <;> ring
    have hw : orient (A : Point) (q 0) (q (C+1)) < 0 := by
      rw [q0,qz]; convert hAw using 1 <;> unfold orient <;> ring
    simpa only [q0,qa] using sampled_entry_fan q n C A hC turn hf hw (arc.index j) (idx_le j)
  have exit (j : Fin (run.length+1)) : orient z (B : Point) (a j.val) ≤ 0 := by
    have hl : orient (B : Point) (q C) (q (C+1)) < 0 := by
      rw [qc,qz]; convert hBl using 1 <;> unfold orient <;> ring
    have hw : orient (B : Point) (q 0) (q (C+1)) < 0 := by
      rw [q0,qz]; convert hBw using 1 <;> unfold orient <;> ring
    have hh := sampled_exit_fan q n C B hC turn hl hw (arc.index j) (idx_le j)
    rw [qa,qz] at hh
    convert hh using 1 <;> unfold orient <;> ring
  have chords (j : ℕ) (hj : j < run.length) (t : Fin (run.length+1)) :
      orient (a j) (a (j+1)) (a t.val) ≤ 0 := by
    let u : Fin (run.length+1) := ⟨j,by omega⟩
    let v : Fin (run.length+1) := ⟨j+1,by omega⟩
    have huv : arc.index u < arc.index v := arc.strictMono (by change j < j+1; omega)
    have hu := idx_le u
    have hv := idx_le v
    have ht := idx_le t
    have eq_u : q (arc.index u) = a j := qa u
    have eq_v : q (arc.index v) = a (j+1) := qa v
    by_cases htu : t.val = j
    · rw [htu]; unfold orient; ring_nf; exact le_rfl
    by_cases htv : t.val = j+1
    · rw [htv]; unfold orient; ring_nf; exact le_rfl
    by_cases htj : t.val < j
    · have htu' : arc.index t < arc.index u := arc.strictMono (by change t.val < j; exact htj)
      have hh := turn (arc.index t) (arc.index u) (arc.index v) htu' huv (by omega)
      rw [qa,eq_u,eq_v] at hh
      have he : orient (a j) (a (j+1)) (a t.val) = orient (a t.val) (a j) (a (j+1)) := by unfold orient; ring
      rw [he]; exact hh.le
    · have hvt : arc.index v < arc.index t := arc.strictMono (by change j+1 < t.val; omega)
      have hh := turn (arc.index u) (arc.index v) (arc.index t) huv hvt (by omega)
      rw [eq_u,eq_v,qa] at hh
      exact hh.le
  have chords_z (j : ℕ) (hj : j < run.length) : orient (a j) (a (j+1)) z ≤ 0 := by
    let u : Fin (run.length+1) := ⟨j,by omega⟩
    let v : Fin (run.length+1) := ⟨j+1,by omega⟩
    have huv : arc.index u < arc.index v := arc.strictMono (by change j < j+1; omega)
    have hv := idx_le v
    have hh := turn (arc.index u) (arc.index v) (C+1) huv (by omega) hC
    simpa only [qa,qz] using hh.le
  have last_starts (t : Fin (run.length+1)) : orient (a run.length) z (a t.val) ≤ 0 := by
    exact (matchStartEnd_edge P hgp o ho run.last).2.2.2 _
      (matchStartEnd_edge P hgp o ho (orbit (chainCycle P hgp o ho) run.first t.val)).1
  intro u v he x hx
  have hx' : x = (A : Point) ∨ x = (B : Point) ∨ x = z ∨
      ∃ t : Fin (run.length+1), x = a t.val := by
    change x ∈ insert (A : Point) (insert (B : Point) (insert z (caseIStarts run))) at hx
    simp only [Finset.mem_insert] at hx
    rcases hx with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · obtain ⟨t,_,ht⟩ := Finset.mem_image.mp h
      exact Or.inr (Or.inr (Or.inr ⟨t,ht.symm⟩))
  rcases he with ⟨rfl,rfl⟩ | ⟨j,hj,rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · change orient (A : Point) (a 0) x ≤ 0
    rcases hx' with rfl | rfl | rfl | ⟨t,rfl⟩
    · unfold orient; ring_nf; exact le_rfl
    · exact hjoin.1.le
    · have he : orient (A : Point) (a 0) z = orient (a 0) z A := by unfold orient; ring
      rw [he]; exact hAw.le
    · exact entry t
  · change orient (a j) (a (j+1)) x ≤ 0
    rcases hx' with rfl | rfl | rfl | ⟨t,rfl⟩
    · exact (caseI_selected_chord_supported run arc A hAf hAl hAw j hj).le
    · exact (caseI_selected_chord_supported run arc B hBf hBl hBw j hj).le
    · exact chords_z j hj
    · exact chords j hj t
  · change orient (a run.length) z x ≤ 0
    rcases hx' with rfl | rfl | rfl | ⟨t,rfl⟩
    · exact hAl.le
    · exact hBl.le
    · unfold orient; ring_nf; exact le_rfl
    · exact last_starts t
  · change orient z (B : Point) x ≤ 0
    rcases hx' with rfl | rfl | rfl | ⟨t,rfl⟩
    · exact hjoin.2.le
    · unfold orient; ring_nf; exact le_rfl
    · unfold orient; ring_nf; exact le_rfl
    · exact exit t

end JSP198.Nicolas
#print axioms JSP198.Nicolas.caseIA_sampled_edge_support
