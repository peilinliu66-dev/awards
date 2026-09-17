/- Released under the MIT license. Actual B endpoint bridges. -/
import JSP198NicolasCaseIABCertificates
set_option maxHeartbeats 1600000
noncomputable section
open Classical Horton
namespace JSP198.Nicolas
theorem caseIA_last_outer_supports_first_edge
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (run : ActualCaseIRun P hgp o ho) (hsingle : RunHasSingletonSectors run)
    (hshort : run.length+3 ≤ (ChainSecond P).card) :
    orient (matchStart P hgp o ho run.first)
      (matchEnd P hgp o ho run.first)
      (chainCycle P hgp o ho run.last : Point) < 0 := by
  let f := chainCycle P hgp o ho
  let A : ChainVertex P := f.symm run.first
  let R : ChainVertex P := run.first
  let K : ChainVertex P := run.last
  let B : ChainVertex P := f K
  let a := matchStart P hgp o ho R
  let b := matchEnd P hgp o ho R
  let c := matchStart P hgp o ho K
  let z := matchEnd P hgp o ho K
  have hgI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hgQ := gp_subset hgp ((hullVertices_subset (inner (inner P))).trans
    (Finset.sdiff_subset.trans Finset.sdiff_subset))
  have ea : BoundaryEdge (ChainThird P) a b := matchStartEnd_edge P hgp o ho R
  have ec : BoundaryEdge (ChainThird P) c z := matchStartEnd_edge P hgp o ho K
  have eaI := matchStart_mem P hgp o ho R
  have ebI := matchEnd_mem P hgp o ho R
  have ecI := matchStart_mem P hgp o ho K
  have ezI := matchEnd_mem P hgp o ho K
  have eoI := (Finset.mem_sdiff.mp ho).1
  have ni (x : Point) (hx : x ∈ inner (inner P)) (r : ChainVertex P) : x ≠ (r : Point) :=
    chain_inner2_ne_second hx r
  have nac : a ≠ c := by
    intro hh
    have he := sectorEdge_eq_of_sectorVertex_eq P hgp o ho K R (Subtype.ext hh.symm)
    have hsame := hsingle 0 (Nat.zero_le _) K he
    exact run.first_ne_last hsame.symm
  have nza : z ≠ a := arc_last_end_ne_first_start run hsingle (by omega)
  have nzb : z ≠ b := by
    intro hh
    have ee := ec
    rw [hh] at ee
    exact nac (boundaryEdge_left_unique hgQ ea ee)
  have nao : a ≠ o := by
    intro hh
    exact (Finset.mem_sdiff.mp ho).2 (by rw [← hh]; exact ea.1)
  let qv : ℕ → ChainVertex P := orbit (α := ChainVertex P) f A
  let q : ℕ → Point := fun i => qv i
  have qs (i : ℕ) : qv (i+1) = orbit (α := ChainVertex P) f R i := by
    induction i with
    | zero => simp only [qv,orbit,A,R,Equiv.apply_symm_apply]
    | succ i ih => change f (qv (i+1)) = f (orbit (α := ChainVertex P) f R i); rw [ih]
  have q0 : q 0 = A := rfl
  have q1 : q 1 = R := congrArg (fun r : ChainVertex P => (r : Point)) (qs 0)
  have qk : q (run.length+1) = K := congrArg (fun r : ChainVertex P => (r : Point)) (qs run.length)
  have qb : q (run.length+2) = B := by
    change (f (qv (run.length+1)) : Point) = B
    rw [qs]
    rfl
  have hi : Function.Injective (fun i : Fin ((ChainSecond P).card) => q i.val) := by
    intro i j hh
    exact (ib_full_cycle_enumeration P hgp o ho A).1 (Subtype.ext hh)
  have turn := ia_cycle_triple_neg (ChainSecond P)
    (convexIndependent_hullVertices (inner P))
    (gp_subset hgp ((hullVertices_subset (inner P)).trans Finset.sdiff_subset))
    (ChainSecond P).card q (fun i => (qv i).property)
    (fun i => chainCycle_edge P hgp o ho (qv i)) hi
  have hpos := run.positive
  have tARK : orient (A : Point) R K < 0 := by
    simpa only [q0,q1,qk] using turn 0 1 (run.length+1) (by omega) (by omega) (by omega)
  have tARB : orient (A : Point) R B < 0 := by
    simpa only [q0,q1,qb] using turn 0 1 (run.length+2) (by omega) (by omega) (by omega)
  have tAKB : orient (A : Point) K B < 0 := by
    simpa only [q0,qk,qb] using turn 0 (run.length+1) (run.length+2) (by omega) (by omega) (by omega)
  have tRKB : orient (R : Point) K B < 0 := by
    simpa only [q1,qk,qb] using turn 1 (run.length+1) (run.length+2) (by omega) (by omega) (by omega)
  have nAK : (A : Point) ≠ K := by intro h; rw [h] at tARK; unfold orient at tARK; nlinarith
  have nAB : (A : Point) ≠ B := by intro h; rw [h] at tARB; unfold orient at tARB; nlinarith
  have nKR : (K : Point) ≠ R := by intro h; rw [h] at tARK; unfold orient at tARK; nlinarith
  have eAR : BoundaryEdge (ChainSecond P) A R := by
    have ee := chainCycle_edge P hgp o ho A
    simpa only [A,f,R,Equiv.apply_symm_apply] using ee
  have eKB : BoundaryEdge (ChainSecond P) K B := chainCycle_edge P hgp o ho K
  have left (x : Point) (hx : x ∈ inner (inner P)) : orient (A : Point) R x < 0 := by
    have hh := boundaryEdge_inner_strict (inner P) hgI x hx A R eAR
    convert hh using 1 <;> unfold orient <;> ring
  have right (x : Point) (hx : x ∈ inner (inner P)) : orient (K : Point) B x < 0 := by
    have hh := boundaryEdge_inner_strict (inner P) hgI x hx K B eKB
    convert hh using 1 <;> unfold orient <;> ring
  have memS (r : ChainVertex P) : (r : Point) ∈ inner P := chain_second_mem_inner r
  have memI (x : Point) (hx : x ∈ inner (inner P)) : x ∈ inner P := Finset.sdiff_subset hx
  have gpSII (r s : ChainVertex P) (x : Point) (hrs : (r : Point) ≠ s)
      (hx : x ∈ inner (inner P)) : orient (r : Point) s x ≠ 0 :=
    hgI r (memS r) s (memS s) x (memI x hx) hrs (ni x hx r).symm (ni x hx s).symm
  have gpSII2 (r : ChainVertex P) (x y : Point)
      (hx : x ∈ inner (inner P)) (hy : y ∈ inner (inner P)) (hxy : x ≠ y) :
      orient (r : Point) x y ≠ 0 :=
    hgI r (memS r) x (memI x hx) y (memI y hy) (ni x hx r).symm (ni y hy r).symm hxy
  have nAaB : orient (A : Point) a b ≠ 0 := gpSII2 A a b eaI ebI ea.2.2.1
  have nBcz : orient (B : Point) c z ≠ 0 := gpSII2 B c z ecI ezI ec.2.2.1
  have noL : orient (A : Point) a b < 0 := by
    have hh : orient a b (A : Point) ≤ 0 := le_of_not_gt run.noLeft
    have he : orient (A : Point) a b = orient a b A := by unfold orient; ring
    exact lt_of_le_of_ne (by rwa [he]) nAaB
  have noR : orient (B : Point) c z < 0 := by
    have hh : orient c z (B : Point) ≤ 0 := le_of_not_gt run.noRight_end
    have he : orient (B : Point) c z = orient c z B := by unfold orient; ring
    exact lt_of_le_of_ne (by rwa [he]) nBcz
  have hf := arc_cut_in_incoming_edge run hsingle
  have hfR : InFan o a b R := sectorEdge_inFan P hgp o ho R
  have hfK : InFan o K B z := previous_sector_end_in_swept_edge P hgp o ho K
    (arc_run_changes run hsingle run.length le_rfl)
  have ownR : 0 < orient (R : Point) a b := by
    have hh := sectorEdge_outward P hgp o ho R
    change 0 < orient a b R at hh
    convert hh using 1 <;> unfold orient <;> ring
  have ownK : 0 < orient (K : Point) c z := by
    have hh := sectorEdge_outward P hgp o ho K
    change 0 < orient c z K at hh
    convert hh using 1 <;> unfold orient <;> ring
  have rao : 0 < orient (R : Point) a o := by
    convert hfR.1 using 1 <;> unfold orient <;> ring
  have aao : orient (A : Point) a o < 0 := by
    have hh : 0 < orient (A : Point) o a := hf.1
    have he : orient (A : Point) a o = -orient (A : Point) o a := by unfold orient; ring
    rw [he]; linarith
  have abz : orient a b z < 0 := ea.strict hgQ ec.2.1 nza nzb
  have acz : orient a c z < 0 := by
    have hh := ec.strict hgQ ea.1 nac nza.symm
    convert hh using 1 <;> unfold orient <;> ring
  have abo : orient a b o < 0 := by
    have hh := boundaryEdge_inner_strict (inner (inner P))
      (gp_subset hgI Finset.sdiff_subset) o ho a b ea
    convert hh using 1 <;> unfold orient <;> ring
  have boz : orient (B : Point) o z < 0 := by
    have hh := hfK.2
    have he : orient (B : Point) o z = -orient o B z := by unfold orient; ring
    rw [he]; linarith
  have nBR : (B : Point) ≠ R := by
    intro hh; rw [hh] at tARB; unfold orient at tARB; nlinarith

  change orient a b (B : Point) < 0
  have nz : orient a b (B : Point) ≠ 0 := by
    have hh := gpSII2 B a b eaI ebI ea.2.2.1
    convert hh using 1 <;> unfold orient <;> ring
  by_contra hn
  have hbad : 0 < orient (B : Point) a b := by
    have hh : 0 < orient a b (B : Point) := lt_of_le_of_ne (le_of_not_gt hn) nz.symm
    convert hh using 1 <;> unfold orient <;> ring
  have h8 : 0 < orient A K R := by
    have hh : orient A R K < 0 := tARK
    have he : orient A K R = -(orient A R K) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h2 : 0 < orient A B R := by
    have hh : orient A R B < 0 := tARB
    have he : orient A B R = -(orient A R B) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h1 : 0 < orient A B K := by
    have hh : orient A K B < 0 := tAKB
    have he : orient A B K = -(orient A K B) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h29 : 0 < orient B K R := by
    have hh : orient R K B < 0 := tRKB
    have he : orient B K R = -(orient R K B) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h77 : orient a b z < 0 := by
    have hh : orient a b z < 0 := abz
    have he : orient a b z = (orient a b z) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h79 : orient a c z < 0 := by
    have hh : orient a c z < 0 := acz
    have he : orient a c z = (orient a c z) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h14 : orient A R a < 0 := by
    have hh : orient A R a < 0 := (left a eaI)
    have he : orient A R a = (orient A R a) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h16 : orient A R c < 0 := by
    have hh : orient A R c < 0 := (left c ecI)
    have he : orient A R c = (orient A R c) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h18 : orient A R z < 0 := by
    have hh : orient A R z < 0 := (left z ezI)
    have he : orient A R z = (orient A R z) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h17 : orient A R o < 0 := by
    have hh : orient A R o < 0 := (left o eoI)
    have he : orient A R o = (orient A R o) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h30 : 0 < orient B K a := by
    have hh : orient K B a < 0 := (right a eaI)
    have he : orient B K a = -(orient K B a) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h32 : 0 < orient B K c := by
    have hh : orient K B c < 0 := (right c ecI)
    have he : orient B K c = -(orient K B c) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h34 : 0 < orient B K z := by
    have hh : orient K B z < 0 := (right z ezI)
    have he : orient B K z = -(orient K B z) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h33 : 0 < orient B K o := by
    have hh : orient K B o < 0 := (right o eoI)
    have he : orient B K o = -(orient K B o) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h67 : 0 < orient R a o := by
    have hh : 0 < orient R a o := rao
    have he : orient R a o = (orient R a o) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h65 : 0 < orient R a b := by
    have hh : 0 < orient R a b := ownR
    have he : orient R a b = (orient R a b) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h76 : orient a b o < 0 := by
    have hh : orient a b o < 0 := abo
    have he : orient a b o = (orient a b o) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h64 : 0 < orient K o z := by
    have hh : 0 < orient K o z := hfK.1
    have he : orient K o z = (orient K o z) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h63 : 0 < orient K c z := by
    have hh : 0 < orient K c z := ownK
    have he : orient K c z = (orient K c z) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h21 : orient A a o < 0 := by
    have hh : orient A a o < 0 := aao
    have he : orient A a o = (orient A a o) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h19 : orient A a b < 0 := by
    have hh : orient A a b < 0 := noL
    have he : orient A a b = (orient A a b) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h48 : orient B c z < 0 := by
    have hh : orient B c z < 0 := noR
    have he : orient B c z = (orient B c z) := by unfold orient; ring
    rw [he]; linarith only [hh]
  exact ia_nine_point_bfirst_certificate A R K B a b c z o
    h8
    h2
    h1
    h29
    h77
    h79
    h14
    h16
    h18
    h17
    h30
    h32
    h34
    h33
    h67
    h65
    h76
    h64
    h63
    h21
    h19
    h48
    hbad
    (gpSII A B a nAB eaI)
    (gpSII A B c nAB ecI)
    (gpSII A B z nAB ezI)
    (gpSII A K a nAK eaI)
    (gpSII A K c nAK ecI)
    (gpSII A K o nAK eoI)
    (gpSII A K z nAK ezI)
    (gpSII2 A a c eaI ecI nac)
    (gpSII2 A a z eaI ezI nza.symm)
    (gpSII2 A c z ecI ezI ec.2.2.1)
    (gpSII2 B a c eaI ecI nac)
    (gpSII2 B a z eaI ezI nza.symm)
    (gpSII K R a nKR eaI)
    (gpSII K R c nKR ecI)
    (gpSII K R o nKR eoI)
    (gpSII K R z nKR ezI)
    (gpSII2 K a b eaI ebI ea.2.2.1)
    (gpSII2 K a c eaI ecI nac)
    (gpSII2 K a o eaI eoI nao)
    (gpSII2 K a z eaI ezI nza.symm)
    (gpSII2 R a z eaI ezI nza.symm)
theorem caseIA_last_outer_supports_arc_chord
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (run : ActualCaseIRun P hgp o ho) (hsingle : RunHasSingletonSectors run)
    (hshort : run.length+3 ≤ (ChainSecond P).card) :
    orient (matchStart P hgp o ho run.first)
      (matchEnd P hgp o ho run.last)
      (chainCycle P hgp o ho run.last : Point) < 0 := by
  let f := chainCycle P hgp o ho
  let A : ChainVertex P := f.symm run.first
  let R : ChainVertex P := run.first
  let K : ChainVertex P := run.last
  let B : ChainVertex P := f K
  let a := matchStart P hgp o ho R
  let b := matchEnd P hgp o ho R
  let c := matchStart P hgp o ho K
  let z := matchEnd P hgp o ho K
  have hgI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hgQ := gp_subset hgp ((hullVertices_subset (inner (inner P))).trans
    (Finset.sdiff_subset.trans Finset.sdiff_subset))
  have ea : BoundaryEdge (ChainThird P) a b := matchStartEnd_edge P hgp o ho R
  have ec : BoundaryEdge (ChainThird P) c z := matchStartEnd_edge P hgp o ho K
  have eaI := matchStart_mem P hgp o ho R
  have ebI := matchEnd_mem P hgp o ho R
  have ecI := matchStart_mem P hgp o ho K
  have ezI := matchEnd_mem P hgp o ho K
  have eoI := (Finset.mem_sdiff.mp ho).1
  have ni (x : Point) (hx : x ∈ inner (inner P)) (r : ChainVertex P) : x ≠ (r : Point) :=
    chain_inner2_ne_second hx r
  have nac : a ≠ c := by
    intro hh
    have he := sectorEdge_eq_of_sectorVertex_eq P hgp o ho K R (Subtype.ext hh.symm)
    have hsame := hsingle 0 (Nat.zero_le _) K he
    exact run.first_ne_last hsame.symm
  have nza : z ≠ a := arc_last_end_ne_first_start run hsingle (by omega)
  have nzb : z ≠ b := by
    intro hh
    have ee := ec
    rw [hh] at ee
    exact nac (boundaryEdge_left_unique hgQ ea ee)
  have nao : a ≠ o := by
    intro hh
    exact (Finset.mem_sdiff.mp ho).2 (by rw [← hh]; exact ea.1)
  let qv : ℕ → ChainVertex P := orbit (α := ChainVertex P) f A
  let q : ℕ → Point := fun i => qv i
  have qs (i : ℕ) : qv (i+1) = orbit (α := ChainVertex P) f R i := by
    induction i with
    | zero => simp only [qv,orbit,A,R,Equiv.apply_symm_apply]
    | succ i ih => change f (qv (i+1)) = f (orbit (α := ChainVertex P) f R i); rw [ih]
  have q0 : q 0 = A := rfl
  have q1 : q 1 = R := congrArg (fun r : ChainVertex P => (r : Point)) (qs 0)
  have qk : q (run.length+1) = K := congrArg (fun r : ChainVertex P => (r : Point)) (qs run.length)
  have qb : q (run.length+2) = B := by
    change (f (qv (run.length+1)) : Point) = B
    rw [qs]
    rfl
  have hi : Function.Injective (fun i : Fin ((ChainSecond P).card) => q i.val) := by
    intro i j hh
    exact (ib_full_cycle_enumeration P hgp o ho A).1 (Subtype.ext hh)
  have turn := ia_cycle_triple_neg (ChainSecond P)
    (convexIndependent_hullVertices (inner P))
    (gp_subset hgp ((hullVertices_subset (inner P)).trans Finset.sdiff_subset))
    (ChainSecond P).card q (fun i => (qv i).property)
    (fun i => chainCycle_edge P hgp o ho (qv i)) hi
  have hpos := run.positive
  have tARK : orient (A : Point) R K < 0 := by
    simpa only [q0,q1,qk] using turn 0 1 (run.length+1) (by omega) (by omega) (by omega)
  have tARB : orient (A : Point) R B < 0 := by
    simpa only [q0,q1,qb] using turn 0 1 (run.length+2) (by omega) (by omega) (by omega)
  have tAKB : orient (A : Point) K B < 0 := by
    simpa only [q0,qk,qb] using turn 0 (run.length+1) (run.length+2) (by omega) (by omega) (by omega)
  have tRKB : orient (R : Point) K B < 0 := by
    simpa only [q1,qk,qb] using turn 1 (run.length+1) (run.length+2) (by omega) (by omega) (by omega)
  have nAK : (A : Point) ≠ K := by intro h; rw [h] at tARK; unfold orient at tARK; nlinarith
  have nAB : (A : Point) ≠ B := by intro h; rw [h] at tARB; unfold orient at tARB; nlinarith
  have nKR : (K : Point) ≠ R := by intro h; rw [h] at tARK; unfold orient at tARK; nlinarith
  have eAR : BoundaryEdge (ChainSecond P) A R := by
    have ee := chainCycle_edge P hgp o ho A
    simpa only [A,f,R,Equiv.apply_symm_apply] using ee
  have eKB : BoundaryEdge (ChainSecond P) K B := chainCycle_edge P hgp o ho K
  have left (x : Point) (hx : x ∈ inner (inner P)) : orient (A : Point) R x < 0 := by
    have hh := boundaryEdge_inner_strict (inner P) hgI x hx A R eAR
    convert hh using 1 <;> unfold orient <;> ring
  have right (x : Point) (hx : x ∈ inner (inner P)) : orient (K : Point) B x < 0 := by
    have hh := boundaryEdge_inner_strict (inner P) hgI x hx K B eKB
    convert hh using 1 <;> unfold orient <;> ring
  have memS (r : ChainVertex P) : (r : Point) ∈ inner P := chain_second_mem_inner r
  have memI (x : Point) (hx : x ∈ inner (inner P)) : x ∈ inner P := Finset.sdiff_subset hx
  have gpSII (r s : ChainVertex P) (x : Point) (hrs : (r : Point) ≠ s)
      (hx : x ∈ inner (inner P)) : orient (r : Point) s x ≠ 0 :=
    hgI r (memS r) s (memS s) x (memI x hx) hrs (ni x hx r).symm (ni x hx s).symm
  have gpSII2 (r : ChainVertex P) (x y : Point)
      (hx : x ∈ inner (inner P)) (hy : y ∈ inner (inner P)) (hxy : x ≠ y) :
      orient (r : Point) x y ≠ 0 :=
    hgI r (memS r) x (memI x hx) y (memI y hy) (ni x hx r).symm (ni y hy r).symm hxy
  have nAaB : orient (A : Point) a b ≠ 0 := gpSII2 A a b eaI ebI ea.2.2.1
  have nBcz : orient (B : Point) c z ≠ 0 := gpSII2 B c z ecI ezI ec.2.2.1
  have noL : orient (A : Point) a b < 0 := by
    have hh : orient a b (A : Point) ≤ 0 := le_of_not_gt run.noLeft
    have he : orient (A : Point) a b = orient a b A := by unfold orient; ring
    exact lt_of_le_of_ne (by rwa [he]) nAaB
  have noR : orient (B : Point) c z < 0 := by
    have hh : orient c z (B : Point) ≤ 0 := le_of_not_gt run.noRight_end
    have he : orient (B : Point) c z = orient c z B := by unfold orient; ring
    exact lt_of_le_of_ne (by rwa [he]) nBcz
  have hf := arc_cut_in_incoming_edge run hsingle
  have hfR : InFan o a b R := sectorEdge_inFan P hgp o ho R
  have hfK : InFan o K B z := previous_sector_end_in_swept_edge P hgp o ho K
    (arc_run_changes run hsingle run.length le_rfl)
  have ownR : 0 < orient (R : Point) a b := by
    have hh := sectorEdge_outward P hgp o ho R
    change 0 < orient a b R at hh
    convert hh using 1 <;> unfold orient <;> ring
  have ownK : 0 < orient (K : Point) c z := by
    have hh := sectorEdge_outward P hgp o ho K
    change 0 < orient c z K at hh
    convert hh using 1 <;> unfold orient <;> ring
  have rao : 0 < orient (R : Point) a o := by
    convert hfR.1 using 1 <;> unfold orient <;> ring
  have aao : orient (A : Point) a o < 0 := by
    have hh : 0 < orient (A : Point) o a := hf.1
    have he : orient (A : Point) a o = -orient (A : Point) o a := by unfold orient; ring
    rw [he]; linarith
  have abz : orient a b z < 0 := ea.strict hgQ ec.2.1 nza nzb
  have acz : orient a c z < 0 := by
    have hh := ec.strict hgQ ea.1 nac nza.symm
    convert hh using 1 <;> unfold orient <;> ring
  have abo : orient a b o < 0 := by
    have hh := boundaryEdge_inner_strict (inner (inner P))
      (gp_subset hgI Finset.sdiff_subset) o ho a b ea
    convert hh using 1 <;> unfold orient <;> ring
  have boz : orient (B : Point) o z < 0 := by
    have hh := hfK.2
    have he : orient (B : Point) o z = -orient o B z := by unfold orient; ring
    rw [he]; linarith
  have nBR : (B : Point) ≠ R := by
    intro hh; rw [hh] at tARB; unfold orient at tARB; nlinarith

  change orient a z (B : Point) < 0
  have nz : orient a z (B : Point) ≠ 0 := by
    have hh := gpSII2 B a z eaI ezI nza.symm
    convert hh using 1 <;> unfold orient <;> ring
  by_contra hn
  have hbad : 0 < orient (B : Point) a z := by
    have hh : 0 < orient a z (B : Point) := lt_of_le_of_ne (le_of_not_gt hn) nz.symm
    convert hh using 1 <;> unfold orient <;> ring
  have h8 : 0 < orient A K R := by
    have hh : orient A R K < 0 := tARK
    have he : orient A K R = -(orient A R K) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h2 : 0 < orient A B R := by
    have hh : orient A R B < 0 := tARB
    have he : orient A B R = -(orient A R B) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h1 : 0 < orient A B K := by
    have hh : orient A K B < 0 := tAKB
    have he : orient A B K = -(orient A K B) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h29 : 0 < orient B K R := by
    have hh : orient R K B < 0 := tRKB
    have he : orient B K R = -(orient R K B) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h79 : orient a c z < 0 := by
    have hh : orient a c z < 0 := acz
    have he : orient a c z = (orient a c z) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h14 : orient A R a < 0 := by
    have hh : orient A R a < 0 := (left a eaI)
    have he : orient A R a = (orient A R a) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h16 : orient A R c < 0 := by
    have hh : orient A R c < 0 := (left c ecI)
    have he : orient A R c = (orient A R c) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h18 : orient A R z < 0 := by
    have hh : orient A R z < 0 := (left z ezI)
    have he : orient A R z = (orient A R z) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h17 : orient A R o < 0 := by
    have hh : orient A R o < 0 := (left o eoI)
    have he : orient A R o = (orient A R o) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h30 : 0 < orient B K a := by
    have hh : orient K B a < 0 := (right a eaI)
    have he : orient B K a = -(orient K B a) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h32 : 0 < orient B K c := by
    have hh : orient K B c < 0 := (right c ecI)
    have he : orient B K c = -(orient K B c) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h34 : 0 < orient B K z := by
    have hh : orient K B z < 0 := (right z ezI)
    have he : orient B K z = -(orient K B z) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h33 : 0 < orient B K o := by
    have hh : orient K B o < 0 := (right o eoI)
    have he : orient B K o = -(orient K B o) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h67 : 0 < orient R a o := by
    have hh : 0 < orient R a o := rao
    have he : orient R a o = (orient R a o) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h64 : 0 < orient K o z := by
    have hh : 0 < orient K o z := hfK.1
    have he : orient K o z = (orient K o z) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h63 : 0 < orient K c z := by
    have hh : 0 < orient K c z := ownK
    have he : orient K c z = (orient K c z) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h21 : orient A a o < 0 := by
    have hh : orient A a o < 0 := aao
    have he : orient A a o = (orient A a o) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h49 : orient B o z < 0 := by
    have hh : orient B o z < 0 := boz
    have he : orient B o z = (orient B o z) := by unfold orient; ring
    rw [he]; linarith only [hh]
  have h48 : orient B c z < 0 := by
    have hh : orient B c z < 0 := noR
    have he : orient B c z = (orient B c z) := by unfold orient; ring
    rw [he]; linarith only [hh]
  exact ia_nine_point_bchord_certificate A R K B a b c z o
    h8
    h2
    h1
    h29
    h79
    h14
    h16
    h18
    h17
    h30
    h32
    h34
    h33
    h67
    h64
    h63
    h21
    h49
    h48
    hbad
    (gpSII A B a nAB eaI)
    (gpSII A B c nAB ecI)
    (gpSII A B o nAB eoI)
    (gpSII A B z nAB ezI)
    (gpSII A K a nAK eaI)
    (gpSII A K c nAK ecI)
    (gpSII A K o nAK eoI)
    (gpSII A K z nAK ezI)
    (gpSII2 A a c eaI ecI nac)
    (gpSII2 A a z eaI ezI nza.symm)
    (gpSII2 A c z ecI ezI ec.2.2.1)
    (gpSII B R a nBR eaI)
    (gpSII B R o nBR eoI)
    (gpSII B R z nBR ezI)
    (gpSII2 B a c eaI ecI nac)
    (gpSII2 B a o eaI eoI nao)
    (gpSII K R a nKR eaI)
    (gpSII K R o nKR eoI)
    (gpSII K R z nKR ezI)
    (gpSII2 K a c eaI ecI nac)
    (gpSII2 K a o eaI eoI nao)
    (gpSII2 K a z eaI ezI nza.symm)
    (gpSII2 R a z eaI ezI nza.symm)
end JSP198.Nicolas
#print axioms JSP198.Nicolas.caseIA_last_outer_supports_first_edge
#print axioms JSP198.Nicolas.caseIA_last_outer_supports_arc_chord
