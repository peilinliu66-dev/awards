/- Released under the MIT license. Actual endpoint support for Case I.A. -/
import JSP198NicolasCaseIAEndpoint
import JSP198NicolasCaseIAChordCertificate

set_option maxHeartbeats 1200000
noncomputable section
open Classical Horton
namespace JSP198.Nicolas

theorem caseIA_first_outer_supports_arc_chord
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (run : ActualCaseIRun P hgp o ho) (hsingle : RunHasSingletonSectors run)
    (hshort : run.length+3 ≤ (ChainSecond P).card) :
    orient (matchStart P hgp o ho run.first) (matchEnd P hgp o ho run.last)
      ((chainCycle P hgp o ho).symm run.first : Point) < 0 := by
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
  have endA : orient (A : Point) c z < 0 := by
    have hh := caseIA_first_outer_supports_last_edge run hsingle hshort
    change orient c z (A : Point) < 0 at hh
    convert hh using 1 <;> unfold orient <;> ring
  change orient a z (A : Point) < 0
  have nz : orient a z (A : Point) ≠ 0 := by
    have hh := gpSII2 A a z eaI ezI nza.symm
    convert hh using 1 <;> unfold orient <;> ring
  by_contra hn
  have hbad : 0 < orient (A : Point) a z := by
    have hh : 0 < orient a z (A : Point) := lt_of_le_of_ne (le_of_not_gt hn) nz.symm
    convert hh using 1 <;> unfold orient <;> ring
  apply ia_nine_point_chord_support_certificate A R K B a b c z o
    (by
      have he : orient (A : Point) K R = -orient (A : Point) R K := by unfold orient; ring
      rw [he]; linarith)
    (by
      have he : orient (A : Point) B K = -orient (A : Point) K B := by unfold orient; ring
      rw [he]; linarith)
    (by
      have he : orient (B : Point) K R = -orient (R : Point) K B := by unfold orient; ring
      rw [he]; linarith)
    abz acz (left a eaI) (left c ecI) (left z ezI)
    (by
      have he : orient (B : Point) K a = -orient (K : Point) B a := by unfold orient; ring
      rw [he]; linarith [right a eaI])
    (by
      have he : orient (B : Point) K z = -orient (K : Point) B z := by unfold orient; ring
      rw [he]; linarith [right z ezI])
    (by
      have he : orient (B : Point) K o = -orient (K : Point) B o := by unfold orient; ring
      rw [he]; linarith [right o eoI])
    rao abo hfK.1 ownK aao noL hbad endA
    (gpSII A K a nAK eaI) (gpSII A K c nAK ecI)
    (gpSII A K o nAK eoI) (gpSII A K z nAK ezI)
    (gpSII2 A a c eaI ecI nac) (gpSII K R a nKR eaI)
    (gpSII2 K a b eaI ebI ea.2.2.1) (gpSII2 K a c eaI ecI nac)
    (gpSII2 K a o eaI eoI nao) (gpSII2 K a z eaI ezI nza.symm)

end JSP198.Nicolas
#print axioms JSP198.Nicolas.caseIA_first_outer_supports_arc_chord
