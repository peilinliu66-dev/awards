/- Released under the MIT license. Actual outer joining supports for Nicolas I.A. -/
import JSP198NicolasCaseIAJoinCertificates

set_option maxHeartbeats 1200000
noncomputable section
open Classical Horton
namespace JSP198.Nicolas

/-- Both outer endpoint joins, from the actual short run and local singleton
fibers. No point-level determinant condition is left as an input. -/
theorem caseIA_outer_join_support
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (run : ActualCaseIRun P hgp o ho) (hsingle : RunHasSingletonSectors run)
    (hshort : run.length+3 ≤ (ChainSecond P).card) :
    orient ((chainCycle P hgp o ho).symm run.first : Point)
      (matchStart P hgp o ho run.first) (chainCycle P hgp o ho run.last : Point) < 0 ∧
    orient (matchEnd P hgp o ho run.last) (chainCycle P hgp o ho run.last : Point)
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
  have hAKR : 0 < orient (A : Point) K R := by
    have he : orient (A : Point) K R = -orient (A : Point) R K := by unfold orient; ring
    rw [he]; linarith
  have hABR : 0 < orient (A : Point) B R := by
    have he : orient (A : Point) B R = -orient (A : Point) R B := by unfold orient; ring
    rw [he]; linarith
  have hABK : 0 < orient (A : Point) B K := by
    have he : orient (A : Point) B K = -orient (A : Point) K B := by unfold orient; ring
    rw [he]; linarith
  have hBKR : 0 < orient (B : Point) K R := by
    have he : orient (B : Point) K R = -orient (R : Point) K B := by unfold orient; ring
    rw [he]; linarith
  have rightRev (x : Point) (hx : x ∈ inner (inner P)) : 0 < orient (B : Point) K x := by
    have he : orient (B : Point) K x = -orient (K : Point) B x := by unfold orient; ring
    rw [he]; linarith [right x hx]
  have rbo : orient (R : Point) b o < 0 := by
    have hh := hfR.2
    have he : orient (R : Point) b o = -orient o b R := by unfold orient; ring
    rw [he]; linarith
  have positive_a : 0 < orient (A : Point) B a := by
    by_contra hn
    have hbad : orient (A : Point) B a < 0 :=
      lt_of_le_of_ne (le_of_not_gt hn) (gpSII A B a nAB eaI)
    exact ia_nine_point_entryB_certificate A R K B a b c z o
      (hAKR)
      (hABR)
      (hABK)
      (hBKR)
      (abz)
      (acz)
      (left a eaI)
      (left b ebI)
      (left c ecI)
      (left z ezI)
      (left o eoI)
      (rightRev b ebI)
      (rightRev c ecI)
      (rightRev z ezI)
      (rao)
      (rbo)
      (ownR)
      (hfK.1)
      (ownK)
      (aao)
      (noL)
      (noR)
      (hbad)
      (gpSII A B c nAB ecI)
      (gpSII A B z nAB ezI)
      (gpSII A K a nAK eaI)
      (gpSII A K b nAK ebI)
      (gpSII A K c nAK ecI)
      (gpSII A K o nAK eoI)
      (gpSII A K z nAK ezI)
      (gpSII2 A a c eaI ecI nac)
      (gpSII2 A a z eaI ezI nza.symm)
      (gpSII2 A c z ecI ezI ec.2.2.1)
      (gpSII K R a nKR eaI)
      (gpSII K R b nKR ebI)
      (gpSII K R o nKR eoI)
      (gpSII K R z nKR ezI)
      (gpSII2 K a c eaI ecI nac)
      (gpSII2 K a o eaI eoI nao)
      (gpSII2 K a z eaI ezI nza.symm)
      (gpSII2 R a z eaI ezI nza.symm)
  have positive_z : 0 < orient (A : Point) B z := by
    by_contra hn
    have hbad : orient (A : Point) B z < 0 :=
      lt_of_le_of_ne (le_of_not_gt hn) (gpSII A B z nAB ezI)
    exact ia_nine_point_exitA_certificate A R K B a b c z o
      (hAKR)
      (hABR)
      (hABK)
      (hBKR)
      (abz)
      (acz)
      (left a eaI)
      (left c ecI)
      (left z ezI)
      (rightRev a eaI)
      (rightRev c ecI)
      (rightRev z ezI)
      (rao)
      (ownR)
      (hfK.1)
      (ownK)
      (aao)
      (noL)
      (noR)
      (hbad)
      (gpSII A B c nAB ecI)
      (gpSII A K a nAK eaI)
      (gpSII A K c nAK ecI)
      (gpSII A K o nAK eoI)
      (gpSII A K z nAK ezI)
      (gpSII2 A a c eaI ecI nac)
      (gpSII2 A a z eaI ezI nza.symm)
      (gpSII2 A c z ecI ezI ec.2.2.1)
      (gpSII K R a nKR eaI)
      (gpSII2 K a c eaI ecI nac)
      (gpSII2 K a o eaI eoI nao)
      (gpSII2 K a z eaI ezI nza.symm)
      (gpSII2 R a z eaI ezI nza.symm)
  change orient (A : Point) a B < 0 ∧ orient z B (A : Point) < 0
  constructor
  · have he : orient (A : Point) a B = -orient (A : Point) B a := by unfold orient; ring
    rw [he]; linarith
  · have he : orient z B (A : Point) = -orient (A : Point) B z := by unfold orient; ring
    rw [he]; linarith

end JSP198.Nicolas
#print axioms JSP198.Nicolas.caseIA_outer_join_support
