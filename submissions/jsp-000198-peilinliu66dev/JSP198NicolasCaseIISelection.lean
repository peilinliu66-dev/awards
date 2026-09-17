/-
Copyright (c) 2026 JSP198 formalization contributors. MIT license.
Mathematical source: C. M. Nicolas (2007), Case II block selection.
This replaces explicit circular block enumeration by a finite reachability mask.
The only alternative produced is a genuine Case I run on singleton sectors.
The user's existing Case I proof and all imported files remain unchanged.
Underlying MIT geometry is credited in JSP198NicolasCaseIIBridge.lean.
Target Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Uncompiled candidate.
-/
import Mathlib
import JSP198NicolasCaseIRuns
import JSP198NicolasCaseIIBridge

noncomputable section
open Classical Horton
namespace JSP198.Nicolas.CaseII

/-- A double-sector link, indexed by its FIRST vertex. Nicolas indexes it
by its second vertex; the actual two-point set and its zero-capacity cell agree. -/
def DoubleLink (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P) : Prop :=
  sectorEdge P hgp o ho r = sectorEdge P hgp o ho (chainCycle P hgp o ho r)

lemma doubleLink_matches
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P)
    (hD : DoubleLink P hgp o ho r) :
    CanMatchRight P hgp o ho r ∧
      CanMatchLeft P hgp o ho (chainCycle P hgp o ho r) := by
  have hr := sectorEdge_outward P hgp o ho r
  have hv := sectorEdge_outward P hgp o ho (chainCycle P hgp o ho r)
  change sectorEdge P hgp o ho r =
    sectorEdge P hgp o ho (chainCycle P hgp o ho r) at hD
  constructor
  · rw [← hD] at hv
    exact hv
  · rw [hD] at hr
    simpa only [CanMatchLeft, matchStart, matchEnd, Equiv.symm_apply_apply] using hr

lemma doubleLink_not_next
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬ HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P)
    (hD : DoubleLink P hgp o ho r) :
    ¬ DoubleLink P hgp o ho (chainCycle P hgp o ho r) := by
  intro hD'
  let f := chainCycle P hgp o ho
  let e := sectorEdge P hgp o ho r
  have hg := gp_subset hgp
    ((hullVertices_subset (inner P)).trans Finset.sdiff_subset)
  have h3 := chain_second_card_ge_three P hgp o ho
  have he1 := chainCycle_edge P hgp o ho r
  have he2 := chainCycle_edge P hgp o ho (f r)
  have h02 := boundary_neighbors_ne (ChainSecond P) hg h3 r (f r) (f (f r)) he1 he2
  have h01 : r ≠ f r := by
    intro h
    exact he1.2.2.1 (congrArg (fun z : ChainVertex P => (z : Point)) h)
  have h12 : f r ≠ f (f r) := by
    intro h
    exact he2.2.2.1 (congrArg (fun z : ChainVertex P => (z : Point)) h)
  have h02' : r ≠ f (f r) := by
    intro h
    exact h02 (congrArg (fun z : ChainVertex P => (z : Point)) h)
  let A : Finset (ChainVertex P) := {r, f r, f (f r)}
  have hA3 : A.card = 3 := by simp [A, h01, h02', h12]
  have hsub : A ⊆ (Finset.univ.filter fun z : ChainVertex P =>
      sectorEdge P hgp o ho z = e) := by
    intro z hz
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hz with rfl | rfl | rfl
    · rfl
    · exact hD.symm
    · exact hD'.symm.trans hD.symm
  have hcard := (Finset.card_le_card hsub).trans
    (sectorEdge_fiber_card_le_two P hgp hno o ho e)
  rw [hA3] at hcard
  omega

/-- The exact local Case I alternative: a first-failure run, with every step
before that failure changing sectors. Its sectors are proved globally singleton
below, so this is not a weakened, spurious Case I alternative. -/
structure SeparatedRun
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) where
  run : ActualCaseIRun P hgp o ho
  changes : ∀ j : ℕ, j < run.length →
    ¬ DoubleLink P hgp o ho (orbit (chainCycle P hgp o ho) run.first j)

/-- A vertex is reached from a failed-left vertex without crossing a double link.
The unbounded natural index is only a definition; an actual first failure is
proved to have fewer steps than the finite boundary size. -/
def RightReach
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P) : Prop :=
  ∃ a : ChainVertex P, ∃ k : ℕ,
    ¬ CanMatchLeft P hgp o ho a ∧
    orbit (chainCycle P hgp o ho) a k = r ∧
    ∀ j : ℕ, j < k → ¬ DoubleLink P hgp o ho
      (orbit (chainCycle P hgp o ho) a j)

lemma rightReach_of_not_left
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P)
    (hL : ¬ CanMatchLeft P hgp o ho r) : RightReach P hgp o ho r :=
  ⟨r, 0, hL, rfl, by intro j hj; omega⟩

lemma rightReach_next
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P)
    (hR : RightReach P hgp o ho r) (hD : ¬ DoubleLink P hgp o ho r) :
    RightReach P hgp o ho (chainCycle P hgp o ho r) := by
  obtain ⟨a,k,hL,hend,hpath⟩ := hR
  refine ⟨a,k+1,hL, ?_, ?_⟩
  · change chainCycle P hgp o ho (orbit (chainCycle P hgp o ho) a k) = _
    rw [hend]
  · intro j hj
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | h
    · exact hpath j h
    · subst j
      rwa [hend]

lemma not_rightReach_after_double
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P)
    (hD : DoubleLink P hgp o ho r) :
    ¬ RightReach P hgp o ho (chainCycle P hgp o ho r) := by
  rintro ⟨a,k,hL,hend,hpath⟩
  cases k with
  | zero =>
      change a = chainCycle P hgp o ho r at hend
      subst a
      exact hL (doubleLink_matches P hgp o ho r hD).2
  | succ k =>
      have he : orbit (chainCycle P hgp o ho) a k = r :=
        (chainCycle P hgp o ho).injective hend
      have hn := hpath k (Nat.lt_succ_self k)
      rw [he] at hn
      exact hn hD

/-- If a right-reachable vertex fails to match right, a genuine separated Case I
run is produced, including the finite no-repetition bound. -/
theorem separatedRun_of_rightReach_not_right
    (P : Finset Point) (hgp : GeneralPosition P)
    (hmin : MinimalOuter P) (hno : ¬ HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (r : ChainVertex P)
    (hreach : RightReach P hgp o ho r)
    (hbad : ¬ CanMatchRight P hgp o ho r) :
    Nonempty (SeparatedRun P hgp o ho) := by
  obtain ⟨a,k,hL,hend,hpath⟩ := hreach
  have hR0 : CanMatchRight P hgp o ho a :=
    (actual_match_left_or_right P hgp hmin hno o ho a).resolve_left hL
  have hevent : ∃ j : ℕ,
      ¬ CanMatchRight P hgp o ho (orbit (chainCycle P hgp o ho) a j) :=
    ⟨k, by rwa [hend]⟩
  obtain ⟨j,hjpos,hjcard,hbefore,hstop,hinj⟩ := exists_first_failure_prefix
    (chainCycle P hgp o ho) a (CanMatchRight P hgp o ho) hR0 hevent
  have hjk : j ≤ k := by
    by_contra hn
    have hh := hbefore k (by omega)
    rw [hend] at hh
    exact hbad hh
  have hcard : Fintype.card (ChainVertex P) = (ChainSecond P).card :=
    Fintype.card_coe _
  rw [hcard] at hjcard
  let R : ActualCaseIRun P hgp o ho :=
    ⟨a,j,hjpos,hjcard,hL,hbefore,hstop,hinj⟩
  refine ⟨⟨R, ?_⟩⟩
  intro i hi
  exact hpath i (lt_of_lt_of_le hi hjk)

/-- The mask exists under the literal Case II condition (absence of a separated
Case I run). Reset edges are EXACTLY double-sector links. -/
structure MatchMask
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) where
  rightSet : ChainVertex P → Prop
  right_ok : ∀ r, rightSet r → CanMatchRight P hgp o ho r
  left_ok : ∀ r, ¬ rightSet r → CanMatchLeft P hgp o ho r
  resets : ∀ r, DoubleLink P hgp o ho r ↔
    rightSet r ∧ ¬ rightSet (chainCycle P hgp o ho r)

theorem exists_matchMask
    (P : Finset Point) (hgp : GeneralPosition P)
    (hmin : MinimalOuter P) (hno : ¬ HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hII : ¬ Nonempty (SeparatedRun P hgp o ho)) :
    Nonempty (MatchMask P hgp o ho) := by
  let Z : ChainVertex P → Prop := fun r =>
    DoubleLink P hgp o ho r ∨ RightReach P hgp o ho r
  have hright : ∀ r, Z r → CanMatchRight P hgp o ho r := by
    intro r hz
    rcases hz with hD | hreach
    · exact (doubleLink_matches P hgp o ho r hD).1
    · by_contra hn
      exact hII (separatedRun_of_rightReach_not_right P hgp hmin hno o ho r hreach hn)
  have hleft : ∀ r, ¬ Z r → CanMatchLeft P hgp o ho r := by
    intro r hz
    by_contra hL
    exact hz (Or.inr (rightReach_of_not_left P hgp o ho r hL))
  refine ⟨⟨Z, hright, hleft, ?_⟩⟩
  intro r
  constructor
  · intro hD
    refine ⟨Or.inl hD, ?_⟩
    rintro (hD' | hreach)
    · exact doubleLink_not_next P hgp hno o ho r hD hD'
    · exact not_rightReach_after_double P hgp o ho r hD hreach
  · rintro ⟨hz, hn⟩
    by_contra hD
    have hr := hz.resolve_left hD
    exact hn (Or.inr (rightReach_next P hgp o ho r hr hD))

/-- Every vertex in the produced separated run has a globally singleton sector.
The two endpoint exclusions use noLeft and noRight_end; interior exclusions
use the two adjacent sector changes. -/
theorem SeparatedRun.sector_fiber_unique
    {P : Finset Point} {hgp : GeneralPosition P}
    (hno : ¬ HasEmptySix P)
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : SeparatedRun P hgp o ho)
    (j : Fin (R.run.length + 1)) (s : ChainVertex P)
    (heq : sectorEdge P hgp o ho s =
      sectorEdge P hgp o ho (orbit (chainCycle P hgp o ho) R.run.first j.val)) :
    s = orbit (chainCycle P hgp o ho) R.run.first j.val := by
  let f := chainCycle P hgp o ho
  let r : ChainVertex P := orbit f R.run.first j.val
  have hg := gp_subset hgp
    ((hullVertices_subset (inner P)).trans Finset.sdiff_subset)
  by_contra hne
  have hne' : r ≠ s := Ne.symm hne
  have heq' : sectorEdge P hgp o ho r = sectorEdge P hgp o ho s := heq.symm
  rcases same_sector_pair_adjacent P hgp hno o ho r s hne' heq' with h | h
  · have hnext : f r = s := by
      apply Subtype.ext
      exact boundaryEdge_right_unique hg (chainCycle_edge P hgp o ho r) h
    have hD : DoubleLink P hgp o ho r := by
      change sectorEdge P hgp o ho r = sectorEdge P hgp o ho (f r)
      rw [hnext]
      exact heq'
    by_cases hj : j.val < R.run.length
    · exact R.changes j.val hj hD
    · have hjlast : j.val = R.run.length := by omega
      have hrR := (doubleLink_matches P hgp o ho r hD).1
      apply R.run.noRight_end
      simpa only [r, hjlast] using hrR
  · have hnext : f s = r := by
      apply Subtype.ext
      exact boundaryEdge_right_unique hg (chainCycle_edge P hgp o ho s) h
    have hD : DoubleLink P hgp o ho s := by
      change sectorEdge P hgp o ho s = sectorEdge P hgp o ho (f s)
      rw [hnext]
      exact heq
    by_cases hj : j.val = 0
    · have hrL := (doubleLink_matches P hgp o ho s hD).2
      change CanMatchLeft P hgp o ho (f s) at hrL
      rw [hnext] at hrL
      apply R.run.noLeft
      simpa only [r, hj, orbit] using hrL
    · have hjpred : j.val - 1 + 1 = j.val := by omega
      have hprev : f (orbit f R.run.first (j.val - 1)) = r := by
        change orbit f R.run.first (j.val - 1 + 1) = r
        rw [hjpred]
      have hsprev : s = orbit f R.run.first (j.val - 1) :=
        f.injective (hnext.trans hprev.symm)
      have hDprev : DoubleLink P hgp o ho
          (orbit f R.run.first (j.val - 1)) := by rwa [← hsprev]
      exact R.changes (j.val - 1) (by omega) hDprev

/-- In particular the sector labels in the full run are distinct. Their radial
ordering comes from the actual boundary walk, not an independent order axiom. -/
theorem SeparatedRun.sector_injective
    {P : Finset Point} {hgp : GeneralPosition P}
    (hno : ¬ HasEmptySix P)
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : SeparatedRun P hgp o ho) :
    Function.Injective (fun j : Fin (R.run.length + 1) =>
      sectorEdge P hgp o ho (orbit (chainCycle P hgp o ho) R.run.first j.val)) := by
  intro i j he
  apply R.run.prefix_injective
  exact SeparatedRun.sector_fiber_unique hno R j
    (orbit (chainCycle P hgp o ho) R.run.first i.val) he

/-! Exact finite balancing, replacing the paper's explicit block-length sum. -/

lemma sum_comp_permutation {V : Type*} [Fintype V]
    (f : Equiv.Perm V) (w : V → ℕ) : (∑ r : V, w (f r)) = ∑ r : V, w r := by
  classical
  refine Finset.sum_bij (fun r _ => f r) ?_ ?_ ?_ ?_
  · intro r _; exact Finset.mem_univ _
  · intro r _ s _ h; exact f.injective h
  · intro s _; exact ⟨f.symm s, Finset.mem_univ _, f.apply_symm_apply s⟩
  · intro r _; rfl

/-- Along any finite permutation, the number of L-to-R transitions equals the
number of R-to-L transitions. No single-cycle or block enumeration is needed. -/
theorem transition_balance {V : Type*} [Fintype V]
    (f : Equiv.Perm V) (Z : V → Prop) :
    (∑ r : V, if ¬ Z r ∧ Z (f r) then 1 else 0 : ℕ) =
      ∑ r : V, if Z r ∧ ¬ Z (f r) then 1 else 0 := by
  classical
  have hpoint (r : V) :
      (if ¬ Z r ∧ Z (f r) then 1 else 0 : ℕ) + (if Z r then 1 else 0) =
        (if Z r ∧ ¬ Z (f r) then 1 else 0) + (if Z (f r) then 1 else 0) := by
    by_cases hr : Z r <;> by_cases hs : Z (f r) <;> simp [hr, hs]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun r _ => hpoint r)
  simp only [Finset.sum_add_distrib] at hsum
  have heq := sum_comp_permutation f (fun r => if Z r then 1 else 0)
  rw [heq] at hsum
  omega

end JSP198.Nicolas.CaseII

#print axioms JSP198.Nicolas.CaseII.exists_matchMask
#print axioms JSP198.Nicolas.CaseII.transition_balance
