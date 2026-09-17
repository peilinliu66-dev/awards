/-
Released under the MIT license.
Nicolas, The Empty Hexagon Theorem (2007), Theorem 4 Case I.B.
The only sector hypothesis is uniqueness of the fibers of vertices ON THE RUN.
Global sector injectivity is DERIVED in this branch, since precisely one
second-layer vertex is outside the run.  No cover or convexity premise.
Candidate Lean source for the pinned project; not compiled in this environment.
-/
import Mathlib
import JSP198NicolasCaseIBSupport
import JSP198NicolasCaseIC

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

/-- Exact input supplied by the singleton-run reduction. Vertices outside the
run are unrestricted. -/
def RunHasSingletonSectors
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho) : Prop :=
  ∀ j : ℕ, j ≤ R.length → ∀ s : ChainVertex P,
    sectorEdge P hgp o ho s =
      sectorEdge P hgp o ho (orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j) →
    s = orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j

/-- A finite prefix closed under its actual successor contains its whole orbit. -/
lemma ib_closed_prefix_surjective
    {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → A) (first : A) (k : ℕ)
    (hclose : f (orbit f first k) = first)
    (hreach : ∀ a : A, ∃ j : ℕ, orbit f first j = a) :
    Function.Surjective (fun j : Fin (k+1) => orbit f first j.val) := by
  let T := (Finset.univ : Finset (Fin (k+1))).image (fun j => orbit f first j.val)
  have hfirst : first ∈ T :=
    Finset.mem_image.mpr ⟨⟨0,by omega⟩,Finset.mem_univ _,rfl⟩
  have hclosed : ∀ a ∈ T, f a ∈ T := by
    intro a ha
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp ha
    rw [← hj]
    by_cases hjk : j.val = k
    · simpa only [hjk,hclose] using hfirst
    · have hlt : j.val+1 < k+1 := by have := j.isLt; omega
      exact Finset.mem_image.mpr ⟨⟨j.val+1,hlt⟩,Finset.mem_univ _,rfl⟩
  have hall : ∀ j : ℕ, orbit f first j ∈ T := by
    intro j
    induction j with
    | zero => exact hfirst
    | succ j ih => exact hclosed _ ih
  intro a
  obtain ⟨j,hj⟩ := hreach a
  have ha : a ∈ T := hj ▸ hall j
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
  exact ⟨i,hi⟩

/-- The first card(C2) iterates of the REAL boundary cycle are distinct, and
its next iterate closes. Derived from the already proved reachability. -/
lemma ib_full_cycle_enumeration
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) (first : ChainVertex P) :
    Function.Injective (fun j : Fin ((ChainSecond P).card) =>
      orbit (α := ChainVertex P) (chainCycle P hgp o ho) first j.val) ∧
    orbit (α := ChainVertex P) (chainCycle P hgp o ho) first ((ChainSecond P).card) = first := by
  let f := chainCycle P hgp o ho
  let last := f.symm first
  have hedge : BoundaryEdge (ChainSecond P) last first := by
    simpa only [last,f,Equiv.apply_symm_apply] using chainCycle_edge P hgp o ho last
  have hne : first ≠ last := by
    intro h
    exact hedge.2.2.1 (congrArg (fun z : ChainVertex P => (z : Point)) h).symm
  obtain ⟨j,_,hj⟩ := chainCycle_reaches P hgp o ho first last
  have hevent : ∃ j : ℕ, ¬ (orbit (α := ChainVertex P) f first j ≠ last) :=
    ⟨j,fun hn => hn hj⟩
  obtain ⟨k,hk0,hkcard,hbefore,hstop,hinj⟩ := exists_first_failure_prefix
    f first (fun a => a ≠ last) hne hevent
  have heq : orbit (α := ChainVertex P) f first k = last := by
    by_contra h
    exact hstop h
  have hclose : f (orbit (α := ChainVertex P) f first k) = first := by
    rw [heq]; exact f.apply_symm_apply first
  have hsurj := ib_closed_prefix_surjective f first k hclose (by
    intro a
    obtain ⟨j,_,hj⟩ := chainCycle_reaches P hgp o ho first a
    exact ⟨j,hj⟩)
  have hcard := Fintype.card_of_bijective ⟨hinj,hsurj⟩
  have hsize : k+1 = (ChainSecond P).card := by
    have hcardV : Fintype.card (ChainVertex P) = (ChainSecond P).card := Fintype.card_coe _
    simpa only [Fintype.card_fin,hcardV] using hcard
  have hi : Function.Injective (fun j : Fin ((ChainSecond P).card) =>
      orbit (α := ChainVertex P) f first j.val) := by
    intro a b hab
    have he := hinj (a₁ := ⟨a.val, by omega⟩) (a₂ := ⟨b.val, by omega⟩) hab
    exact Fin.ext (congrArg (fun z : Fin (k+1) => z.val) he)
  have hc : orbit (α := ChainVertex P) f first ((ChainSecond P).card) = first := by
    rw [← hsize]
    exact hclose
  exact ⟨hi,hc⟩

namespace ActualCaseIRun

/-- Full enumeration used only in the case with exactly one omitted vertex. -/
lemma ib_enumeration
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hB : R.length+2 = (ChainSecond P).card) :
    Function.Bijective (fun j : Fin (R.length+2) =>
      orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j.val) ∧
    chainCycle P hgp o ho (chainCycle P hgp o ho R.last) = R.first := by
  let f := chainCycle P hgp o ho
  obtain ⟨hinj,hclose⟩ := ib_full_cycle_enumeration P hgp o ho R.first
  have hi : Function.Injective (fun j : Fin (R.length+2) =>
      orbit (α := ChainVertex P) f R.first j.val) := by
    intro a b hab
    have he := hinj (a₁ := ⟨a.val, by omega⟩) (a₂ := ⟨b.val, by omega⟩) hab
    exact Fin.ext (congrArg (fun z : Fin ((ChainSecond P).card) => z.val) he)
  let e := fun j : Fin (R.length+2) => orbit (α := ChainVertex P) f R.first j.val
  let T := (Finset.univ : Finset (Fin (R.length+2))).image e
  have hcT : T.card = (ChainSecond P).card := by
    dsimp [T]
    rw [Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin,hB]
  have hT : T = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    have hcardV : Fintype.card (ChainVertex P) = (ChainSecond P).card := Fintype.card_coe _
    simpa only [Finset.card_univ,hcardV,hcT] using
      (le_refl (ChainSecond P).card)
  have hs : Function.Surjective e := by
    intro a
    have ha : a ∈ T := by rw [hT]; exact Finset.mem_univ _
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp ha
    exact ⟨j,hj⟩
  refine ⟨⟨hi,hs⟩,?_⟩
  change orbit (α := ChainVertex P) f R.first (R.length+2) = R.first
  rwa [hB]

lemma ib_outside_ne_run
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hB : R.length+2 = (ChainSecond P).card)
    (j : ℕ) (hj : j ≤ R.length) :
    chainCycle P hgp o ho R.last ≠
      orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j := by
  intro he
  have hi := (R.ib_enumeration hB).1.1
  have hindices : (⟨R.length+1,by omega⟩ : Fin (R.length+2)) = ⟨j,by omega⟩ := hi he
  have hv := congrArg Fin.val hindices
  simp only at hv
  omega

lemma ib_outside_or_run
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hB : R.length+2 = (ChainSecond P).card) (a : ChainVertex P) :
    a = chainCycle P hgp o ho R.last ∨
      ∃ j : ℕ, j ≤ R.length ∧
        a = orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j := by
  obtain ⟨j,hj⟩ := (R.ib_enumeration hB).1.2 a
  by_cases hlast : j.val = R.length+1
  · left
    rw [← hj]
    change orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j.val = _
    rw [hlast]
    rfl
  · right
    refine ⟨j.val,by have := j.isLt; omega,hj.symm⟩

/-- In I.B only, local singleton fibers force global injectivity because
there is exactly one vertex outside the run. This is a conclusion, not input. -/
lemma ib_sector_injective
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hB : R.length+2 = (ChainSecond P).card)
    (hsingle : RunHasSingletonSectors R) :
    Function.Injective (sectorEdge P hgp o ho) := by
  intro a b he
  rcases R.ib_outside_or_run hB a with ha | ⟨j,hj,ha⟩
  · rcases R.ib_outside_or_run hB b with hb | ⟨j,hj,hb⟩
    · exact ha.trans hb.symm
    · have h := hsingle j hj a (by simpa only [hb] using he)
      exact h.trans hb.symm
  · have h := hsingle j hj b (by simpa only [ha] using he.symm)
    exact ha.trans h.symm

lemma ib_adjacent_distinct
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hB : R.length+2 = (ChainSecond P).card)
    (hsingle : RunHasSingletonSectors R) :
    AdjacentSectorsDistinct P hgp o ho := by
  intro a he
  have h := R.ib_sector_injective hB hsingle he
  exact (chainCycle_edge P hgp o ho a).2.2.1
    (congrArg (fun z : ChainVertex P => (z : Point)) h)

lemma ib_right_except_two
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hB : R.length+2 = (ChainSecond P).card) :
    ∀ a : ChainVertex P, a ≠ R.last → a ≠ chainCycle P hgp o ho R.last →
      CanMatchRight P hgp o ho a := by
  intro a hal has
  rcases R.ib_outside_or_run hB a with ha | ⟨j,hj,ha⟩
  · exact (has ha).elim
  · have hjk : j < R.length := by
      by_contra hn
      have he : j = R.length := by omega
      exact hal (by rw [ha,he]; rfl)
    rw [ha]
    exact R.right_before j hjk

end ActualCaseIRun

/-! ## The exact one-fan cover for the left-matching outside vertex -/

/-- The fan vertex is selected geometrically rather than prescribed as a0.
This is the genuine Case I.B cover, including both exceptional joins. -/
theorem ib_one_fan_outer_bound
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (R : ActualCaseIRun P hgp o ho)
    (hB : R.length+2 = (ChainSecond P).card)
    (hsingle : RunHasSingletonSectors R)
    (hsleft : CanMatchLeft P hgp o ho (chainCycle P hgp o ho R.last)) :
    (hullVertices P).card ≤ (ChainSecond P).card+1 := by
  let f := chainCycle P hgp o ho
  let l := R.last
  let s := f l
  let first := R.first
  let a := matchStart P hgp o ho s
  let b := matchEnd P hgp o ho s
  have hclose : f s = first := (R.ib_enumeration hB).2
  have hsf : s ≠ first := R.ib_outside_ne_run hB 0 (by omega)
  have hsl : s ≠ l := R.ib_outside_ne_run hB R.length (le_refl _)
  have hfl : first ≠ l := R.first_ne_last
  have hdiff := R.ib_adjacent_distinct hB hsingle
  obtain ⟨z,hz,_,hgapS,hgapF⟩ := ib_sector_bridge_vertex P hgp o ho s (hdiff s)
  have hgapF' : 0 ≤ orient (first : Point) z (matchStart P hgp o ho first) := by
    change 0 ≤ orient (f s : Point) z (matchStart P hgp o ho (f s)) at hgapF
    simpa only [hclose] using hgapF
  have hgapS' : 0 ≤ orient (s : Point) b z := hgapS
  let c : ChainVertex P → Point := fun r =>
    if r = s then z else if r = l then a else matchStart P hgp o ho r
  let d : ChainVertex P → Point := fun r =>
    if r = s then z else if r = l then b else matchEnd P hgp o ho r
  have hc : ∀ r, c r ∈ inner (inner P) := by
    intro r
    by_cases hrs : r = s
    · simpa only [c,if_pos hrs] using hz
    · by_cases hrl : r = l
      · simpa only [c,if_neg hrs,if_pos hrl] using matchStart_mem P hgp o ho s
      · simpa only [c,if_neg hrs,if_neg hrl] using matchStart_mem P hgp o ho r
  have hd : ∀ r, d r ∈ inner (inner P) := by
    intro r
    by_cases hrs : r = s
    · simpa only [d,if_pos hrs] using hz
    · by_cases hrl : r = l
      · simpa only [d,if_neg hrs,if_pos hrl] using matchEnd_mem P hgp o ho s
      · simpa only [d,if_neg hrs,if_neg hrl] using matchEnd_mem P hgp o ho r
  have hsface : 0 < orient a b (s : Point) := sectorEdge_outward P hgp o ho s
  have hlface : 0 < orient a b (l : Point) := by
    have h := hsleft
    change 0 < orient a b (f.symm s : Point) at h
    simpa only [s,Equiv.symm_apply_apply] using h
  have hshape : ∀ r : ChainVertex P, c r = d r ∨
      (0 < orient (r : Point) (c r) (d r) ∧
       0 < orient (r : Point) (c r) (f r : Point) ∧
       0 < orient (r : Point) (d r) (f r : Point) ∧
       0 < orient (c r) (d r) (f r : Point)) := by
    intro r
    by_cases hrs : r = s
    · left; simp only [c,d,if_pos hrs]
    · right
      by_cases hrl : r = l
      · subst r
        simp only [c,d,if_neg hsl.symm,if_pos rfl]
        exact boundary_match_four_signs P hgp l s a b
          (chainCycle_edge P hgp o ho l) (matchStartEnd_edge P hgp o ho s) hlface hsface
      · simp only [c,d,if_neg hrs,if_neg hrl]
        exact boundary_match_four_signs P hgp r (f r)
          (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
          (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho r)
          (sectorEdge_outward P hgp o ho r) (R.ib_right_except_two hB r hrl hrs)
  have hgap : ∀ r : ChainVertex P, 0 ≤ orient (f r : Point) (d r) (c (f r)) := by
    intro r
    by_cases hrs : r = s
    · subst r
      simp only [d,c,if_pos rfl,hclose,if_neg hsf.symm,if_neg hfl]
      exact hgapF'
    · by_cases hrl : r = l
      · subst r
        change 0 ≤ orient (s : Point) (d l) (c s)
        simpa only [d,c,if_neg hsl.symm,ite_true] using hgapS'
      · have hns : f r ≠ s := by
          intro he
          exact hrl (f.injective he)
        by_cases hnl : f r = l
        · simp only [d,c,if_neg hrs,if_neg hrl,if_neg hns,if_pos hnl]
          have hh := skipped_sector_join_positive P hgp o ho hdiff r
          change 0 < orient (f r : Point) (matchEnd P hgp o ho r)
            (matchStart P hgp o ho (f (f r))) at hh
          rw [hnl] at hh
          simpa only [hnl] using hh.le
        · simp only [d,c,if_neg hrs,if_neg hrl,if_neg hns,if_neg hnl]
          exact right_radial_join_coherent P hgp o ho r (hdiff r)
            (R.ib_right_except_two hB r hrl hrs)
  let cells := fun r : ChainVertex P => stripCell P r (f r) (c r) (d r)
  have hcover : ∀ x ∈ hullVertices P, ∃ r ∈ (Finset.univ : Finset (ChainVertex P)),
      x ∈ cells r := by
    intro x hx
    obtain ⟨r,hr⟩ := coherent_strips_cover P hgp o ho c d hc hd hshape hgap x hx
    exact ⟨r,Finset.mem_univ _,hr⟩
  have hbound : ∀ r : ChainVertex P, (cells r).card ≤ 1 + if r=s then 1 else 0 := by
    intro r
    by_cases hrs : r=s
    · subst r
      have he : cells s = outerFan P z (s,f s) := by
        dsimp only [cells]
        simp only [c,d,if_pos rfl]
        exact stripCell_self_eq_outerFan P s (f s) z
      rw [he,if_pos rfl]
      exact outerFan_card_le_two P hgp hno z (Finset.mem_sdiff.mp hz).1
        (s,f s) (chainCycle_edge P hgp o ho s)
        (chain_inner2_ne_second hz s) (chain_inner2_ne_second hz (f s))
    · by_cases hrl : r=l
      · subst r
        have he : cells l = matchChannel P l s a b := by
          dsimp only [cells]
          simp only [c,d,if_neg hsl.symm,if_pos rfl]
          exact stripCell_eq_matchChannel P l s a b (matchStartEnd_edge P hgp o ho s).2.2.1
        rw [he,if_neg hsl.symm,Nat.add_zero]
        exact boundary_match_channel_le_one P hgp hno l s a b
          (chainCycle_edge P hgp o ho l) (matchStartEnd_edge P hgp o ho s) hlface hsface
      · have he : cells r = matchChannel P r (f r)
            (matchStart P hgp o ho r) (matchEnd P hgp o ho r) := by
          dsimp only [cells]
          simp only [c,d,if_neg hrs,if_neg hrl]
          exact stripCell_eq_matchChannel _ _ _ _ _ (matchStartEnd_edge P hgp o ho r).2.2.1
        rw [he,if_neg hrs,Nat.add_zero]
        exact boundary_match_channel_le_one P hgp hno r (f r)
          (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
          (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho r)
          (sectorEdge_outward P hgp o ho r) (R.ib_right_except_two hB r hrl hrs)
  have hcN := card_le_sum_of_cover (hullVertices P) Finset.univ cells hcover
  have hsum : (∑ r : ChainVertex P, (cells r).card) ≤ (ChainSecond P).card+1 := by
    calc
      (∑ r : ChainVertex P, (cells r).card) ≤
          ∑ r : ChainVertex P, (1 + if r=s then 1 else 0 : ℕ) :=
        Finset.sum_le_sum (fun r _ => hbound r)
      _ = (ChainSecond P).card+1 := by
        rw [Finset.sum_add_distrib]
        simp [ChainVertex]
  exact hcN.trans hsum

/-! ## Tight equality is impossible: insert the one outside vertex into C3 -/

theorem hasEmptySix_of_caseIB_left
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (R : ActualCaseIRun P hgp o ho)
    (hB : R.length+2 = (ChainSecond P).card)
    (hsingle : RunHasSingletonSectors R)
    (hsleft : CanMatchLeft P hgp o ho (chainCycle P hgp o ho R.last)) :
    HasEmptySix P := by
  by_contra hno
  let f := chainCycle P hgp o ho
  let l := R.last
  let s := f l
  let first := R.first
  let c := matchStart P hgp o ho l
  let a := matchStart P hgp o ho s
  let b := matchEnd P hgp o ho s
  let d := matchEnd P hgp o ho first
  have hclose : f s = first := (R.ib_enumeration hB).2
  have hdiff := R.ib_adjacent_distinct hB hsingle
  have hbound := ib_one_fan_outer_bound P hgp hno o ho R hB hsingle hsleft
  obtain ⟨hsize,houter,hbij,hsucc⟩ :=
    tight_layer_sizes_and_successors P hgp hmin hno o ho hdiff hbound
  have hca : matchEnd P hgp o ho l = a := hsucc l
  have hab : b = matchStart P hgp o ho first := by
    have hh := hsucc s
    change b = matchStart P hgp o ho (f s) at hh
    simpa only [hclose] using hh
  have heCA : BoundaryEdge (ChainThird P) c a := by
    have hh := matchStartEnd_edge P hgp o ho l
    rwa [hca] at hh
  have heAB : BoundaryEdge (ChainThird P) a b := matchStartEnd_edge P hgp o ho s
  have heBD : BoundaryEdge (ChainThird P) b d := by
    rw [hab]
    exact matchStartEnd_edge P hgp o ho first
  have hface : 0 < orient a b (s : Point) := sectorEdge_outward P hgp o ho s
  have hprev : orient c a (s : Point) < 0 := by
    have hn : ¬0 < orient c a (s : Point) := by
      intro h
      apply R.noRight_end
      change 0 < orient c (matchEnd P hgp o ho l) (s : Point)
      rwa [hca]
    have hne := hgp c (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (matchStart_mem P hgp o ho l)).1).1
      a (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (matchStart_mem P hgp o ho s)).1).1
      s (Finset.mem_sdiff.mp (chain_second_mem_inner s)).1 heCA.2.2.1
      (chain_inner2_ne_second (matchStart_mem P hgp o ho l) s)
      (chain_inner2_ne_second (matchStart_mem P hgp o ho s) s)
    exact lt_of_le_of_ne (le_of_not_gt hn) hne
  have hnext : orient b d (s : Point) < 0 := by
    have hn : ¬0 < orient b d (s : Point) := by
      intro h
      apply R.noLeft
      change 0 < orient (matchStart P hgp o ho first) d (f.symm first : Point)
      have hpred : f.symm first=s := by rw [← hclose,Equiv.symm_apply_apply]
      rwa [hpred,←hab]
    have hne := hgp b (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (matchEnd_mem P hgp o ho s)).1).1
      d (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (matchEnd_mem P hgp o ho first)).1).1
      s (Finset.mem_sdiff.mp (chain_second_mem_inner s)).1 heBD.2.2.1
      (chain_inner2_ne_second (matchEnd_mem P hgp o ho s) s)
      (chain_inner2_ne_second (matchEnd_mem P hgp o ho first) s)
    exact lt_of_le_of_ne (le_of_not_gt hn) hne
  have hgpI := gp_subset hgp (show inner P ⊆ P from Finset.sdiff_subset)
  have hgpII := gp_subset hgpI (show inner (inner P) ⊆ inner P from Finset.sdiff_subset)
  have hQ3 : 3 ≤ (ChainThird P).card :=
    three_le_hull_of_inner_nonempty (inner (inner P)) hgpII ⟨o,ho⟩
  have hQI : ChainThird P ⊆ inner P := (hullVertices_subset (inner (inner P))).trans Finset.sdiff_subset
  have hsQ : (s : Point) ∉ ChainThird P := by
    intro h
    exact (chain_inner2_ne_second (chain_third_mem_inner2 h) s) rfl
  have hconv := ib_insert_single_visible_edge_convex (inner P) (ChainThird P)
    hgpI hQI (convexIndependent_hullVertices (inner (inner P))) hQ3
    s c a b d (chain_second_mem_inner s) hsQ heCA heAB heBD hface hprev hnext
  let T : Finset Point := insert (s : Point) (ChainThird P)
  have hTI : T ⊆ inner P := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact chain_second_mem_inner s
    · exact hQI hx
  have hTP : T ⊆ P := hTI.trans Finset.sdiff_subset
  have hne : T ≠ hullVertices P := by
    intro h
    have hsT : (s : Point) ∈ T := Finset.mem_insert_self _ _
    have hsH : (s : Point) ∈ hullVertices P := h ▸ hsT
    exact (Finset.mem_sdiff.mp (chain_second_mem_inner s)).2 hsH
  have hsmall := hmin.smaller T hTP (by
    intro x hx
    rw [convexHull_hullVertices]
    exact subset_convexHull ℝ _ (hTP hx)) hconv hne
  have hcard : T.card = (ChainThird P).card+1 := by
    simp only [T,Finset.card_insert_of_notMem hsQ]
  omega

/-! ## The other side is an ACTUAL full run, not an informal reflection -/

theorem hasEmptySix_of_caseIB_not_left
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (R : ActualCaseIRun P hgp o ho)
    (hB : R.length+2 = (ChainSecond P).card)
    (hsingle : RunHasSingletonSectors R)
    (hsnotleft : ¬CanMatchLeft P hgp o ho (chainCycle P hgp o ho R.last)) :
    HasEmptySix P := by
  by_contra hno
  let f := chainCycle P hgp o ho
  let l := R.last
  let s := f l
  have hsl : s ≠ l := R.ib_outside_ne_run hB R.length (le_refl _)
  have hsright : CanMatchRight P hgp o ho s := by
    rcases actual_match_left_or_right P hgp hmin hno o ho s with h | h
    · exact (hsnotleft h).elim
    · exact h
  have hall : ∀ a : ChainVertex P, a ≠ l → CanMatchRight P hgp o ho a := by
    intro a ha
    by_cases hs : a=s
    · simpa only [hs] using hsright
    · exact R.ib_right_except_two hB a ha hs
  obtain ⟨j,_,hj⟩ := chainCycle_reaches P hgp o ho s l
  have hevent : ∃ j : ℕ, ¬CanMatchRight P hgp o ho (orbit (α := ChainVertex P) f s j) :=
    ⟨j,by
      change ¬CanMatchRight P hgp o ho
        (orbit (α := ChainVertex P) (chainCycle P hgp o ho) s j)
      rw [hj]
      exact R.noRight_end⟩
  obtain ⟨k,hkpos,hkbound,hbefore,hstop,hinj⟩ := exists_first_failure_prefix
    f s (CanMatchRight P hgp o ho) hsright hevent
  have hend : orbit (α := ChainVertex P) f s k = l := by
    by_contra h
    exact hstop (hall _ h)
  have hclose : f (orbit (α := ChainVertex P) f s k) = s := by rw [hend]
  have hsurj := ib_closed_prefix_surjective f s k hclose (by
    intro a
    obtain ⟨j,_,hj⟩ := chainCycle_reaches P hgp o ho s a
    exact ⟨j,hj⟩)
  have hsize : k+1 = (ChainSecond P).card := by
    have hc := Fintype.card_of_bijective ⟨hinj,hsurj⟩
    have hcardV : Fintype.card (ChainVertex P) = (ChainSecond P).card := Fintype.card_coe _
    simpa only [Fintype.card_fin,hcardV] using hc
  have hk : k < (ChainSecond P).card := by omega
  let R' : ActualCaseIRun P hgp o ho :=
    ⟨s,k,hkpos,hk,hsnotleft,hbefore,hstop,hinj⟩
  exact hno (hasEmptySix_of_full_caseI_run P hgp hmin o ho
    (R.ib_adjacent_distinct hB hsingle) R' hsize)

/-- COMPLETE I.B, with singleton-fiber hypotheses ONLY ON THE ORIGINAL RUN.
There is no externally supplied global sector-order, cover, convexity or
matching-chain hypothesis beyond the genuine ActualCaseIRun. -/
theorem hasEmptySix_of_caseIB_run
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (R : ActualCaseIRun P hgp o ho)
    (hsingle : RunHasSingletonSectors R)
    (hB : R.length+2 = (ChainSecond P).card) : HasEmptySix P := by
  by_cases h : CanMatchLeft P hgp o ho (chainCycle P hgp o ho R.last)
  · exact hasEmptySix_of_caseIB_left P hgp hmin o ho R hB hsingle h
  · exact hasEmptySix_of_caseIB_not_left P hgp hmin o ho R hB hsingle h

/-- Natural-number interface avoiding a new definition at the upstream call. -/
theorem hasEmptySix_of_caseIB_singleton_fibers
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (R : ActualCaseIRun P hgp o ho)
    (hsingle : ∀ j : ℕ, j ≤ R.length → ∀ s : ChainVertex P,
      sectorEdge P hgp o ho s = sectorEdge P hgp o ho
        (orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j) →
      s = orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j)
    (hB : R.length+2 = (ChainSecond P).card) : HasEmptySix P :=
  hasEmptySix_of_caseIB_run P hgp hmin o ho R hsingle hB


/-- After I.B is discharged, any remaining short singleton run has precisely
the I.A size range. This does not claim a proof of I.A. -/
theorem ActualCaseIRun.caseA_size_of_short
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hmin : MinimalOuter P) (hno : ¬HasEmptySix P)
    (hsingle : RunHasSingletonSectors R)
    (hshort : R.length+2 ≤ (ChainSecond P).card) :
    R.length+3 ≤ (ChainSecond P).card := by
  by_contra hn
  have hB : R.length+2 = (ChainSecond P).card := by omega
  exact hno (hasEmptySix_of_caseIB_run P hgp hmin o ho R hsingle hB)

end JSP198.Nicolas

#print axioms JSP198.Nicolas.hasEmptySix_of_caseIB_run
#print axioms JSP198.Nicolas.hasEmptySix_of_caseIB_singleton_fibers
