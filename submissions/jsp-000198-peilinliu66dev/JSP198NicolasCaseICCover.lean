/-
Released under the MIT license.
Nicolas Case I.C: ACTUAL covering by all right-match channels except one
closing vertex fan; the sharp layer cardinalities and no-skipping conclusion.
The later one-outer-point gluing is deliberately not redeveloped here.
-/
import Mathlib
import JSP198NicolasSweptOrder

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

/-- This is the full covering appearing at the start of Case I.C, with all
order-preservation proved by the common determinant-cover theorem. -/
theorem caseIC_one_fan_cover
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho)
    (last : ChainVertex P)
    (hright : ∀ r : ChainVertex P, r ≠ last → CanMatchRight P hgp o ho r) :
    ∀ x ∈ hullVertices P,
      x ∈ outerFan P (matchStart P hgp o ho (chainCycle P hgp o ho last))
        (last, chainCycle P hgp o ho last) ∨
      ∃ r : ChainVertex P, r ≠ last ∧
        x ∈ matchChannel P r (chainCycle P hgp o ho r)
          (matchStart P hgp o ho r) (matchEnd P hgp o ho r) := by
  let f := chainCycle P hgp o ho
  let first := f last
  let z := matchStart P hgp o ho first
  let c := fun r : ChainVertex P => if r = last then z else matchStart P hgp o ho r
  let d := fun r : ChainVertex P => if r = last then z else matchEnd P hgp o ho r
  have hfirst : first ≠ last := by
    intro he
    have hh := (chainCycle_edge P hgp o ho last).2.2.1
    exact hh (congrArg (fun r : ChainVertex P => (r : Point)) he).symm
  have hc : ∀ r, c r ∈ inner (inner P) := by
    intro r
    by_cases hr : r = last
    · simpa only [c,if_pos hr] using matchStart_mem P hgp o ho first
    · simpa only [c,if_neg hr] using matchStart_mem P hgp o ho r
  have hd : ∀ r, d r ∈ inner (inner P) := by
    intro r
    by_cases hr : r = last
    · simpa only [d,if_pos hr] using matchStart_mem P hgp o ho first
    · simpa only [d,if_neg hr] using matchEnd_mem P hgp o ho r
  have hshape : ∀ r : ChainVertex P, c r = d r ∨
      (0 < orient (r : Point) (c r) (d r) ∧
       0 < orient (r : Point) (c r) (f r : Point) ∧
       0 < orient (r : Point) (d r) (f r : Point) ∧
       0 < orient (c r) (d r) (f r : Point)) := by
    intro r
    by_cases hr : r = last
    · left; simp only [c,d,if_pos hr]
    · right
      simp only [c,d,if_neg hr]
      exact boundary_match_four_signs P hgp r (f r)
        (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
        (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho r)
        (sectorEdge_outward P hgp o ho r) (hright r hr)
  have hgap : ∀ r : ChainVertex P, 0 ≤ orient (f r : Point) (d r) (c (f r)) := by
    intro r
    by_cases hr : r = last
    · subst r
      have heq : c (f last) = z := by
        change (if first = last then z else matchStart P hgp o ho first) = z
        rw [if_neg hfirst]
      rw [show d last = z by simp [d],heq]
      unfold orient
      nlinarith
    · by_cases hnext : f r = last
      · have hh := skipped_sector_join_positive P hgp o ho hdiff r
        change 0 < orient (f r : Point) (matchEnd P hgp o ho r)
          (matchStart P hgp o ho (f (f r))) at hh
        rw [hnext] at hh
        simpa only [c,d,if_neg hr,if_pos hnext,hnext,z,first,ite_true] using hh.le
      · simpa only [c,d,if_neg hr,if_neg hnext] using
          right_radial_join_coherent P hgp o ho r (hdiff r) (hright r hr)
  intro x hx
  obtain ⟨r,hr⟩ := coherent_strips_cover P hgp o ho c d hc hd hshape hgap x hx
  by_cases he : r = last
  · left
    subst r
    have hh : stripCell P last (f last) (c last) (d last) =
        outerFan P z (last,f last) := by
      simp only [c,d,if_pos rfl]
      exact stripCell_self_eq_outerFan P last (f last) z
    rwa [hh] at hr
  · right
    refine ⟨r,he,?_⟩
    simp only [c,d,if_neg he] at hr
    rw [stripCell_eq_matchChannel _ _ _ _ _
      (matchStartEnd_edge P hgp o ho r).2.2.1] at hr
    exact hr

/-- Exact finite count from the proved Case I.C cover: n−1 channels of capacity
one, plus a single closing fan of capacity two. -/
theorem caseIC_outer_card_le_second_add_one
    (P : Finset Point) (hgp : GeneralPosition P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho)
    (last : ChainVertex P)
    (hright : ∀ r : ChainVertex P, r ≠ last → CanMatchRight P hgp o ho r) :
    (hullVertices P).card ≤ (ChainSecond P).card + 1 := by
  let f := chainCycle P hgp o ho
  let first := f last
  let z := matchStart P hgp o ho first
  let fan := outerFan P z (last,first)
  let cells := fun r : ChainVertex P =>
    if r = last then fan else
      matchChannel P r (f r) (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
  have hfan : fan.card ≤ 2 := by
    have hzII := matchStart_mem P hgp o ho first
    apply outerFan_card_le_two P hgp hno z (Finset.mem_sdiff.mp hzII).1
      (last,first) (chainCycle_edge P hgp o ho last)
    · exact chain_inner2_ne_second hzII last
    · exact chain_inner2_ne_second hzII first
  have hcover : ∀ x ∈ hullVertices P,
      ∃ r ∈ (Finset.univ : Finset (ChainVertex P)), x ∈ cells r := by
    intro x hx
    rcases caseIC_one_fan_cover P hgp o ho hdiff last hright x hx with h | ⟨r,hr,h⟩
    · exact ⟨last,Finset.mem_univ _,by simpa only [cells,if_pos rfl] using h⟩
    · exact ⟨r,Finset.mem_univ _,by simpa only [cells,if_neg hr] using h⟩
  have hbound : ∀ r : ChainVertex P, (cells r).card ≤ 1 + if r = last then 1 else 0 := by
    intro r
    by_cases hr : r = last
    · simpa only [cells,if_pos hr] using hfan
    · have hh := boundary_match_channel_le_one P hgp hno r (f r)
        (matchStart P hgp o ho r) (matchEnd P hgp o ho r)
        (chainCycle_edge P hgp o ho r) (matchStartEnd_edge P hgp o ho r)
        (sectorEdge_outward P hgp o ho r) (hright r hr)
      simpa only [cells,if_neg hr,Nat.add_zero] using hh
  have hc := card_le_sum_of_cover (hullVertices P) Finset.univ cells hcover
  have hs : (∑ r : ChainVertex P, (cells r).card) ≤ (ChainSecond P).card + 1 := by
    calc
      (∑ r : ChainVertex P, (cells r).card) ≤
          ∑ r : ChainVertex P, (1 + if r = last then 1 else 0 : ℕ) :=
        Finset.sum_le_sum (fun r _ => hbound r)
      _ = (ChainSecond P).card + 1 := by
        rw [Finset.sum_add_distrib]
        simp [ChainVertex]
  exact hc.trans hs

/-- The whole first half of Case I.C, now without a presumed exterior cover or
presumed exact sector order. The remaining local six-point gluing is separate. -/
theorem caseIC_tight_structure
    (P : Finset Point) (hgp : GeneralPosition P)
    (hmin : MinimalOuter P) (hno : ¬HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho)
    (last : ChainVertex P)
    (hright : ∀ r : ChainVertex P, r ≠ last → CanMatchRight P hgp o ho r) :
    (ChainThird P).card = (ChainSecond P).card ∧
    (hullVertices P).card = (ChainSecond P).card + 1 ∧
    Function.Bijective (sectorVertex P hgp o ho) ∧
    (∀ r : ChainVertex P,
      matchEnd P hgp o ho r = matchStart P hgp o ho (chainCycle P hgp o ho r)) :=
  tight_layer_sizes_and_successors P hgp hmin hno o ho hdiff
    (caseIC_outer_card_le_second_add_one P hgp hno o ho hdiff last hright)

end JSP198.Nicolas

#print axioms JSP198.Nicolas.caseIC_tight_structure
#print axioms JSP198.Nicolas.caseIC_one_fan_cover
