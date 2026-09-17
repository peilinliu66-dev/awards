/-
Released under the MIT license.
Actual finite Case I runs, obtained from the genuine boundary permutation and
proved left/right match availability. In a singleton-sector configuration,
the first failed right match is reached before any vertex can repeat.
This file does not assume a run, sector injectivity, or a geometric cover.
Mathematical source: C. M. Nicolas, The Empty Hexagon Theorem (2007).
-/
import Mathlib
import JSP198NicolasCaseICCover

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

lemma chain_orbit_add {A : Type*} (f : A → A) (x : A) (m n : ℕ) :
    orbit f x (m + n) = orbit f (orbit f x m) n := by
  induction n with
  | zero => simp only [Nat.add_zero, orbit]
  | succ n ih =>
      change f (orbit f x (m + n)) = f (orbit f (orbit f x m) n)
      rw [ih]

/-- A deterministic orbit cannot repeat before its first failed predicate.
Neither a cyclic-order premise nor injectivity of the underlying map is needed. -/
lemma first_failure_prefix_injective
    {A : Type*} (f : A → A) (x : A) (B : A → Prop) (k : ℕ)
    (hbefore : ∀ j : ℕ, j < k → B (orbit f x j))
    (hstop : ¬ B (orbit f x k)) :
    Function.Injective (fun j : Fin (k + 1) => orbit f x j.val) := by
  have hforbid : ∀ i j : ℕ, i < j → j ≤ k →
      orbit f x i = orbit f x j → False := by
    intro i j hij hjk he
    have hs := congrArg (fun y : A => orbit f y (k - j)) he
    rw [← chain_orbit_add f x i (k-j), ← chain_orbit_add f x j (k-j)] at hs
    have hj : j + (k - j) = k := Nat.add_sub_of_le hjk
    rw [hj] at hs
    have hi : i + (k-j) < k := by omega
    exact hstop (hs ▸ hbefore (i+(k-j)) hi)
  intro i j he
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact (hforbid i.val j.val h (by omega) he).elim
  · exact h
  · exact (hforbid j.val i.val h (by omega) he.symm).elim

/-- Finite first-failure construction, including the exact no-repetition bound. -/
lemma exists_first_failure_prefix
    {A : Type*} [Fintype A] (f : A → A) (x : A) (B : A → Prop)
    (hx : B x) (hevent : ∃ j : ℕ, ¬ B (orbit f x j)) :
    ∃ k : ℕ, 0 < k ∧ k < Fintype.card A ∧
      (∀ j : ℕ, j < k → B (orbit f x j)) ∧
      ¬ B (orbit f x k) ∧
      Function.Injective (fun j : Fin (k + 1) => orbit f x j.val) := by
  let k := Nat.find hevent
  have hstop : ¬ B (orbit f x k) := Nat.find_spec hevent
  have hbefore : ∀ j : ℕ, j < k → B (orbit f x j) := by
    intro j hj
    by_contra hn
    exact Nat.find_min hevent hj hn
  have hpos : 0 < k := by
    by_contra hn
    have hk : k = 0 := by omega
    apply hstop
    simpa only [hk,orbit] using hx
  have hinj := first_failure_prefix_injective f x B k hbefore hstop
  have hcard := Fintype.card_le_of_injective
    (fun j : Fin (k+1) => orbit f x j.val) hinj
  simp only [Fintype.card_fin] at hcard
  exact ⟨k,hpos,by omega,hbefore,hstop,hinj⟩

/-- Data PRODUCED by `exists_actual_caseI_run` below. None of the global geometry
is assumed by declaring a final theorem with this structure as its hypothesis. -/
structure ActualCaseIRun
    (P : Finset Point) (hgp : GeneralPosition P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) where
  first : ChainVertex P
  length : ℕ
  positive : 0 < length
  shorter : length < (ChainSecond P).card
  noLeft : ¬ CanMatchLeft P hgp o ho first
  right_before : ∀ j : ℕ, j < length →
    CanMatchRight P hgp o ho (orbit (α := ChainVertex P) (chainCycle P hgp o ho) first j)
  noRight_end : ¬ CanMatchRight P hgp o ho
    (orbit (α := ChainVertex P) (chainCycle P hgp o ho) first length)
  prefix_injective : Function.Injective
    (fun j : Fin (length+1) => orbit (α := ChainVertex P) (chainCycle P hgp o ho) first j.val)

namespace ActualCaseIRun

def last {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho) : ChainVertex P :=
  orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first R.length

lemma first_ne_last {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho) : R.first ≠ R.last := by
  intro he
  have h0 : (0 : ℕ) < R.length + 1 := by omega
  have hk : R.length < R.length + 1 := by omega
  have hi : (⟨0,h0⟩ : Fin (R.length+1)) = ⟨R.length,hk⟩ :=
    R.prefix_injective (show orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first 0 =
      orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first R.length from he)
  have hz := congrArg Fin.val hi
  have hp := R.positive
  simp only at hz
  omega

lemma end_canMatchLeft
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hmin : MinimalOuter P) (hno : ¬ HasEmptySix P) :
    CanMatchLeft P hgp o ho R.last := by
  rcases actual_match_left_or_right P hgp hmin hno o ho R.last with h | h
  · exact h
  · exact (R.noRight_end h).elim

/-- Distinct actual inner vertices, not merely distinct integer sector labels. -/
lemma inner_starts_injective
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hno : ¬ HasEmptySix P) (hdiff : AdjacentSectorsDistinct P hgp o ho) :
    Function.Injective (fun j : Fin (R.length+1) =>
      sectorVertex P hgp o ho (orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j.val)) :=
  (sectorVertex_injective_of_adjacent_distinct P hgp hno o ho hdiff).comp
    R.prefix_injective

/-- Each successive sector start crosses its actual outer edge. This is the
geometric order certificate retained on the run; no sorted-label axiom is used. -/
lemma swept_starts
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hdiff : AdjacentSectorsDistinct P hgp o ho) (j : ℕ) :
    InFan o (orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j)
      (orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first (j+1))
      (matchStart P hgp o ho (orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first (j+1))) := by
  exact next_sector_start_in_swept_edge P hgp o ho
    (orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j)
    (hdiff (orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j))

/-- A full-length Case I run enumerates all second-layer vertices. -/
lemma prefix_surjective_of_full
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hfull : R.length+1 = (ChainSecond P).card) :
    Function.Surjective
      (fun j : Fin (R.length+1) => orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j.val) := by
  let g := fun j : Fin (R.length+1) => orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j.val
  let image := (Finset.univ : Finset (Fin (R.length+1))).image g
  have hsize : image.card = (ChainSecond P).card := by
    dsimp [image]
    rw [Finset.card_image_of_injective _ R.prefix_injective,
      Finset.card_univ,Fintype.card_fin,hfull]
  have hwhole : image = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    have hcard : Fintype.card (ChainVertex P) = (ChainSecond P).card :=
      Fintype.card_coe _
    simpa only [Finset.card_univ,hcard,hsize] using (le_refl (ChainSecond P).card)
  intro r
  have hr : r ∈ image := by rw [hwhole]; exact Finset.mem_univ _
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hr
  exact ⟨j,hj⟩

/-- In a full run the terminal successor really is the initial vertex.
This discharges the closing-index equality needed by the local I.C geometry. -/
lemma cycle_closes_of_full
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hfull : R.length+1 = (ChainSecond P).card) :
    chainCycle P hgp o ho R.last = R.first := by
  let f := chainCycle P hgp o ho
  obtain ⟨j,hj⟩ := R.prefix_surjective_of_full hfull (f R.last)
  by_cases hj0 : j.val = 0
  · have he : R.first = f R.last := by simpa only [hj0,orbit] using hj
    exact he.symm
  · have hjpos : 0 < j.val := by omega
    have hjstep : j.val-1+1 = j.val := by omega
    have he : orbit f R.first (j.val-1) = R.last := by
      apply f.injective
      change orbit f R.first (j.val-1+1) = f R.last
      rw [hjstep]
      exact hj
    have ha : j.val-1 < R.length+1 := by have := j.isLt; omega
    have hb : R.length < R.length+1 := by omega
    have hi : (⟨j.val-1,ha⟩ : Fin (R.length+1)) = ⟨R.length,hb⟩ :=
      R.prefix_injective he
    have hv := congrArg Fin.val hi
    have hjlt := j.isLt
    simp only at hv
    omega

lemma right_everywhere_except_last_of_full
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hfull : R.length+1 = (ChainSecond P).card) :
    ∀ r : ChainVertex P, r ≠ R.last → CanMatchRight P hgp o ho r := by
  intro r hr
  obtain ⟨j,hj⟩ := R.prefix_surjective_of_full hfull r
  have hjne : j.val ≠ R.length := by
    intro he
    apply hr
    rw [← hj]
    change orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first j.val =
      orbit (α := ChainVertex P) (chainCycle P hgp o ho) R.first R.length
    rw [he]
  have hjlt : j.val < R.length := by have := j.isLt; omega
  rw [← hj]
  exact R.right_before j.val hjlt

/-- Actual full runs satisfy all conclusions of the first half of I.C, including
an ACTUAL exterior cover, tight cardinalities, and exact cyclic successor order. -/
theorem tight_structure_of_full
    {P : Finset Point} {hgp : GeneralPosition P}
    {o : Point} {ho : o ∈ inner (inner (inner P))}
    (R : ActualCaseIRun P hgp o ho)
    (hmin : MinimalOuter P) (hno : ¬ HasEmptySix P)
    (hdiff : AdjacentSectorsDistinct P hgp o ho)
    (hfull : R.length+1 = (ChainSecond P).card) :
    (ChainThird P).card = (ChainSecond P).card ∧
    (hullVertices P).card = (ChainSecond P).card + 1 ∧
    Function.Bijective (sectorVertex P hgp o ho) ∧
    (∀ r : ChainVertex P,
      matchEnd P hgp o ho r = matchStart P hgp o ho (chainCycle P hgp o ho r)) :=
  caseIC_tight_structure P hgp hmin hno o ho hdiff R.last
    (R.right_everywhere_except_last_of_full hfull)

end ActualCaseIRun

/-- A genuine singleton-sector minimal counterexample supplies a Case I run.
All-left and all-right possibilities are ruled out by PROVED geometric covers. -/
theorem exists_actual_caseI_run
    (P : Finset Point) (hgp : GeneralPosition P)
    (hmin : MinimalOuter P) (hno : ¬ HasEmptySix P)
    (o : Point) (ho : o ∈ inner (inner (inner P)))
    (hdiff : AdjacentSectorsDistinct P hgp o ho) :
    Nonempty (ActualCaseIRun P hgp o ho) := by
  have hL : ∃ r : ChainVertex P, ¬ CanMatchLeft P hgp o ho r := by
    by_contra hn
    have hall : ∀ r, CanMatchLeft P hgp o ho r := by
      intro r
      by_contra hr
      exact hn ⟨r,hr⟩
    exact hno (hasEmptySix_of_all_left_matches P hgp hmin o ho hdiff hall)
  have hR : ∃ r : ChainVertex P, ¬ CanMatchRight P hgp o ho r := by
    by_contra hn
    have hall : ∀ r, CanMatchRight P hgp o ho r := by
      intro r
      by_contra hr
      exact hn ⟨r,hr⟩
    exact hno (hasEmptySix_of_all_right_matches P hgp hmin o ho hdiff hall)
  obtain ⟨first,hfirst⟩ := hL
  obtain ⟨bad,hbad⟩ := hR
  have hfirstR : CanMatchRight P hgp o ho first := by
    rcases actual_match_left_or_right P hgp hmin hno o ho first with h | h
    · exact (hfirst h).elim
    · exact h
  obtain ⟨j,_,hj⟩ := chainCycle_reaches P hgp o ho first bad
  have hevent : ∃ j : ℕ,
      ¬ CanMatchRight P hgp o ho (orbit (α := ChainVertex P) (chainCycle P hgp o ho) first j) :=
    ⟨j,by simpa only [hj] using hbad⟩
  obtain ⟨k,hk0,hkcard,hbefore,hstop,hinj⟩ := exists_first_failure_prefix
    (chainCycle P hgp o ho) first (CanMatchRight P hgp o ho) hfirstR hevent
  have hcard : Fintype.card (ChainVertex P) = (ChainSecond P).card := Fintype.card_coe _
  rw [hcard] at hkcard
  exact ⟨⟨first,k,hk0,hkcard,hfirst,hbefore,hstop,hinj⟩⟩

/-- Exact geometric classification remaining after this batch. The right side
is NOT presented as a completed six-hole theorem: short-run replacement and
double-sector bridging are the remaining branches. -/
theorem actual_four_layer_case_split
    (P : Finset Point) (hgp : GeneralPosition P) (hmin : MinimalOuter P)
    (o : Point) (ho : o ∈ inner (inner (inner P))) :
    HasEmptySix P ∨ Nonempty (ActualCaseIRun P hgp o ho) ∨
      ∃ r : ChainVertex P,
        sectorEdge P hgp o ho r = sectorEdge P hgp o ho (chainCycle P hgp o ho r) := by
  by_cases h : HasEmptySix P
  · exact Or.inl h
  by_cases hd : AdjacentSectorsDistinct P hgp o ho
  · exact Or.inr (Or.inl (exists_actual_caseI_run P hgp hmin h o ho hd))
  · right; right
    by_contra hn
    apply hd
    intro r he
    exact hn ⟨r,he⟩

end JSP198.Nicolas

#print axioms JSP198.Nicolas.exists_actual_caseI_run
#print axioms JSP198.Nicolas.actual_four_layer_case_split
#print axioms JSP198.Nicolas.ActualCaseIRun.tight_structure_of_full
