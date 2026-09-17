import Mathlib

set_option maxHeartbeats 1600000

namespace JSP619
namespace Moore
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {s : ℕ}

theorem short_paths_eq
    (hgirth : ∀ v (p : G.Walk v v), p.IsCycle → 2 * s < p.length)
    {u v : V} {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length ≤ 2 * s) : p = q := by
  by_contra hne
  obtain ⟨w, _, _, c, hc, hclen⟩ := hp.exists_isCycle_length_le_add_of_ne hq hne
  have := hgirth w c hc
  omega

theorem neighbor_on_short_path
    (hgirth : ∀ v (p : G.Walk v v), p.IsCycle → 2 * s < p.length)
    {u v w : V} (p : G.Walk u v) (hp : p.IsPath)
    (hlen : p.length + 1 ≤ 2 * s) (hw : G.Adj v w) (hwmem : w ∈ p.support) :
    w = p.penultimate := by
  have heq : p.dropUntil w hwmem = hw.symm.toWalk :=
    short_paths_eq hgirth (hp.dropUntil hwmem) hw.symm.isPath_toWalk (by
      have := p.length_dropUntil_le_length hwmem
      simp only [Adj.length_toWalk]
      omega)
  apply hp.eq_penultimate_of_mem_edges
  apply p.edges_dropUntil_subset_edges hwmem
  rw [heq]
  simp [Sym2.eq_swap]

abbrev Paths (G : SimpleGraph V) (r : V) (n : ℕ) :=
  Σ v : V, {p : G.Walk r v // p.IsPath ∧ p.length = n}

theorem card_paths_le (r : V) (n : ℕ) (hn : n ≤ s)
    (hgirth : ∀ v (p : G.Walk v v), p.IsCycle → 2 * s < p.length) :
    Fintype.card (Paths G r n) ≤ Fintype.card V := by
  apply Fintype.card_le_of_injective Sigma.fst
  rintro ⟨v, p, hp, hplen⟩ ⟨w, q, hq, hqlen⟩ heq
  dsimp at heq
  subst w
  have : p = q := short_paths_eq hgirth hp hq (by omega)
  subst q
  rfl

abbrev Extensions (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) (n : ℕ) :=
  Σ p : Paths G r n, ↥((G.neighborFinset p.1).erase p.2.1.penultimate)

noncomputable instance (r : V) (n : ℕ) : Fintype (Extensions G r n) := by
  unfold Extensions
  infer_instance

noncomputable def extend (r : V) (n : ℕ) (hn : n < s)
    (hgirth : ∀ v (p : G.Walk v v), p.IsCycle → 2 * s < p.length)
    (e : Extensions G r n) : Paths G r (n + 1) := by
  let p := e.1.2.1
  have hadj : G.Adj e.1.1 e.2.1 := (G.mem_neighborFinset _ _).mp
    (mem_erase.mp e.2.2).2
  have hnot : e.2.1 ∉ p.support := by
    intro hmem
    have := neighbor_on_short_path hgirth p e.1.2.2.1 (by
      have := e.1.2.2.2
      dsimp [p]
      omega) hadj hmem
    exact (mem_erase.mp e.2.2).1 this
  exact ⟨e.2.1, p.concat hadj, e.1.2.2.1.concat hnot hadj,
    by simp only [Walk.length_concat, e.1.2.2.2, p]⟩

theorem extend_injective (r : V) (n : ℕ) (hn : n < s)
    (hgirth : ∀ v (p : G.Walk v v), p.IsCycle → 2 * s < p.length) :
    Function.Injective (extend r n hn hgirth) := by
  rintro ⟨⟨v, p, hp, hplen⟩, w, hw⟩ ⟨⟨v', p', hp', hplen'⟩, w', hw'⟩ heq
  have hww : w = w' := congrArg Sigma.fst heq
  subst w'
  have hppeq := congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)
  change p.concat _ = p'.concat _ at hppeq
  obtain ⟨hvv, hpp⟩ := Walk.concat_inj hppeq
  subst v'
  simp only [Walk.copy_rfl_rfl] at hpp
  subst p'
  rfl

theorem extension_card_lower (r : V) (n d : ℕ)
    (hdeg : ∀ v, d + 1 ≤ G.degree v) :
    d * Fintype.card (Paths G r n) ≤ Fintype.card (Extensions G r n) := by
  classical
  unfold Extensions
  conv_rhs => rw [Fintype.card_sigma]
  calc
    d * Fintype.card (Paths G r n) = ∑ _p : Paths G r n, d := by simp [mul_comm]
    _ ≤ ∑ p : Paths G r n, Fintype.card ↥((G.neighborFinset p.1).erase p.2.1.penultimate) := by
      apply sum_le_sum
      intro p _
      simp only [Fintype.card_coe]
      have h := pred_card_le_card_erase (s := G.neighborFinset p.1)
        (a := p.2.1.penultimate)
      rw [G.card_neighborFinset_eq_degree] at h
      have := hdeg p.1
      omega

theorem card_paths_one (r : V) (d : ℕ) (hdeg : d + 1 ≤ G.degree r) :
    d + 1 ≤ Fintype.card (Paths G r 1) := by
  let f : G.neighborSet r → Paths G r 1 := fun w =>
    ⟨w.1, w.2.toWalk, w.2.isPath_toWalk, w.2.length_toWalk⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg Sigma.fst h)
  have hcard := Fintype.card_le_of_injective f hf
  rw [G.card_neighborSet_eq_degree] at hcard
  exact hdeg.trans hcard

theorem card_paths_gt_pow (r : V) (d : ℕ) (hd : 1 ≤ d)
    (hdeg : ∀ v, d + 1 ≤ G.degree v)
    (hgirth : ∀ v (p : G.Walk v v), p.IsCycle → 2 * s < p.length)
    (n : ℕ) (hn0 : 1 ≤ n) (hn : n ≤ s) :
    d ^ n < Fintype.card (Paths G r n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hnzero : n = 0
    · subst n
      have := card_paths_one r d (hdeg r)
      simpa using (show d < Fintype.card (Paths G r 1) by omega)
    · have hprev := ih (by omega) (by omega)
      have hmul := Nat.mul_lt_mul_of_pos_left hprev (by omega : 0 < d)
      have hinj := Fintype.card_le_of_injective (extend r n (by omega) hgirth)
        (extend_injective r n (by omega) hgirth)
      have hlow := extension_card_lower r n d hdeg
      rw [pow_succ']
      exact hmul.trans_le (hlow.trans hinj)

end Moore

theorem moore_card_gt_pow {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d s : ℕ)
    (hd : 1 ≤ d) (hs : 1 ≤ s) (hdeg : ∀ v, d + 1 ≤ G.degree v)
    (hgirth : ∀ v (p : G.Walk v v), p.IsCycle → 2 * s < p.length) :
    d ^ s < Fintype.card V := by
  obtain ⟨r⟩ := ‹Nonempty V›
  exact (Moore.card_paths_gt_pow r d hd hdeg hgirth s hs le_rfl).trans_le
    (Moore.card_paths_le r s le_rfl hgirth)

#print axioms moore_card_gt_pow
end JSP619
