import JSP619Basic

/-! Actual Walk.IsPath / Walk.IsCycle constructions and length-set counting.
No condition in this file is claimed to follow from girth
until it is supplied by the structural modules. -/
noncomputable section
open Finset Function
namespace JSP619
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} {G : SimpleGraph V}

lemma path_start_not_tail {a b : V} {p : G.Walk a b} (hp : p.IsPath) :
    a ∉ p.support.tail := by
  have h := hp.support_nodup
  rw [← p.cons_tail_support, List.nodup_cons] at h
  exact h.1

lemma append_isPath_of_inter {a b c : V} {p : G.Walk a b} {q : G.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = b) :
    (p.append q).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  apply List.disjoint_left.mpr
  intro x hx hxq
  have hxb := hinter x hx (List.mem_of_mem_tail hxq)
  exact path_start_not_tail hq (hxb ▸ hxq)

/-- Two simple paths with only their endpoints in common form a simple cycle,
provided their combined length is at least three. -/
lemma append_isCycle_of_inter {a b : V} {p : G.Walk a b} {q : G.Walk b a}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = a ∨ x = b)
    (hlen : 3 ≤ p.length + q.length) : (p.append q).IsCycle := by
  have hd : p.support.tail.Disjoint q.support.tail := by
    apply List.disjoint_left.mpr
    intro x hx hy
    rcases hinter x (List.mem_of_mem_tail hx) (List.mem_of_mem_tail hy) with h | h
    · exact path_start_not_tail hp (h ▸ hx)
    · exact path_start_not_tail hq (h ▸ hy)
  exact hp.isCycle_append hq hd (by omega)

/-- Same-layer endpoints; the connecting path has all its other vertices strictly below.
The main path stays on or above the layer. -/
lemma cycle_of_high_and_low_paths (level : V → ℕ) (i : ℕ)
    {a b : V} {p : G.Walk a b} {q : G.Walk b a}
    (hp : p.IsPath) (hq : q.IsPath)
    (hhigh : ∀ x ∈ p.support, i ≤ level x)
    (hlow : ∀ x ∈ q.support, x ≠ a → x ≠ b → level x < i)
    (hlen : 3 ≤ p.length + q.length) : (p.append q).IsCycle := by
  apply append_isCycle_of_inter hp hq _ hlen
  intro x hx hy
  by_contra! h
  exact Nat.not_lt_of_ge (hhigh x hx) (hlow x hy h.1 h.2)

section Counting
variable [Fintype V] [DecidableEq V]

/-- Counts a family of actual cycles with pairwise different lengths. -/
theorem card_cycleLengths_ge_of_witnesses {I : Type*} [DecidableEq I]
    (S : Finset I) (len : I → ℕ)
    (hinj : Set.InjOn len (↑S : Set I))
    (hcycles : ∀ t ∈ S, ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = len t) :
    S.card ≤ (cycleLengths G).card := by
  classical
  have hsub : S.image len ⊆ cycleLengths G := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact mem_cycleLengths.mpr (hcycles t ht)
  have hcard : (S.image len).card = S.card := Finset.card_image_iff.mpr hinj
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- A forward subpath has exactly b-a edges, with the stated actual endpoints. -/
lemma forward_subpath {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ p.length) :
    ∃ q : G.Walk (p.getVert a) (p.getVert b),
      q.IsPath ∧ q.length = b - a ∧ ∀ v ∈ q.support, v ∈ p.support := by
  exact ⟨pathSegment p a b hab, pathSegment_isPath hp a b hab,
    pathSegment_length p a b hab hb, fun v hv => pathSegment_support_subset p a b hab hv⟩

/-- Counts equal-offset cycles from targets all on the same side of a fixed path position. -/
theorem fan_on_right {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (level : V → ℕ) (i a h : ℕ) (ha : a ≤ p.length) (hh : 2 ≤ h)
    (B : Finset ℕ)
    (hB : ∀ b ∈ B, a < b ∧ b ≤ p.length)
    (hhigh : ∀ v ∈ p.support, i ≤ level v)
    (hreturn : ∀ b ∈ B, ∃ q : G.Walk (p.getVert b) (p.getVert a),
      q.IsPath ∧ q.length = h ∧
        ∀ v ∈ q.support, v ≠ p.getVert a → v ≠ p.getVert b → level v < i) :
    B.card ≤ (cycleLengths G).card := by
  apply card_le_cycleLengths_of_equal_external_paths hp B hB hh
  intro b hb
  obtain ⟨q, hq, hqlen, hqsupp⟩ := hreturn b hb
  refine ⟨q.reverse, hq.reverse, by simpa using hqlen, ?_⟩
  intro x hx hxP
  have hxq : x ∈ q.support := by simpa using hx
  by_cases hxa : x = p.getVert a
  · exact Or.inl hxa
  by_cases hxb : x = p.getVert b
  · exact Or.inr hxb
  exact (Nat.not_lt_of_ge (hhigh x hxP) (hqsupp x hxq hxa hxb)).elim

/-- The corresponding backward-subpath family. -/
theorem fan_on_left {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (level : V → ℕ) (i a h : ℕ) (ha : a ≤ p.length) (hh : 2 ≤ h)
    (B : Finset ℕ)
    (hB : ∀ b ∈ B, b < a)
    (hhigh : ∀ v ∈ p.support, i ≤ level v)
    (hreturn : ∀ b ∈ B, ∃ q : G.Walk (p.getVert b) (p.getVert a),
      q.IsPath ∧ q.length = h ∧
        ∀ v ∈ q.support, v ≠ p.getVert a → v ≠ p.getVert b → level v < i) :
    B.card ≤ (cycleLengths G).card := by
  apply card_le_cycleLengths_of_equal_external_paths_left hp B
    (fun b hb => ⟨hB b hb, ha⟩) hh
  intro b hb
  obtain ⟨q, hq, hqlen, hqsupp⟩ := hreturn b hb
  refine ⟨q.reverse, hq.reverse, by simpa using hqlen, ?_⟩
  intro x hx hxP
  have hxq : x ∈ q.support := by simpa using hx
  by_cases hxa : x = p.getVert a
  · exact Or.inl hxa
  by_cases hxb : x = p.getVert b
  · exact Or.inr hxb
  exact (Nat.not_lt_of_ge (hhigh x hxP) (hqsupp x hxq hxa hxb)).elim

/-- Without choosing a side in advance, the loss is at most a factor of two. -/
theorem fan_count {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (level : V → ℕ) (i a h : ℕ) (ha : a ≤ p.length) (hh : 2 ≤ h)
    (B : Finset ℕ)
    (hB : ∀ b ∈ B, b ≠ a ∧ b ≤ p.length)
    (hhigh : ∀ v ∈ p.support, i ≤ level v)
    (hreturn : ∀ b ∈ B, ∃ q : G.Walk (p.getVert b) (p.getVert a),
      q.IsPath ∧ q.length = h ∧
        ∀ v ∈ q.support, v ≠ p.getVert a → v ≠ p.getVert b → level v < i) :
    B.card ≤ 2 * (cycleLengths G).card := by
  classical
  let L := B.filter (fun b => b < a)
  let R := B.filter (fun b => a < b)
  have hL : L.card ≤ (cycleLengths G).card := by
    apply fan_on_left p hp level i a h ha hh L
    · intro b hb
      exact (Finset.mem_filter.mp hb).2
    · exact hhigh
    · intro b hb
      exact hreturn b (Finset.mem_filter.mp hb).1
  have hR : R.card ≤ (cycleLengths G).card := by
    apply fan_on_right p hp level i a h ha hh R
    · intro b hb
      exact ⟨(Finset.mem_filter.mp hb).2, (hB b (Finset.mem_filter.mp hb).1).2⟩
    · exact hhigh
    · intro b hb
      exact hreturn b (Finset.mem_filter.mp hb).1
  have hcover : B = L ∪ R := by
    ext b
    simp only [L, R, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hb
      rcases lt_or_gt_of_ne (hB b hb).1 with hlt | hgt
      · exact Or.inl ⟨hb, hlt⟩
      · exact Or.inr ⟨hb, hgt⟩
    · tauto
  have hdis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro b hb hc
    have h1 := (Finset.mem_filter.mp hb).2
    have h2 := (Finset.mem_filter.mp hc).2
    omega
  rw [hcover, Finset.card_union_of_disjoint hdis]
  omega

end Counting

#print axioms append_isPath_of_inter
#print axioms fan_count

end JSP619
end
