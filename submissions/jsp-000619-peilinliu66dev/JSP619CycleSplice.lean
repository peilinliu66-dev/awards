import Mathlib

/-!
Splicing a subpath with an internally disjoint detour.  The resulting objects
are Mathlib `Walk.IsCycle` witnesses, and their exact edge counts are retained.
-/

namespace JSP619

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- Two paths which meet only at their endpoints form a cycle, provided one
of them has at least two edges. -/
theorem isCycle_append_reverse_of_intersection
    {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x ∈ q.support, x ∈ p.support → x = u ∨ x = v)
    (hlen : 2 ≤ q.length) : (p.append q.reverse).IsCycle := by
  have hpstart : u ∉ p.support.tail := by
    have h := hp.support_nodup
    rw [← p.cons_tail_support, List.nodup_cons] at h
    exact h.1
  have hqstart : v ∉ q.reverse.support.tail := by
    have h := hq.reverse.support_nodup
    rw [← q.reverse.cons_tail_support, List.nodup_cons] at h
    exact h.1
  apply hp.isCycle_append hq.reverse
  · rw [List.disjoint_left]
    intro x hxp hxq
    have hxp' : x ∈ p.support := List.mem_of_mem_tail hxp
    have hxq' : x ∈ q.support := by
      have := List.mem_of_mem_tail hxq
      simpa only [Walk.support_reverse, List.mem_reverse] using this
    rcases hinter x hxq' hxp' with rfl | rfl
    · exact hpstart hxp
    · exact hqstart hxq
  · exact Or.inr (by rw [Walk.length_reverse]; omega)

/-- A segment indexed in the original path, with exact endpoint types. -/
def pathSegment (p : G.Walk u v) (a j : ℕ) (haj : a ≤ j) :
    G.Walk (p.getVert a) (p.getVert j) :=
  ((p.take j).drop a).copy (by
    rw [Walk.take_getVert, Nat.min_eq_right haj]) rfl

theorem pathSegment_isPath {p : G.Walk u v} (hp : p.IsPath)
    (a j : ℕ) (haj : a ≤ j) : (pathSegment p a j haj).IsPath := by
  unfold pathSegment
  rw [Walk.isPath_copy]
  exact (hp.take j).drop a

theorem pathSegment_length (p : G.Walk u v) (a j : ℕ) (haj : a ≤ j)
    (hj : j ≤ p.length) : (pathSegment p a j haj).length = j - a := by
  simp only [pathSegment, Walk.length_copy, Walk.drop_length, Walk.take_length,
    Nat.min_eq_left hj]

theorem pathSegment_support_subset (p : G.Walk u v) (a j : ℕ) (haj : a ≤ j) :
    (pathSegment p a j haj).support ⊆ p.support := by
  intro x hx
  simp only [pathSegment, Walk.support_copy] at hx
  exact (p.isSubwalk_take j).support_subset
    (((p.take j).isSubwalk_drop a).support_subset hx)

/-- The detour from indices `a` to `j` closes the intervening path segment
into a simple cycle of exactly `ℓ + j - a` edges. -/
theorem exists_cycle_of_external_path {p : G.Walk u v} (hp : p.IsPath)
    {a j ℓ : ℕ} (haj : a < j) (hj : j ≤ p.length) (hℓ : 2 ≤ ℓ)
    (q : G.Walk (p.getVert a) (p.getVert j)) (hq : q.IsPath)
    (hql : q.length = ℓ)
    (hinter : ∀ x ∈ q.support, x ∈ p.support →
      x = p.getVert a ∨ x = p.getVert j) :
    ∃ c : G.Walk (p.getVert a) (p.getVert a),
      c.IsCycle ∧ c.length = ℓ + j - a := by
  let s := pathSegment p a j haj.le
  refine ⟨s.append q.reverse, ?_, ?_⟩
  · apply isCycle_append_reverse_of_intersection (pathSegment_isPath hp a j haj.le) hq
    · intro x hxq hxs
      exact hinter x hxq (pathSegment_support_subset p a j haj.le hxs)
    · omega
  · have hs : s.length = j - a := pathSegment_length p a j haj.le hj
    simp only [Walk.length_append, Walk.length_reverse]
    omega

/-- The finite set of all actual simple-cycle lengths in a finite graph. -/
noncomputable def cycleLengths [Fintype V] (G : SimpleGraph V) : Finset ℕ := by
  classical
  exact (Finset.range (Fintype.card V + 1)).filter fun n =>
    ∃ x : V, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = n

theorem cycle_length_le_card [Fintype V] {x : V} {c : G.Walk x x}
    (hc : c.IsCycle) : c.length ≤ Fintype.card V := by
  have h := hc.support_nodup.length_le_card
  simpa only [List.length_tail, Walk.length_support, Nat.add_sub_cancel] using h

theorem mem_cycleLengths_iff [Fintype V] {n : ℕ} :
    n ∈ cycleLengths G ↔ ∃ x : V, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = n := by
  classical
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · rintro ⟨x, c, hc, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.lt_succ_of_le (cycle_length_le_card hc)), x, c, hc, rfl⟩

/-- The exact cycle-length witness at each chosen later path index. -/
theorem cycles_of_equal_external_paths {p : G.Walk u v} (hp : p.IsPath)
    {a ℓ : ℕ} (B : Finset ℕ)
    (hB : ∀ j ∈ B, a < j ∧ j ≤ p.length) (hℓ : 2 ≤ ℓ)
    (hdetour : ∀ j ∈ B, ∃ q : G.Walk (p.getVert a) (p.getVert j),
      q.IsPath ∧ q.length = ℓ ∧
        ∀ x ∈ q.support, x ∈ p.support → x = p.getVert a ∨ x = p.getVert j) :
    ∀ j ∈ B, ∃ c : G.Walk (p.getVert a) (p.getVert a),
      c.IsCycle ∧ c.length = ℓ + j - a := by
  intro j hj
  obtain ⟨q, hq, hql, hinter⟩ := hdetour j hj
  exact exists_cycle_of_external_path hp (hB j hj).1 (hB j hj).2 hℓ q hq hql hinter

/-- Distinct indices give distinct actual cycle lengths. -/
theorem card_le_cycleLengths_of_equal_external_paths [Fintype V]
    {p : G.Walk u v} (hp : p.IsPath) {a ℓ : ℕ} (B : Finset ℕ)
    (hB : ∀ j ∈ B, a < j ∧ j ≤ p.length) (hℓ : 2 ≤ ℓ)
    (hdetour : ∀ j ∈ B, ∃ q : G.Walk (p.getVert a) (p.getVert j),
      q.IsPath ∧ q.length = ℓ ∧
        ∀ x ∈ q.support, x ∈ p.support → x = p.getVert a ∨ x = p.getVert j) :
    B.card ≤ (cycleLengths G).card := by
  classical
  have hcycles := cycles_of_equal_external_paths hp B hB hℓ hdetour
  have hinj : Set.InjOn (fun j => ℓ + j - a) (↑B : Set ℕ) := by
    intro i hi j hj heq
    have hi' := (hB i hi).1
    have hj' := (hB j hj).1
    change ℓ + i - a = ℓ + j - a at heq
    omega
  have hsub : B.image (fun j => ℓ + j - a) ⊆ cycleLengths G := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨c, hc, hcl⟩ := hcycles j hj
    exact mem_cycleLengths_iff.mpr ⟨p.getVert a, c, hc, hcl⟩
  calc
    B.card = (B.image (fun j => ℓ + j - a)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (cycleLengths G).card := Finset.card_le_card hsub

/-- The corresponding construction when the detour goes to an earlier index.
The cycle is still based at the fixed vertex `p.getVert a`. -/
theorem exists_cycle_of_external_path_left {p : G.Walk u v} (hp : p.IsPath)
    {a j ℓ : ℕ} (hja : j < a) (ha : a ≤ p.length) (hℓ : 2 ≤ ℓ)
    (q : G.Walk (p.getVert a) (p.getVert j)) (hq : q.IsPath)
    (hql : q.length = ℓ)
    (hinter : ∀ x ∈ q.support, x ∈ p.support →
      x = p.getVert a ∨ x = p.getVert j) :
    ∃ c : G.Walk (p.getVert a) (p.getVert a),
      c.IsCycle ∧ c.length = ℓ + a - j := by
  let s := pathSegment p j a hja.le
  refine ⟨s.reverse.append q.reverse, ?_, ?_⟩
  · apply isCycle_append_reverse_of_intersection
      (pathSegment_isPath hp j a hja.le).reverse hq
    · intro x hxq hxs
      have hxs' : x ∈ s.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hxs
      exact hinter x hxq (pathSegment_support_subset p j a hja.le hxs')
    · omega
  · have hs : s.length = a - j := pathSegment_length p j a hja.le ha
    simp only [Walk.length_append, Walk.length_reverse]
    omega

/-- Exact cycle lengths for a collection of earlier indices. -/
theorem cycles_of_equal_external_paths_left {p : G.Walk u v} (hp : p.IsPath)
    {a ℓ : ℕ} (B : Finset ℕ)
    (hB : ∀ j ∈ B, j < a ∧ a ≤ p.length) (hℓ : 2 ≤ ℓ)
    (hdetour : ∀ j ∈ B, ∃ q : G.Walk (p.getVert a) (p.getVert j),
      q.IsPath ∧ q.length = ℓ ∧
        ∀ x ∈ q.support, x ∈ p.support → x = p.getVert a ∨ x = p.getVert j) :
    ∀ j ∈ B, ∃ c : G.Walk (p.getVert a) (p.getVert a),
      c.IsCycle ∧ c.length = ℓ + a - j := by
  intro j hj
  obtain ⟨q, hq, hql, hinter⟩ := hdetour j hj
  exact exists_cycle_of_external_path_left hp (hB j hj).1 (hB j hj).2 hℓ q hq hql hinter

/-- The left-hand lengths are strictly decreasing as the chosen index grows. -/
theorem card_le_cycleLengths_of_equal_external_paths_left [Fintype V]
    {p : G.Walk u v} (hp : p.IsPath) {a ℓ : ℕ} (B : Finset ℕ)
    (hB : ∀ j ∈ B, j < a ∧ a ≤ p.length) (hℓ : 2 ≤ ℓ)
    (hdetour : ∀ j ∈ B, ∃ q : G.Walk (p.getVert a) (p.getVert j),
      q.IsPath ∧ q.length = ℓ ∧
        ∀ x ∈ q.support, x ∈ p.support → x = p.getVert a ∨ x = p.getVert j) :
    B.card ≤ (cycleLengths G).card := by
  classical
  have hcycles := cycles_of_equal_external_paths_left hp B hB hℓ hdetour
  have hinj : Set.InjOn (fun j => ℓ + a - j) (↑B : Set ℕ) := by
    intro i hi j hj heq
    have hi' := (hB i hi).1
    have hj' := (hB j hj).1
    change ℓ + a - i = ℓ + a - j at heq
    omega
  have hsub : B.image (fun j => ℓ + a - j) ⊆ cycleLengths G := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨c, hc, hcl⟩ := hcycles j hj
    exact mem_cycleLengths_iff.mpr ⟨p.getVert a, c, hc, hcl⟩
  calc
    B.card = (B.image (fun j => ℓ + a - j)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (cycleLengths G).card := Finset.card_le_card hsub

/-- A uniform exact-length formula, using the sum of the two natural-number
differences for the distance between path indices. -/
theorem cycles_of_equal_external_paths_same_side {p : G.Walk u v} (hp : p.IsPath)
    {a ℓ : ℕ} (ha : a ≤ p.length) (B : Finset ℕ)
    (hB : ∀ j ∈ B, j ≤ p.length)
    (hside : (∀ j ∈ B, a < j) ∨ (∀ j ∈ B, j < a)) (hℓ : 2 ≤ ℓ)
    (hdetour : ∀ j ∈ B, ∃ q : G.Walk (p.getVert a) (p.getVert j),
      q.IsPath ∧ q.length = ℓ ∧
        ∀ x ∈ q.support, x ∈ p.support → x = p.getVert a ∨ x = p.getVert j) :
    ∀ j ∈ B, ∃ c : G.Walk (p.getVert a) (p.getVert a),
      c.IsCycle ∧ c.length = ℓ + (j - a) + (a - j) := by
  intro j hj
  rcases hside with hright | hleft
  · obtain ⟨c, hc, hcl⟩ := cycles_of_equal_external_paths hp B
      (fun k hk => ⟨hright k hk, hB k hk⟩) hℓ hdetour j hj
    refine ⟨c, hc, ?_⟩
    have := hright j hj
    omega
  · obtain ⟨c, hc, hcl⟩ := cycles_of_equal_external_paths_left hp B
      (fun k hk => ⟨hleft k hk, ha⟩) hℓ hdetour j hj
    refine ⟨c, hc, ?_⟩
    have := hleft j hj
    omega

/-- Directly accepts the side disjunction returned by the index partition lemma. -/
theorem card_le_cycleLengths_of_equal_external_paths_same_side [Fintype V]
    {p : G.Walk u v} (hp : p.IsPath) {a ℓ : ℕ}
    (ha : a ≤ p.length) (B : Finset ℕ) (hB : ∀ j ∈ B, j ≤ p.length)
    (hside : (∀ j ∈ B, a < j) ∨ (∀ j ∈ B, j < a)) (hℓ : 2 ≤ ℓ)
    (hdetour : ∀ j ∈ B, ∃ q : G.Walk (p.getVert a) (p.getVert j),
      q.IsPath ∧ q.length = ℓ ∧
        ∀ x ∈ q.support, x ∈ p.support → x = p.getVert a ∨ x = p.getVert j) :
    B.card ≤ (cycleLengths G).card := by
  rcases hside with hright | hleft
  · exact card_le_cycleLengths_of_equal_external_paths hp B
      (fun j hj => ⟨hright j hj, hB j hj⟩) hℓ hdetour
  · exact card_le_cycleLengths_of_equal_external_paths_left hp B
      (fun j hj => ⟨hleft j hj, ha⟩) hℓ hdetour

#print axioms exists_cycle_of_external_path
#print axioms card_le_cycleLengths_of_equal_external_paths
#print axioms cycles_of_equal_external_paths_same_side
#print axioms card_le_cycleLengths_of_equal_external_paths_same_side

end JSP619
