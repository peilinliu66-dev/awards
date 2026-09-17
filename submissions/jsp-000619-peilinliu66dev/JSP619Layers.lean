import JSP619CycleCore

/-!
# Rooted shortest-path layers and equal-length return paths

Parents decrease the layer by exactly one. The equal-return-path assertion is
proved from iterated parents; it is not assumed as a tree black box.
Lean 4.33.1 formalization.
-/
noncomputable section
open Finset Function
namespace JSP619
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} {G : SimpleGraph V}

structure LayerTree (G : SimpleGraph V) where
  root : V
  level : V → ℕ
  parent : V → V
  level_root : level root = 0
  zero_root : ∀ v, level v = 0 → v = root
  parent_adj : ∀ v, 0 < level v → G.Adj v (parent v)
  parent_level : ∀ v, 0 < level v → level (parent v) + 1 = level v
  edge_level : ∀ v w, G.Adj v w → level v ≤ level w + 1

/-- A coherent BFS parent system is obtained by choosing one predecessor at each vertex. -/
def layerTreeOfConnected (hG : G.Connected) (r : V) : LayerTree G := by
  classical
  let lev : V → ℕ := fun v => G.dist v r
  have hprev (v : V) (hv : 0 < lev v) :
      ∃ w, G.Adj v w ∧ lev w + 1 = lev v := by
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v r
    cases p with
    | nil => simp [lev] at hv
    | @cons v w r hadj q =>
      have h1 := SimpleGraph.dist_le q
      have h2 := hG.dist_triangle (u := v) (v := w) (w := r)
      have hdist : G.dist v w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
      rw [hdist] at h2
      simp only [SimpleGraph.Walk.length_cons] at hp
      exact ⟨w, hadj, by dsimp [lev]; omega⟩
  let par : V → V := fun v => if h : 0 < lev v then Classical.choose (hprev v h) else v
  refine
    { root := r
      level := lev
      parent := par
      level_root := by simp [lev]
      zero_root := ?_
      parent_adj := ?_
      parent_level := ?_
      edge_level := ?_ }
  · intro v hv
    exact hG.dist_eq_zero_iff.mp hv
  · intro v hv
    dsimp [par]
    rw [dif_pos hv]
    exact (Classical.choose_spec (hprev v hv)).1
  · intro v hv
    dsimp [par]
    rw [dif_pos hv]
    exact (Classical.choose_spec (hprev v hv)).2
  · intro v w hvw
    have h := hG.dist_triangle (u := v) (v := w) (w := r)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvw] at h
    dsimp [lev]
    omega

namespace LayerTree
variable (T : LayerTree G)

def climb (T : LayerTree G) : ℕ → V → V
  | 0, v => v
  | n + 1, v => T.climb n (T.parent v)

@[simp] lemma climb_zero (v : V) : T.climb 0 v = v := rfl
@[simp] lemma climb_succ (n : ℕ) (v : V) :
    T.climb (n + 1) v = T.climb n (T.parent v) := rfl

lemma climb_add (a b : ℕ) (v : V) :
    T.climb (a + b) v = T.climb a (T.climb b v) := by
  induction b generalizing v with
  | zero => simp
  | succ b ih =>
    simpa only [Nat.add_succ, climb_succ] using ih (T.parent v)

lemma level_climb (n : ℕ) (v : V) (hn : n ≤ T.level v) :
    T.level (T.climb n v) = T.level v - n := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    have hp := T.parent_level v (by omega)
    rw [climb_succ, ih (T.parent v) (by omega)]
    omega

/-- The actual parent walk, stopped before the root if necessary. -/
def climbWalk (T : LayerTree G) : (n : ℕ) → (v : V) → n ≤ T.level v → G.Walk v (T.climb n v)
  | 0, v, _ => .nil
  | n + 1, v, hn =>
      .cons (T.parent_adj v (by omega))
        (T.climbWalk n (T.parent v) (by
          have h := T.parent_level v (by omega)
          omega))

@[simp] lemma climbWalk_length (n : ℕ) (v : V) (hn : n ≤ T.level v) :
    (T.climbWalk n v hn).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [climbWalk, ih]

lemma mem_climbWalk (n : ℕ) (v : V) (hn : n ≤ T.level v) {x : V}
    (hx : x ∈ (T.climbWalk n v hn).support) :
    ∃ j ≤ n, x = T.climb j v := by
  induction n generalizing v with
  | zero =>
    have h : x = v := by simpa [climbWalk] using hx
    exact ⟨0, le_rfl, h⟩
  | succ n ih =>
    change x ∈ v :: (T.climbWalk n (T.parent v) _).support at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨0, Nat.zero_le _, rfl⟩
    · obtain ⟨j, hj, he⟩ := ih (T.parent v) (by
        have h := T.parent_level v (by omega)
        omega) hx
      exact ⟨j + 1, by omega, he⟩

lemma climbWalk_level_bounds (n : ℕ) (v : V) (hn : n ≤ T.level v) {x : V}
    (hx : x ∈ (T.climbWalk n v hn).support) :
    T.level v - n ≤ T.level x ∧ T.level x ≤ T.level v := by
  obtain ⟨j, hj, rfl⟩ := T.mem_climbWalk n v hn hx
  rw [T.level_climb j v (by omega)]
  omega

lemma climbWalk_level_lt (n : ℕ) (v : V) (hn : n ≤ T.level v) {x : V}
    (hx : x ∈ (T.climbWalk n v hn).support) (hne : x ≠ v) :
    T.level x < T.level v := by
  obtain ⟨j, hj, he⟩ := T.mem_climbWalk n v hn hx
  have hj0 : 0 < j := by
    by_contra! hz
    have : j = 0 := by omega
    simp [this] at he
    exact hne he
  rw [he, T.level_climb j v (by omega)]
  omega

lemma climbWalk_isPath (n : ℕ) (v : V) (hn : n ≤ T.level v) :
    (T.climbWalk n v hn).IsPath := by
  induction n generalizing v with
  | zero => exact SimpleGraph.Walk.IsPath.nil
  | succ n ih =>
    have hpar := T.parent_level v (by omega)
    have hnb : n ≤ T.level (T.parent v) := by omega
    change (SimpleGraph.Walk.cons (T.parent_adj v (by omega))
      (T.climbWalk n (T.parent v) hnb)).IsPath
    apply (ih (T.parent v) hnb).cons
    intro hv
    have h := (T.climbWalk_level_bounds n (T.parent v) _ hv).2
    omega

def ancestor (v : V) (j : ℕ) : V := T.climb (T.level v - j) v

lemma ancestor_level (v : V) (j : ℕ) (hj : j ≤ T.level v) :
    T.level (T.ancestor v j) = j := by
  rw [ancestor, T.level_climb _ v (Nat.sub_le _ _)]
  omega

@[simp] lemma ancestor_self (v : V) : T.ancestor v (T.level v) = v := by
  simp [ancestor]

@[simp] lemma ancestor_zero (v : V) : T.ancestor v 0 = T.root :=
  T.zero_root _ (T.ancestor_level v 0 (Nat.zero_le _))

lemma ancestor_climb (v : V) (t j : ℕ) (ht : t ≤ T.level v)
    (hj : j ≤ T.level v - t) :
    T.ancestor (T.climb t v) j = T.ancestor v j := by
  unfold ancestor
  rw [T.level_climb t v ht, ← T.climb_add]
  congr 1
  omega

lemma ancestor_of_mem_climbWalk (n : ℕ) (v : V) (hn : n ≤ T.level v)
    {x : V} (hx : x ∈ (T.climbWalk n v hn).support) (j : ℕ)
    (hj : j ≤ T.level x) : T.ancestor x j = T.ancestor v j := by
  obtain ⟨t, ht, rfl⟩ := T.mem_climbWalk n v hn hx
  apply T.ancestor_climb v t j (by omega)
  simpa only [T.level_climb t v (by omega)] using hj

/-- A walk from v to its ancestor at level j. -/
def downTo (v : V) (j : ℕ) : G.Walk v (T.ancestor v j) :=
  T.climbWalk (T.level v - j) v (Nat.sub_le _ _)

@[simp] lemma downTo_length (v : V) (j : ℕ) :
    (T.downTo v j).length = T.level v - j :=
  T.climbWalk_length _ _ _

lemma downTo_isPath (v : V) (j : ℕ) : (T.downTo v j).IsPath :=
  T.climbWalk_isPath _ _ _

lemma downTo_internal_level {v x : V} {j : ℕ}
    (hx : x ∈ (T.downTo v j).support) (hne : x ≠ v) : T.level x < T.level v :=
  T.climbWalk_level_lt _ _ _ hx hne

/-- Different branches above level r meet only at their common ancestor at r. -/
lemma downTo_intersection {a b : V} {i r : ℕ}
    (ha : T.level a = i) (hb : T.level b = i) (hr : r < i)
    (hcommon : T.ancestor a r = T.ancestor b r)
    (hbranch : T.ancestor a (r + 1) ≠ T.ancestor b (r + 1))
    {x : V} (hxa : x ∈ (T.downTo a r).support)
    (hxb : x ∈ (T.downTo b r).support) : x = T.ancestor a r := by
  have hxlo : r ≤ T.level x := by
    have h := (T.climbWalk_level_bounds (T.level a - r) a (Nat.sub_le _ _) hxa).1
    rw [ha] at h
    omega
  by_cases he : T.level x = r
  · have h := T.ancestor_of_mem_climbWalk _ a _ hxa r hxlo
    simpa [← he] using h
  · have hj : r + 1 ≤ T.level x := by omega
    have h1 := T.ancestor_of_mem_climbWalk _ a _ hxa (r + 1) hj
    have h2 := T.ancestor_of_mem_climbWalk _ b _ hxb (r + 1) hj
    exact False.elim (hbranch (h1.symm.trans h2))

/-- The real return path has the fixed length 2*(i-r), with all internal vertices below i. -/
theorem equal_length_return {a b : V} {i r : ℕ}
    (ha : T.level a = i) (hb : T.level b = i) (hr : r < i)
    (hcommon : T.ancestor a r = T.ancestor b r)
    (hbranch : T.ancestor a (r + 1) ≠ T.ancestor b (r + 1)) :
    ∃ q : G.Walk b a, q.IsPath ∧ q.length = 2 * (i - r) ∧
      ∀ x ∈ q.support, x ≠ a → x ≠ b → T.level x < i := by
  let pa := T.downTo a r
  let pb := (T.downTo b r).copy rfl hcommon.symm
  have hpa : pa.IsPath := T.downTo_isPath a r
  have hpb : pb.IsPath := by simpa [pb] using T.downTo_isPath b r
  refine ⟨pb.append pa.reverse, ?_, ?_, ?_⟩
  · apply append_isPath_of_inter hpb hpa.reverse
    intro x hxb hxa
    apply T.downTo_intersection ha hb hr hcommon hbranch
    · simpa [pa] using hxa
    · simpa [pb] using hxb
  · simp [pa, pb, ha, hb, two_mul]
  · intro x hx hxa hxb
    have hh : x ∈ pb.support ∨ x ∈ pa.reverse.support := by
      simpa only [SimpleGraph.Walk.mem_support_append_iff] using hx
    rcases hh with hh | hh
    · have hh' : x ∈ (T.downTo b r).support := by simpa [pb] using hh
      simpa [hb] using T.downTo_internal_level hh' hxb
    · have hh' : x ∈ (T.downTo a r).support := by simpa [pa] using hh
      simpa [ha] using T.downTo_internal_level hh' hxa

/-- A finite same-level set splits into two nonempty branches; keeping the larger
side loses at most one half. This is proved by the first nonconstant ancestor level. -/
theorem branch_partition {J : Type v} [DecidableEq J]
    (W : Finset J) (f : J → V) (i : ℕ) (hW : 2 ≤ W.card)
    (hlevel : ∀ x ∈ W, T.level (f x) = i)
    (hinj : Set.InjOn f (↑W : Set J)) :
    ∃ (a : J) (B : Finset J) (r : ℕ), a ∈ W ∧ B ⊆ W ∧ a ∉ B ∧
      r < i ∧ W.card ≤ 2 * B.card ∧
      ∀ b ∈ B, T.ancestor (f a) r = T.ancestor (f b) r ∧
        T.ancestor (f a) (r + 1) ≠ T.ancestor (f b) (r + 1) := by
  classical
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < W.card)
  have hyex : ∃ y ∈ W, f x ≠ f y := by
    by_contra! hall
    have hsub : W ⊆ {x} := by
      intro y hy
      apply Finset.mem_singleton.mpr
      exact hinj hy hx (hall y hy).symm
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  obtain ⟨y, hy, hxy⟩ := hyex
  let P : ℕ → Prop := fun j => ∃ a ∈ W, ∃ b ∈ W,
    T.ancestor (f a) j ≠ T.ancestor (f b) j
  have hiP : P i := by
    refine ⟨x, hx, y, hy, ?_⟩
    have hxself : T.ancestor (f x) i = f x := by
      rw [← hlevel x hx, T.ancestor_self]
    have hyself : T.ancestor (f y) i = f y := by
      rw [← hlevel y hy, T.ancestor_self]
    simpa only [hxself, hyself] using hxy
  have hex : ∃ j, P j := ⟨i, hiP⟩
  let j := Nat.find hex
  have hjP : P j := Nat.find_spec hex
  have hji : j ≤ i := Nat.find_min' hex hiP
  have hj0 : 0 < j := by
    by_contra! hz
    have : j = 0 := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := hjP
    simp [this] at hab
  let r := j - 1
  have hrj : r + 1 = j := by dsimp [r]; omega
  have hr : r < i := by dsimp [r]; omega
  have hcommon : ∀ a ∈ W, ∀ b ∈ W,
      T.ancestor (f a) r = T.ancestor (f b) r := by
    intro a ha b hb
    by_contra hab
    have hnot := Nat.find_min hex (show r < Nat.find hex by dsimp [r, j] at *; omega)
    exact hnot ⟨a, ha, b, hb, hab⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hjP
  let A := W.filter (fun z => T.ancestor (f z) j = T.ancestor (f a) j)
  let B := W \ A
  have haA : a ∈ A := by simp [A, ha]
  have hbB : b ∈ B := by
    simp only [B, Finset.mem_sdiff]
    exact ⟨hb, by simpa [A, hb] using hab.symm⟩
  have hAsub : A ⊆ W := Finset.filter_subset _ _
  have hBsub : B ⊆ W := Finset.sdiff_subset
  have hsum : A.card + B.card = W.card := by
    simpa [B, Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hAsub
  by_cases hAB : A.card ≤ B.card
  · refine ⟨a, B, r, ha, hBsub, ?_, hr, by omega, ?_⟩
    · intro hab'
      exact (Finset.mem_sdiff.mp hab').2 haA
    · intro z hz
      refine ⟨hcommon a ha z (hBsub hz), ?_⟩
      rw [hrj]
      intro he
      apply (Finset.mem_sdiff.mp hz).2
      exact Finset.mem_filter.mpr ⟨hBsub hz, he.symm⟩
  · refine ⟨b, A, r, hb, hAsub, (Finset.mem_sdiff.mp hbB).2, hr, by omega, ?_⟩
    intro z hz
    refine ⟨hcommon b hb z (hAsub hz), ?_⟩
    rw [hrj]
    have he := (Finset.mem_filter.mp hz).2
    intro hbad
    exact hab (he.symm.trans hbad.symm)

end LayerTree
#print axioms layerTreeOfConnected
#print axioms LayerTree.equal_length_return
#print axioms LayerTree.branch_partition
end JSP619
end
