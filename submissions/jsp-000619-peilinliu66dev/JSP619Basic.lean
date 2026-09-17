import JSP619CycleSplice

/-!
# JSP-000619 / Erdos 752: finite counting and genuine cycle witnesses

Lean 4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Mathematical attribution: Sudakov--Verstraete,
"Cycle lengths in sparse graphs", Theorem 2.2. No theta-graph lemma is used.
-/

noncomputable section
open Finset Function
namespace JSP619
attribute [local instance] Classical.propDecidable
universe u v

/-- Strict girth hypothesis, including the acyclic case without a junk value. -/
def HighGirth {V : Type u} (G : SimpleGraph V) (s : ℕ) : Prop :=
  ∀ (v : V) (p : G.Walk v v), p.IsCycle → 2 * s < p.length

lemma highGirth_of_girth {V : Type u} {G : SimpleGraph V} {s : ℕ}
    (h : 2 * s < G.girth) : HighGirth G s := by
  intro v p hp
  exact h.trans_le (SimpleGraph.girth_le_length hp)

lemma highGirth_map {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W} (f : H →g G)
    (hf : Injective f) {s : ℕ} (hG : HighGirth G s) : HighGirth H s := by
  intro v p hp
  have h := hG (f v) (p.map f) (hp.map hf)
  simpa using h

@[simp] lemma mem_cycleLengths {V : Type u} [Fintype V]
    {G : SimpleGraph V} {n : ℕ} :
    n ∈ cycleLengths G ↔ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n :=
  mem_cycleLengths_iff

lemma cycleLengths_map_subset {V : Type u} {W : Type v}
    [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H →g G) (hf : Injective f) : cycleLengths H ⊆ cycleLengths G := by
  intro n hn
  obtain ⟨v, p, hp, he⟩ := mem_cycleLengths.mp hn
  exact mem_cycleLengths.mpr ⟨f v, p.map f, hp.map hf, by simpa using he⟩

lemma card_cycleLengths_map_le {V : Type u} {W : Type v}
    [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H →g G) (hf : Injective f) :
    (cycleLengths H).card ≤ (cycleLengths G).card :=
  Finset.card_le_card (cycleLengths_map_subset f hf)

/-- Finite optimization of a bounded integer score. The state space need not be finite. -/
lemma exists_score_max {A : Type u} (P : A → Prop) (f : A → ℕ) (N : ℕ)
    (hne : ∃ a, P a) (hb : ∀ a, P a → f a ≤ N) :
    ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by
  classical
  let T : Finset ℕ := (Finset.range (N + 1)).filter (fun n => ∃ a, P a ∧ f a = n)
  have hT : T.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨f a, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hb a ha)), a, ha, rfl⟩⟩
  have hm := Finset.max'_mem T hT
  obtain ⟨a, ha, he⟩ := (Finset.mem_filter.mp hm).2
  refine ⟨a, ha, ?_⟩
  intro b hb'
  rw [he]
  exact Finset.le_max' T (f b) (Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hb b hb')), b, hb', rfl⟩)

section FiniteDensity
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- All neighbors of v that lie in A. -/
def neighborsIn (G : SimpleGraph V) (A : Finset V) (v : V) : Finset V := by
  classical
  exact A.filter (G.Adj v)

def degIn (G : SimpleGraph V) (A : Finset V) (v : V) : ℕ :=
  (neighborsIn G A v).card

/-- Twice the number of edges in the induced graph on A. -/
def mass (G : SimpleGraph V) (A : Finset V) : ℕ :=
  ∑ v ∈ A, degIn G A v

@[simp] lemma mem_neighborsIn {G : SimpleGraph V} {A : Finset V} {v w : V} :
    w ∈ neighborsIn G A v ↔ w ∈ A ∧ G.Adj v w := by
  classical
  simp [neighborsIn]

lemma degIn_eq_sum (G : SimpleGraph V) (A : Finset V) (v : V) :
    degIn G A v = ∑ w ∈ A, if G.Adj v w then 1 else 0 := by
  classical
  simp [degIn, neighborsIn]

@[simp] lemma degIn_empty (G : SimpleGraph V) (v : V) : degIn G ∅ v = 0 := by
  classical
  simp [degIn, neighborsIn]

@[simp] lemma mass_empty (G : SimpleGraph V) : mass G ∅ = 0 := by
  simp [mass]

@[simp] lemma mass_singleton (G : SimpleGraph V) (v : V) : mass G {v} = 0 := by
  classical
  simp [mass, degIn, neighborsIn]

lemma degIn_le_card (G : SimpleGraph V) (A : Finset V) (v : V) :
    degIn G A v ≤ A.card := Finset.card_le_card (Finset.filter_subset _ _)

lemma degIn_mono (G : SimpleGraph V) {A B : Finset V} (h : A ⊆ B) (v : V) :
    degIn G A v ≤ degIn G B v := by
  classical
  apply Finset.card_le_card
  intro w hw
  exact mem_neighborsIn.mpr ⟨h (mem_neighborsIn.mp hw).1, (mem_neighborsIn.mp hw).2⟩

@[simp] lemma degIn_univ (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degIn G Finset.univ v = G.degree v := by
  classical
  have he : neighborsIn G Finset.univ v = G.neighborFinset v := by
    ext w
    simp
  rw [degIn, he]
  exact G.card_neighborFinset_eq_degree v

lemma degIn_erase_add (G : SimpleGraph V) (A : Finset V) (v x : V) (hv : v ∈ A) :
    degIn G (A.erase v) x + (if G.Adj x v then 1 else 0) = degIn G A x := by
  classical
  rw [degIn_eq_sum, degIn_eq_sum]
  exact Finset.sum_erase_add _ _ hv

@[simp] lemma degIn_erase_self (G : SimpleGraph V) (A : Finset V) (v : V) :
    degIn G (A.erase v) v = degIn G A v := by
  classical
  apply congrArg Finset.card
  ext x
  simp only [mem_neighborsIn, Finset.mem_erase]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · rintro ⟨hx, hadj⟩
    exact ⟨⟨hadj.ne.symm, hx⟩, hadj⟩

lemma mass_erase_add (G : SimpleGraph V) (A : Finset V) (v : V) (hv : v ∈ A) :
    mass G (A.erase v) + 2 * degIn G A v = mass G A := by
  classical
  have h1 : ∑ x ∈ A.erase v, degIn G A x =
      mass G (A.erase v) + degIn G A v := by
    calc
      (∑ x ∈ A.erase v, degIn G A x) =
          ∑ x ∈ A.erase v,
            (degIn G (A.erase v) x + if G.Adj x v then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        exact (degIn_erase_add G A v x hv).symm
      _ = mass G (A.erase v) + degIn G (A.erase v) v := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [degIn_eq_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [G.adj_comm]
      _ = mass G (A.erase v) + degIn G A v := by rw [degIn_erase_self]
  have h2 := Finset.sum_erase_add A (degIn G A) hv
  change (∑ x ∈ A.erase v, degIn G A x) + degIn G A v = mass G A at h2
  omega

/-- A nonempty graph of average degree at least 2*r contains a nonempty r-core.
The proof explicitly deletes low-degree vertices through a minimum-cardinality witness. -/
theorem exists_core (G : SimpleGraph V) (A : Finset V) (r : ℕ)
    (hr : 0 < r) (hA : A.Nonempty) (hden : 2 * r * A.card ≤ mass G A) :
    ∃ B : Finset V, B ⊆ A ∧ B.Nonempty ∧ ∀ v ∈ B, r ≤ degIn G B v := by
  classical
  let P : ℕ → Prop := fun n => ∃ B : Finset V,
    B ⊆ A ∧ B.Nonempty ∧ 2 * r * B.card ≤ mass G B ∧ B.card = n
  have hex : ∃ n, P n := ⟨A.card, A, Finset.Subset.refl A, hA, hden, rfl⟩
  obtain ⟨B, hBA, hB, hdB, hcard⟩ := Nat.find_spec hex
  refine ⟨B, hBA, hB, ?_⟩
  intro v hv
  by_contra! hlow
  have hE : (B.erase v).Nonempty := by
    by_contra hempty
    have heq : B = {v} := by
      ext x
      constructor
      · intro hx
        by_cases h : x = v
        · simpa [h]
        · have : x ∈ B.erase v := Finset.mem_erase.mpr ⟨h, hx⟩
          exact False.elim (hempty ⟨x, this⟩)
      · intro hx
        rcases Finset.mem_singleton.mp hx with rfl
        exact hv
    rw [heq] at hdB
    simp only [Finset.card_singleton, mass_singleton, mul_one] at hdB
    omega
  have hecard := Finset.card_erase_of_mem hv
  have hemass := mass_erase_add G B v hv
  have hecard_add : (B.erase v).card + 1 = B.card := by
    have hp := Finset.card_pos.mpr hB
    omega
  have heDensity : 2 * r * (B.erase v).card ≤ mass G (B.erase v) := by
    rw [← hecard_add] at hdB
    nlinarith [hlow]
  have heP : P (B.erase v).card :=
    ⟨B.erase v, (Finset.erase_subset v B).trans hBA, hE, heDensity, rfl⟩
  have hmin := Nat.find_min' hex heP
  have hpos := Finset.card_pos.mpr hB
  omega

/-- External, rather than inclusive, neighborhood. -/
def boundary (G : SimpleGraph V) (A : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ∉ A ∧ ∃ x ∈ A, G.Adj x v)

@[simp] lemma mem_boundary {G : SimpleGraph V} {A : Finset V} {v : V} :
    v ∈ boundary G A ↔ v ∉ A ∧ ∃ x ∈ A, G.Adj x v := by
  classical
  simp [boundary]

lemma disjoint_boundary (G : SimpleGraph V) (A : Finset V) :
    Disjoint A (boundary G A) := by
  classical
  exact Finset.disjoint_left.mpr (fun x hx hb => (mem_boundary.mp hb).1 hx)

lemma neighbor_mem_closure {G : SimpleGraph V} {A : Finset V} {x y : V}
    (hx : x ∈ A) (hxy : G.Adj x y) : y ∈ A ∪ boundary G A := by
  classical
  by_cases hy : y ∈ A
  · exact Finset.mem_union_left _ hy
  · exact Finset.mem_union_right _ (mem_boundary.mpr ⟨hy, x, hx, hxy⟩)

lemma degIn_closure (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {x : V} (hx : x ∈ A) :
    degIn G (A ∪ boundary G A) x = G.degree x := by
  classical
  rw [← degIn_univ G x]
  apply congrArg Finset.card
  ext y
  simp only [mem_neighborsIn, Finset.mem_univ, true_and]
  exact ⟨And.right, fun h => ⟨neighbor_mem_closure hx h, h⟩⟩

/-- Induced graph with its vertex set carried by an actual finite subtype. -/
def induced (G : SimpleGraph V) (A : Finset V) : SimpleGraph ↥A where
  Adj x y := G.Adj x.1 y.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.ne rfl⟩

def inducedHom (G : SimpleGraph V) (A : Finset V) : induced G A →g G where
  toFun := Subtype.val
  map_rel' := fun h => h

lemma induced_degree (G : SimpleGraph V) (A : Finset V)
    [DecidableRel G.Adj] (v : ↥A) :
    (induced G A).degree v = degIn G A v.1 := by
  classical
  let e : (induced G A).neighborSet v ≃ ↥(neighborsIn G A v.1) :=
    { toFun := fun w => ⟨w.1.1, mem_neighborsIn.mpr ⟨w.1.2, w.2⟩⟩
      invFun := fun w => ⟨⟨w.1, (mem_neighborsIn.mp w.2).1⟩,
        (mem_neighborsIn.mp w.2).2⟩
      left_inv := by intro w; rfl
      right_inv := by intro w; rfl }
  rw [← (induced G A).card_neighborSet_eq_degree v]
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

end FiniteDensity

#print axioms exists_core
#print axioms induced_degree

end JSP619
end
