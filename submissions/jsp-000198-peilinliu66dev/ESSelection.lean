import ESConvex

noncomputable section
namespace Horton

/-- Exact finite Ramsey interface. The finite combinatorial theorem is supplied
separately; no geometric hypothesis is built into this interface. -/
def OrderedTripleRamsey25 (N : ℕ) : Prop :=
  ∀ C : Fin N → Fin N → Fin N → Bool,
    ∃ f : Fin 25 → Fin N, StrictMono f ∧
      ∃ c : Bool, ∀ i j k, i < j → j < k → C (f i) (f j) (f k) = c

/-- Selection-to-geometry bridge. This is deliberately named with its Ramsey
hypothesis: the unconditional ES(25) theorem will instantiate that hypothesis. -/
theorem exists_convex25_of_orderedTripleRamsey (N : ℕ)
    (hRamsey : OrderedTripleRamsey25 N)
    (S : Finset Point) (hN : N ≤ S.card) (hgp : GeneralPosition S) :
    ∃ T : Finset Point, T ⊆ S ∧ T.card = 25 ∧
      ConvexIndependent ℝ (fun x : (T : Set Point) => (x : Point)) := by
  classical
  let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (Fintype.card_coe S)
  let p : Fin N → Point := fun i => (e.symm (Fin.castLE hN i)).val
  have hp_mem (i : Fin N) : p i ∈ S := (e.symm (Fin.castLE hN i)).property
  have hp_inj : Function.Injective p := by
    intro i j h
    have h' : e.symm (Fin.castLE hN i) = e.symm (Fin.castLE hN j) := Subtype.ext h
    have h'' := e.symm.injective h'
    exact Fin.ext (congrArg (fun x : Fin S.card => x.val) h'')
  let C : Fin N → Fin N → Fin N → Bool :=
    fun i j k => decide (0 < orient (p i) (p j) (p k))
  obtain ⟨f, hf, c, hc⟩ := hRamsey C
  let q : Fin 25 → Point := p ∘ f
  have hq_inj : Function.Injective q := hp_inj.comp hf.injective
  have hq_nonzero (i j k : Fin 25) (hij : i < j) (hjk : j < k) :
      orient (q i) (q j) (q k) ≠ 0 := by
    exact hgp (q i) (hp_mem _) (q j) (hp_mem _) (q k) (hp_mem _)
      (hq_inj.ne (ne_of_lt hij)) (hq_inj.ne (ne_of_lt (hij.trans hjk)))
      (hq_inj.ne (ne_of_lt hjk))
  have hq_convex : ConvexIndependent ℝ q := by
    cases c
    · apply convexIndependent_of_esNegative
      intro i j k hij hjk
      have hcolor := hc i j k hij hjk
      change decide (0 < orient (q i) (q j) (q k)) = false at hcolor
      have hn : ¬ 0 < orient (q i) (q j) (q k) := of_decide_eq_false hcolor
      exact lt_of_le_of_ne (le_of_not_gt hn) (hq_nonzero i j k hij hjk)
    · apply convexIndependent_of_esPositive
      intro i j k hij hjk
      have hcolor := hc i j k hij hjk
      change decide (0 < orient (q i) (q j) (q k)) = true at hcolor
      exact of_decide_eq_true hcolor
  let T : Finset Point := Finset.univ.image q
  refine ⟨T, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hp_mem (f i)
  · change (Finset.univ.image q).card = 25
    rw [Finset.card_image_of_injective _ hq_inj]
    simp
  · have heq : (T : Set Point) = Set.range q := by
      ext x
      simp [T]
    rw [heq]
    exact hq_convex.range

end Horton

#print axioms Horton.exists_convex25_of_orderedTripleRamsey
