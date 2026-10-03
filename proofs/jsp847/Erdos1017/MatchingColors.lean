import Erdos1017.FiniteAveraging
import Erdos1017.PackingEdgeCount

/-! Cyclic matching colors with an exact discarded-edge budget.
Original finite implementation; UNCOMPILED. -/

open scoped BigOperators

namespace Erdos1017

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pair_eq_of_card_two {C : Finset V} (hC : C.card = 2)
    {u : V} (hu : u ∈ C) : ∃ v, v ≠ u ∧ C = {u, v} := by
  classical
  have he : (C.erase u).card = 1 := by
    have := Finset.card_erase_add_one hu
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp he
  have hvC : v ∈ C.erase u := by rw [hv]; simp
  refine ⟨v, (Finset.mem_erase.mp hvC).1, ?_⟩
  calc
    C = insert u (C.erase u) := (Finset.insert_erase hu).symm
    _ = {u, v} := by rw [hv]

theorem matching_of_label_sums {A : Type*} [AddCancelCommMonoid A]
    (X : Finset V) (label : V → A)
    (hinj : Set.InjOn label (↑X : Set V))
    {C D : Finset V} (hC : C.card = 2) (hD : D.card = 2)
    (hCX : C ⊆ X) (hDX : D ⊆ X) {u : V} (huC : u ∈ C) (huD : u ∈ D)
    (hc : (∑ v ∈ C, label v) = ∑ v ∈ D, label v) : C = D := by
  classical
  obtain ⟨v, hvu, rfl⟩ := pair_eq_of_card_two hC huC
  obtain ⟨w, hwu, rfl⟩ := pair_eq_of_card_two hD huD
  have hvw : label v = label w := by
    have : label u + label v = label u + label w := by
      simpa [hvu.symm, hwu.symm] using hc
    exact add_left_cancel this
  have : v = w := hinj (hCX (by simp)) (hDX (by simp)) hvw
  subst w
  rfl

theorem sum_fiber_cards {A : Type*} [Fintype A] [DecidableEq A]
    (E : Finset (Finset V)) (color : Finset V → A) (C : Finset A) :
    (∑ a ∈ C, (E.filter (fun e => color e = a)).card) =
      (E.filter (fun e => color e ∈ C)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hc : color e ∈ C
  · simp [hc, eq_comm]
  · simp [hc, eq_comm]

/-- Selected pair classes are assigned distinct vertices on the other side.
Equality of assigned vertices, together with a common endpoint, forces equal pairs. -/
structure ColoredPairSelection (X Y : Finset V) (E : Finset (Finset V)) where
  retained : Finset (Finset V)
  subset : retained ⊆ E
  apex : Finset V → V
  apex_mem : ∀ C ∈ retained, apex C ∈ Y
  matching : ∀ C ∈ retained, ∀ D ∈ retained, apex C = apex D →
    ∀ u ∈ C, u ∈ D → C = D
  discard_budget : X.card * (E \ retained).card ≤
    (X.card - min X.card Y.card) * E.card

theorem exists_coloredPairSelection (X Y : Finset V)
    (hx : 0 < X.card) (hy : 0 < Y.card) (E : Finset (Finset V))
    (hpairs : ∀ C ∈ E, C.card = 2 ∧ C ⊆ X) :
    Nonempty (ColoredPairSelection X Y E) := by
  classical
  letI : NeZero X.card := ⟨ne_of_gt hx⟩
  let labelEquiv : X ≃ ZMod X.card := Fintype.equivOfCardEq (by simp)
  let label : V → ZMod X.card := fun v =>
    if hv : v ∈ X then labelEquiv ⟨v, hv⟩ else 0
  have hinj : Set.InjOn label (↑X : Set V) := by
    intro u hu v hv huv
    have huX : u ∈ X := hu
    have hvX : v ∈ X := hv
    have h : labelEquiv ⟨u, hu⟩ = labelEquiv ⟨v, hv⟩ := by
      simpa only [label, dif_pos huX, dif_pos hvX] using huv
    exact congrArg Subtype.val (labelEquiv.injective h)
  let color : Finset V → ZMod X.card := fun C => ∑ v ∈ C, label v
  let w : ZMod X.card → ℕ := fun a => (E.filter (fun e => color e = a)).card
  obtain ⟨C, hC, hbudget⟩ := exists_color_subset_discard_budget w
    (min X.card Y.card) (by simpa using min_le_left X.card Y.card)
  let retained := E.filter (fun e => color e ∈ C)
  have htotal : (∑ a : ZMod X.card, w a) = E.card := by
    simpa [w] using sum_fiber_cards E color Finset.univ
  have hdiscard : (∑ a ∈ Finset.univ \ C, w a) = (E \ retained).card := by
    rw [show (∑ a ∈ Finset.univ \ C, w a) =
        (E.filter (fun e => color e ∈ Finset.univ \ C)).card from
      sum_fiber_cards E color (Finset.univ \ C)]
    congr 1
    ext e
    simp [retained]
    aesop
  have hCY : Fintype.card C ≤ Fintype.card Y := by
    simpa [hC] using min_le_right X.card Y.card
  let ec := Fintype.equivFin C
  let ey := Fintype.equivFin Y
  let j : C → Y := fun c => ey.symm
    ⟨(ec c).val, lt_of_lt_of_le (ec c).isLt hCY⟩
  have hj : Function.Injective j := by
    intro c d h
    apply ec.injective
    apply Fin.ext
    simpa only [j, Equiv.apply_symm_apply] using
      congrArg (fun y : Y => (ey y).val) h
  obtain ⟨y₀, hy₀⟩ := Finset.card_pos.mp hy
  let apex : Finset V → V := fun e =>
    if hc : color e ∈ C then (j ⟨color e, hc⟩).val else y₀
  refine ⟨⟨retained, Finset.filter_subset _ _, apex, ?_, ?_, ?_⟩⟩
  · intro e he
    have hc := (Finset.mem_filter.mp he).2
    simpa [apex, hc] using (j ⟨color e, hc⟩).property
  · intro e he f hf hef u hue huf
    have heC := (Finset.mem_filter.mp he).2
    have hfC := (Finset.mem_filter.mp hf).2
    have hjef : j ⟨color e, heC⟩ = j ⟨color f, hfC⟩ := by
      apply Subtype.ext
      simpa [apex, heC, hfC] using hef
    have hc : color e = color f := congrArg Subtype.val (hj hjef)
    obtain ⟨hecard, heX⟩ := hpairs e (Finset.mem_filter.mp he).1
    obtain ⟨hfcard, hfX⟩ := hpairs f (Finset.mem_filter.mp hf).1
    exact matching_of_label_sums X label hinj hecard hfcard heX hfX hue huf hc
  · simpa only [ZMod.card, htotal, hdiscard] using hbudget

end Erdos1017
