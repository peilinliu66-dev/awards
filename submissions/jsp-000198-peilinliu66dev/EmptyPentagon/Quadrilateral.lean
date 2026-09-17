/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Quadrilateral.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Forces
import EmptyPentagon.Certificate
import EmptyPentagon.Identities
import EmptyPentagon.Enumeration

noncomputable section
namespace Horton

/-- Swapping the first two arguments of `orient` negates it. -/
theorem orient_swap_left (a b c : Point) : orient b a c = -orient a b c := by
  unfold orient
  ring

/-- Swapping the last two arguments of `orient` negates it. -/
theorem orient_swap_right (a b c : Point) : orient a c b = -orient a b c := by
  unfold orient
  ring

/-- The orientation vanishes when the third point equals the first. -/
theorem orient_left_self (a b : Point) : orient a b a = 0 := by
  unfold orient
  ring

/-- The orientation vanishes when the third point equals the second. -/
theorem orient_right_self (a b : Point) : orient a b b = 0 := by
  unfold orient
  ring

/-- The Boolean orientation sign vector of an indexed five-point configuration. -/
def orientSign (p : Fin 5 → Point) (i j k : Fin 5) : Bool :=
  decide (0 < orient (p i) (p j) (p k))

/-- Indexed general position: pairwise distinct indices give a nonzero orientation. -/
def IndexedGP (p : Fin 5 → Point) : Prop :=
  ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k → orient (p i) (p j) (p k) ≠ 0

/-- A `true` sign is a strictly positive orientation. -/
theorem orientSign_true_iff (p : Fin 5 → Point) (i j k : Fin 5) :
    orientSign p i j k = true ↔ 0 < orient (p i) (p j) (p k) :=
  decide_eq_true_iff

/-- A `false` sign is a nonpositive orientation. -/
theorem orientSign_false_iff (p : Fin 5 → Point) (i j k : Fin 5) :
    orientSign p i j k = false ↔ orient (p i) (p j) (p k) ≤ 0 := by
  simp [orientSign]

/-- In general position a `false` sign is a strictly negative orientation. -/
theorem orientSign_false_iff_neg {p : Fin 5 → Point} (hgp : IndexedGP p) (i j k : Fin 5)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    orientSign p i j k = false ↔ orient (p i) (p j) (p k) < 0 := by
  rw [orientSign_false_iff]
  exact ⟨fun h => lt_of_le_of_ne h (hgp i j k hij hik hjk), le_of_lt⟩

/-- Equality of the signs of two nonzero reals is the sign of their product. -/
theorem beq_decide_pos_iff {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    ((decide (0 < x) == decide (0 < y)) = true ↔ 0 < x * y) ∧
      ((decide (0 < x) == decide (0 < y)) = false ↔ x * y < 0) := by
  rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy
  · have h := mul_pos_of_neg_of_neg hx hy
    simp [hx.not_gt, hy.not_gt, h, h.not_gt]
  · have h := mul_neg_of_neg_of_pos hx hy
    simp [hx.not_gt, hy, h, h.not_gt]
  · have h := mul_neg_of_pos_of_neg hx hy
    simp [hx, hy.not_gt, h, h.not_gt]
  · have h := mul_pos hx hy
    simp [hx, hy, h, h.not_gt]

/-- Inequality of the signs of two nonzero reals is the negativity of their product. -/
theorem bne_decide_pos_iff {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    ((decide (0 < x) != decide (0 < y)) = true ↔ x * y < 0) ∧
      ((decide (0 < x) != decide (0 < y)) = false ↔ 0 < x * y) := by
  rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy
  · have h := mul_pos_of_neg_of_neg hx hy
    simp [hx.not_gt, hy.not_gt, h, h.not_gt]
  · have h := mul_neg_of_neg_of_pos hx hy
    simp [hx.not_gt, hy, h, h.not_gt]
  · have h := mul_neg_of_pos_of_neg hx hy
    simp [hx, hy.not_gt, h, h.not_gt]
  · have h := mul_pos hx hy
    simp [hx, hy, h, h.not_gt]

/-- Alternation in the first two indices, for pairwise distinct indices. -/
theorem orientSign_swap_left {p : Fin 5 → Point} (hgp : IndexedGP p) (i j k : Fin 5)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    orientSign p j i k = !orientSign p i j k := by
  have h := hgp i j k hij hik hjk
  unfold orientSign
  rw [orient_swap_left]
  rcases h.lt_or_gt with h | h
  · simp [h, h.not_gt]
  · simp [h, h.not_gt]

/-- Alternation in the last two indices, for pairwise distinct indices. -/
theorem orientSign_swap_right {p : Fin 5 → Point} (hgp : IndexedGP p) (i j k : Fin 5)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    orientSign p i k j = !orientSign p i j k := by
  have h := hgp i j k hij hik hjk
  unfold orientSign
  rw [orient_swap_right]
  rcases h.lt_or_gt with h | h
  · simp [h, h.not_gt]
  · simp [h, h.not_gt]

/-- The four-point forbidden sign pattern never occurs for real orientations. -/
theorem orientSign_not_forb4 {p : Fin 5 → Point} (hgp : IndexedGP p) (a b c d : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) :
    ¬ (orientSign p a b c = !orientSign p a b d ∧ orientSign p a c d = !orientSign p a b d ∧
      orientSign p b c d = orientSign p a b d) := by
  rintro ⟨h1, h2, h3⟩
  have hid := orient_four_identity (p a) (p b) (p c) (p d)
  rcases Bool.eq_false_or_eq_true (orientSign p a b d) with hd | hd <;>
    rw [hd] at h1 h2 h3 <;> simp only [Bool.not_true, Bool.not_false] at h1 h2
  · have e1 := (orientSign_false_iff_neg hgp a b c hab hac hbc).1 h1
    have e2 := (orientSign_false_iff_neg hgp a c d hac had hcd).1 h2
    have e3 := (orientSign_true_iff p b c d).1 h3
    have e4 := (orientSign_true_iff p a b d).1 hd
    linarith
  · have e1 := (orientSign_true_iff p a b c).1 h1
    have e2 := (orientSign_true_iff p a c d).1 h2
    have e3 := (orientSign_false_iff_neg hgp b c d hbc hbd hcd).1 h3
    have e4 := (orientSign_false_iff_neg hgp a b d hab had hbd).1 hd
    linarith

/-- The five-point forbidden sign pattern never occurs for real orientations. -/
theorem orientSign_not_forb5 {p : Fin 5 → Point} (hgp : IndexedGP p) (a b c d e : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    ¬ ((orientSign p a b c == orientSign p a d e) = (orientSign p a b d != orientSign p a c e) ∧
      (orientSign p a b d != orientSign p a c e) =
        (orientSign p a b e == orientSign p a c d)) := by
  rintro ⟨h1, h2⟩
  have hpl := orient_plucker (p a) (p b) (p c) (p d) (p e)
  have n1 := hgp a b c hab hac hbc
  have n2 := hgp a d e had hae hde
  have n3 := hgp a b d hab had hbd
  have n4 := hgp a c e hac hae hce
  have n5 := hgp a b e hab hae hbe
  have n6 := hgp a c d hac had hcd
  unfold orientSign at h1 h2
  set x := orient (p a) (p b) (p c)
  set y := orient (p a) (p d) (p e)
  set z := orient (p a) (p b) (p d)
  set w := orient (p a) (p c) (p e)
  set u := orient (p a) (p b) (p e)
  set t := orient (p a) (p c) (p d)
  rcases Bool.eq_false_or_eq_true (decide (0 < z) != decide (0 < w)) with hm | hm <;>
    rw [hm] at h1 h2
  · have e1 := (beq_decide_pos_iff n1 n2).1.1 h1
    have e2 := (bne_decide_pos_iff n3 n4).1.1 hm
    have e3 := (beq_decide_pos_iff n5 n6).1.1 h2.symm
    linarith
  · have e1 := (beq_decide_pos_iff n1 n2).2.1 h1
    have e2 := (bne_decide_pos_iff n3 n4).2.1 hm
    have e3 := (beq_decide_pos_iff n5 n6).2.1 h2.symm
    linarith

/-- The orientation sign vector of a configuration in general position is consistent. -/
theorem consistent_orientSign {p : Fin 5 → Point} (hgp : IndexedGP p) :
    Consistent (orientSign p) :=
  ⟨fun i j k hij hik hjk => orientSign_swap_left hgp i j k hij hik hjk,
    fun i j k hij hik hjk => orientSign_swap_right hgp i j k hij hik hjk,
    fun a b c d hab hac had hbc hbd hcd => orientSign_not_forb4 hgp a b c d hab hac had hbc hbd hcd,
    fun a b c d e hab hac had hae hbc hbd hbe hcd hce hde =>
      orientSign_not_forb5 hgp a b c d e hab hac had hae hbc hbd hbe hcd hce hde⟩

/-- A quadrilateral certificate on an injective enumeration of `S` in general position yields an
empty convex quadrilateral in `S`. -/
theorem exists_emptyConvexPolygon_of_quadCert (S : Finset Point) (p : Fin 5 → Point)
    (hinj : Function.Injective p) (hgp : IndexedGP p) (hmem : ∀ i, p i ∈ S)
    (hsurj : ∀ q ∈ S, ∃ i, p i = q) (i j k l m : Fin 5) (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l)
    (hkm : k ≠ m) (hlm : l ≠ m) (hc : QuadCert (orientSign p) i j k l m) :
    ∃ V : Finset Point, V.card = 4 ∧ EmptyConvexPolygon S V := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := hc
  rw [orientSign_true_iff] at c1 c2 c3 c4 c5 c6 c7 c8 c10 c12
  rw [orientSign_false_iff_neg hgp i k j hik hij hjk.symm] at c9
  rw [orientSign_false_iff_neg hgp j l k hjl hjk hkl.symm] at c11
  refine ⟨{p i, p j, p k, p l}, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · exact hinj.ne hkl
    · simp [hinj.eq_iff, hjk, hjl]
    · simp [hinj.eq_iff, hij, hik, hil]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact hmem _
  · refine convexIndependent_of_separated _ ?_
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · refine ⟨p l, by simp, p j, by simp, hinj.ne hjl.symm, ?_, ?_⟩
      · rw [orient_swap_left]
        linarith
      · intro x hx hne
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact absurd rfl hne
        · exact (orient_right_self _ _).ge
        · rw [orient_swap_left]
          linarith
        · exact (orient_left_self _ _).ge
    · refine ⟨p i, by simp, p k, by simp, hinj.ne hik, c9, ?_⟩
      intro x hx hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact (orient_left_self _ _).ge
      · exact absurd rfl hne
      · exact (orient_right_self _ _).ge
      · exact c10.le
    · refine ⟨p j, by simp, p l, by simp, hinj.ne hjl, c11, ?_⟩
      intro x hx hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact c12.le
      · exact (orient_left_self _ _).ge
      · exact absurd rfl hne
      · exact (orient_right_self _ _).ge
    · refine ⟨p k, by simp, p i, by simp, hinj.ne hik.symm, ?_, ?_⟩
      · rw [orient_swap_left]
        linarith
      · intro x hx hne
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact (orient_right_self _ _).ge
        · rw [orient_swap_left]
          linarith
        · exact (orient_left_self _ _).ge
        · exact absurd rfl hne
  · intro q hq hqV
    obtain ⟨n, rfl⟩ := hsurj q hq
    simp only [Finset.mem_insert, Finset.mem_singleton, hinj.eq_iff, not_or] at hqV
    obtain ⟨hni, hnj, hnk, hnl⟩ := hqV
    have hn : n = m := by omega
    subst hn
    have hV : ∀ u w : Fin 5, u ≠ w → 0 ≤ orient (p u) (p w) (p i) →
        0 ≤ orient (p u) (p w) (p j) → 0 ≤ orient (p u) (p w) (p k) →
        0 ≤ orient (p u) (p w) (p l) → orient (p u) (p w) (p n) ≤ 0 →
        p n ∉ interior (convexHull ℝ (({p i, p j, p k, p l} : Finset Point) : Set Point)) := by
      intro u w huw h1 h2 h3 h4 h5
      refine not_mem_interior_convexHull_of_halfplane _ (p u) (p w) (p n) (hinj.ne huw) ?_ h5
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    rcases c13 with h | h | h | h <;> rw [orientSign_false_iff] at h
    · exact hV i j hij (orient_left_self _ _).ge (orient_right_self _ _).ge c1.le c2.le h
    · exact hV j k hjk c4.le (orient_left_self _ _).ge (orient_right_self _ _).ge c3.le h
    · exact hV k l hkl c5.le c6.le (orient_left_self _ _).ge (orient_right_self _ _).ge h
    · exact hV l i hil.symm (orient_right_self _ _).ge c7.le c8.le (orient_left_self _ _).ge h

/-- Every five points in general position contain an empty convex quadrilateral. -/
theorem forcesEmptyKGon_four_five : ForcesEmptyKGon 4 5 := by
  intro S hS hgp
  have hcard : Fintype.card S = 5 := by simp [hS]
  let e : S ≃ Fin 5 := Fintype.equivFinOfCardEq hcard
  let p : Fin 5 → Point := fun i => (e.symm i : Point)
  have hinj : Function.Injective p := Subtype.val_injective.comp e.symm.injective
  have hmem : ∀ i, p i ∈ S := fun i => (e.symm i).2
  have hsurj : ∀ q ∈ S, ∃ i, p i = q := fun q hq => ⟨e ⟨q, hq⟩, by simp [p]⟩
  have hgp' : IndexedGP p := fun i j k hij hik hjk =>
    hgp _ (hmem i) _ (hmem j) _ (hmem k) (hinj.ne hij) (hinj.ne hik) (hinj.ne hjk)
  obtain ⟨i, j, k, l, m, hij, hik, hil, him, hjk, hjl, hjm, hkl, hkm, hlm, hc⟩ :=
    exists_quadCert (orientSign p) (consistent_orientSign hgp')
  exact exists_emptyConvexPolygon_of_quadCert S p hinj hgp' hmem hsurj i j k l m hij hik hil him
    hjk hjl hjm hkl hkm hlm hc

end Horton
