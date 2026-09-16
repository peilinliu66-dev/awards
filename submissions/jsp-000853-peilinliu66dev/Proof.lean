import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
JSP-000853 / Erdős 1025: the complete order-of-magnitude answer.
Mathematical attribution: Spencer (1972), Furedi (1991), and the exposition
and grid construction in Conlon--Fox--Sudakov (2016), Section 2.
This is a formalization of known mathematics.
-/

open Finset

namespace Erdos1025

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A map from unordered two-element sets to a point outside the input set. -/
structure PairMap (V : Type*) [Fintype V] [DecidableEq V] where
  value : {s : Finset V // s.card = 2} → V
  outside : ∀ s, value s ∉ s.val

def PairMap.Free (f : PairMap V) (S : Finset V) : Prop :=
  ∀ p : {s : Finset V // s.card = 2}, p.val ⊆ S → f.value p ∉ S

def Independent (H : Finset (Finset V)) (S : Finset V) : Prop :=
  ∀ e ∈ H, ¬e ⊆ S

/-- Delete at most one point for each edge contained in a chosen sample. -/
theorem deletion (H : Finset (Finset V))
    (hne : ∀ e ∈ H, e.Nonempty) (S : Finset V) :
    ∃ T ⊆ S, Independent H T ∧
      S.card ≤ T.card + (H.filter (· ⊆ S)).card := by
  classical
  let B := H.filter (· ⊆ S)
  let pick : {e // e ∈ B} → V := fun e =>
    (hne e.val (Finset.mem_filter.mp e.property).1).choose
  let D := B.attach.image pick
  refine ⟨S \ D, sdiff_subset, ?_, ?_⟩
  · intro e he hes
    have heb : e ∈ B := mem_filter.mpr ⟨he, hes.trans sdiff_subset⟩
    have hp : pick ⟨e, heb⟩ ∈ e :=
      (hne e (Finset.mem_filter.mp heb).1).choose_spec
    have hd : pick ⟨e, heb⟩ ∈ D := mem_image.mpr ⟨⟨e, heb⟩, by simp, rfl⟩
    exact (mem_sdiff.mp (hes hp)).2 hd
  · have hD : D.card ≤ B.card := (card_image_le).trans_eq card_attach
    have := card_le_card_sdiff_add_card (s := S) (t := D)
    change S.card ≤ (S \ D).card + B.card
    omega

/-- Exact double-counting of incidences between triples and fixed-size samples. -/
theorem sum_triples_in_samples (H : Finset (Finset V))
    (h3 : ∀ e ∈ H, e.card = 3) (k : ℕ) (hk : 3 ≤ k) :
    ∑ S ∈ (univ : Finset V).powersetCard k, (H.filter (· ⊆ S)).card =
      H.card * (Fintype.card V - 3).choose (k - 3) := by
  classical
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  calc
    _ = ∑ e ∈ H, ((univ.powersetCard k).filter (e ⊆ ·)).card := by
      apply sum_congr rfl
      intro e he
      rw [card_eq_sum_ones, sum_filter]
    _ = ∑ e ∈ H, (Fintype.card V - 3).choose (k - 3) := by
      apply sum_congr rfl
      intro e he
      rw [card_filter_powersetCard_subset e univ k (subset_univ _) (by rw [h3 e he]; exact hk)]
      simp [h3 e he]
    _ = _ := by simp

theorem six_choose_three (n : ℕ) : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  have h2 := Nat.choose_succ_right_eq n 1
  have h3 := Nat.choose_succ_right_eq n 2
  simp only [Nat.choose_one_right] at h2
  nlinarith [congrArg (fun t => t * (n - 2)) h2]

/-- Sampling at most sqrt(n) vertices loses at most half to bad triples. -/
theorem sampling_bound (n k : ℕ) (hk : 3 ≤ k) (hkn : k * k ≤ n) :
    2 * n.choose 2 * (n - 3).choose (k - 3) ≤ k * n.choose k := by
  have hn : 3 ≤ n := by nlinarith
  have hid := Nat.choose_mul (n := n) hk
  have hn3 := Nat.choose_succ_right_eq n 2
  have heq :
      (2 * n.choose 2 * (n - 3).choose (k - 3)) * (n - 2) =
        (k * n.choose k) * ((k - 1) * (k - 2)) := by
    calc
      _ = 6 * (n.choose 3 * (n - 3).choose (k - 3)) := by
        nlinarith [congrArg (fun t => 2 * t * (n - 3).choose (k - 3)) hn3]
      _ = 6 * (n.choose k * k.choose 3) := by rw [hid]
      _ = n.choose k * (6 * k.choose 3) := by ring
      _ = _ := by rw [six_choose_three]; ring
  have hsmall : (k - 1) * (k - 2) ≤ n - 2 := by
    have h1 := Nat.sub_add_cancel (show 1 ≤ k by omega)
    have h2 := Nat.sub_add_cancel (show 2 ≤ k by omega)
    have h3 := Nat.sub_add_cancel (show 2 ≤ n by omega)
    nlinarith
  have hmul := Nat.mul_le_mul_left (k * n.choose k) hsmall
  rw [← heq] at hmul
  exact le_of_mul_le_mul_right hmul (by omega)

/-- A complete finite lower bound, formulated for the associated triple system. -/
theorem hypergraph_lower (H : Finset (Finset V))
    (h3 : ∀ e ∈ H, e.card = 3)
    (hsize : H.card ≤ (Fintype.card V).choose 2)
    (k : ℕ) (hk : 3 ≤ k) (hkn : k * k ≤ Fintype.card V) :
    ∃ T : Finset V, Independent H T ∧ k ≤ 2 * T.card := by
  classical
  let samples := (univ : Finset V).powersetCard k
  have hkN : k ≤ Fintype.card V := by nlinarith
  have hs : samples.Nonempty := powersetCard_nonempty.mpr (by simpa using hkN)
  have hsum :
      (∑ S ∈ samples, 2 * (H.filter (· ⊆ S)).card) ≤ ∑ _S ∈ samples, k := by
    rw [← mul_sum, sum_triples_in_samples H h3 k hk]
    have h := sampling_bound (Fintype.card V) k hk hkn
    have hm := Nat.mul_le_mul_right ((Fintype.card V - 3).choose (k - 3))
      (Nat.mul_le_mul_left 2 hsize)
    simp only [sum_const, smul_eq_mul, samples, card_powersetCard, card_univ]
    nlinarith
  obtain ⟨S, hS, hSbad⟩ := exists_le_of_sum_le hs hsum
  have hScard : S.card = k := (mem_powersetCard.mp hS).2
  obtain ⟨T, hTS, hTi, hTc⟩ := deletion H
    (fun e he => card_pos.mp (by rw [h3 e he]; omega)) S
  exact ⟨T, hTi, by omega⟩

def PairMap.edges (f : PairMap V) : Finset (Finset V) :=
  ((univ : Finset V).powersetCard 2).attach.image fun p =>
    insert (f.value ⟨p.val, (mem_powersetCard.mp p.property).2⟩) p.val

theorem PairMap.edges_card_three (f : PairMap V) :
    ∀ e ∈ f.edges, e.card = 3 := by
  classical
  intro e he
  obtain ⟨p, hp, rfl⟩ := mem_image.mp he
  rw [card_insert_of_notMem (f.outside _), (mem_powersetCard.mp p.property).2]

theorem PairMap.edges_card_le (f : PairMap V) :
    f.edges.card ≤ (Fintype.card V).choose 2 := by
  exact (card_image_le).trans_eq (by simp)

theorem PairMap.free_of_independent (f : PairMap V) (S : Finset V)
    (h : Independent f.edges S) : f.Free S := by
  intro p hp hf
  have hpair : p.val ∈ (univ : Finset V).powersetCard 2 :=
    mem_powersetCard.mpr ⟨subset_univ _, p.property⟩
  have he : insert (f.value p) p.val ∈ f.edges :=
    mem_image.mpr ⟨⟨p.val, hpair⟩, by simp, rfl⟩
  exact h _ he (insert_subset hf hp)

/-- The lower half of the full answer, for every n ≥ 9. -/
theorem PairMap.lower (f : PairMap V) (hn : 9 ≤ Fintype.card V) :
    ∃ T : Finset V, f.Free T ∧ Nat.sqrt (Fintype.card V) ≤ 2 * T.card := by
  obtain ⟨T, hT, hc⟩ := hypergraph_lower f.edges f.edges_card_three f.edges_card_le
    (Nat.sqrt (Fintype.card V)) (Nat.le_sqrt.mpr hn) (Nat.sqrt_le _)
  exact ⟨T, f.free_of_independent T hT, hc⟩

section Grid

variable {R C : Type*} [Fintype R] [Fintype C] [LinearOrder R] [LinearOrder C]
variable (row : V → R) (col : V → C)

/-- The oriented opposite corner of a pair of points in distinct rows and columns. -/
def Corner (s : Finset V) (z : V) : Prop :=
  ∃ a b, a ∈ s ∧ b ∈ s ∧ row a < row b ∧ col a ≠ col b ∧
    row z = row a ∧ col z = col b

theorem corner_pair_iff (a b z : V) (hab : row a < row b) :
    Corner row col {a, b} z ↔ col a ≠ col b ∧ row z = row a ∧ col z = col b := by
  simp only [Corner, mem_insert, mem_singleton]
  constructor
  · rintro ⟨u, v, hu, hv, huv, hc, hrz, hcz⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (lt_irrefl _ huv).elim
    · exact ⟨hc, hrz, hcz⟩
    · exact (lt_asymm hab huv).elim
    · exact (lt_irrefl _ huv).elim
  · rintro ⟨hc, hr, hy⟩
    exact ⟨a, b, Or.inl rfl, Or.inr rfl, hab, hc, hr, hy⟩

theorem pair_eq_of_corner {s : Finset V} {z : V} (hs : s.card = 2)
    (hz : Corner row col s z) :
    ∃ a b, s = {a, b} ∧ row a < row b ∧ col a ≠ col b ∧
      row z = row a ∧ col z = col b := by
  obtain ⟨a, b, ha, hb, hr, hc, hz⟩ := hz
  have hab : a ≠ b := fun he => lt_irrefl _ (he ▸ hr)
  have hsub : ({a, b} : Finset V) ⊆ s := insert_subset ha (singleton_subset_iff.mpr hb)
  have heq : s = {a, b} := (eq_of_subset_of_card_le hsub (by simp [hs, hab])).symm
  exact ⟨a, b, heq, hr, hc, hz⟩

theorem corner_outside {s : Finset V} {z : V} (hs : s.card = 2)
    (hz : Corner row col s z) : z ∉ s := by
  obtain ⟨a, b, rfl, hr, hc, hzrow, hzcol⟩ := pair_eq_of_corner row col hs hz
  simp only [mem_insert, mem_singleton, not_or]
  constructor
  · intro h; exact hc (h ▸ hzcol)
  · intro h; have := h ▸ hzrow; exact (ne_of_lt hr) this.symm

theorem corner_unique
    (hinj : ∀ a b, row a = row b → col a = col b → a = b)
    {s : Finset V} {z w : V} (hs : s.card = 2)
    (hz : Corner row col s z) (hw : Corner row col s w) : z = w := by
  obtain ⟨a, b, rfl, hr, hc, hzrow, hzcol⟩ := pair_eq_of_corner row col hs hz
  obtain ⟨_, hwrow, hwcol⟩ := (corner_pair_iff row col a b w hr).mp hw
  exact hinj z w (hzrow.trans hwrow.symm) (hzcol.trans hwcol.symm)

theorem exists_outside_pair (hn : 3 ≤ Fintype.card V) (s : Finset V) (hs : s.card = 2) :
    ∃ z : V, z ∉ s := by
  obtain ⟨z, _, hz⟩ := exists_mem_notMem_of_card_lt_card
    (s := s) (t := univ) (by simpa [hs] using (show 2 < Fintype.card V by omega))
  exact ⟨z, hz⟩

noncomputable def gridMap (hn : 3 ≤ Fintype.card V) : PairMap V := by
  classical
  exact {
    value := fun p => if h : ∃ z, Corner row col p.val z then h.choose
      else (exists_outside_pair hn p.val p.property).choose
    outside := fun p => by
      split_ifs with h
      · exact corner_outside row col p.property h.choose_spec
      · exact (exists_outside_pair hn p.val p.property).choose_spec }

theorem gridMap_value (hn : 3 ≤ Fintype.card V)
    (hinj : ∀ a b, row a = row b → col a = col b → a = b)
    (p : {s : Finset V // s.card = 2}) (z : V)
    (hz : Corner row col p.val z) : (gridMap row col hn).value p = z := by
  classical
  have hex : ∃ w, Corner row col p.val w := ⟨z, hz⟩
  simp only [gridMap, dif_pos hex]
  exact corner_unique row col hinj p.property hex.choose_spec hz

/-- Any independent set is covered by one row-maximum or one column-maximum per line. -/
theorem gridMap_upper (hn : 3 ≤ Fintype.card V)
    (hinj : ∀ a b, row a = row b → col a = col b → a = b)
    (S : Finset V) (hfree : (gridMap row col hn).Free S) :
    S.card ≤ Fintype.card R + Fintype.card C := by
  classical
  let A := S.filter (fun p => ∀ q ∈ S, row q = row p → col q ≤ col p)
  let B := S.filter (fun p => ∀ q ∈ S, col q = col p → row q ≤ row p)
  have hA : A.card ≤ Fintype.card R := by
    have hi : Set.InjOn row (A : Set V) := by
      intro a ha b hb hr
      have ha' := (mem_filter.mp ha).2
      have hb' := (mem_filter.mp hb).2
      exact hinj a b hr (le_antisymm
        (hb' a (mem_filter.mp ha).1 hr)
        (ha' b (mem_filter.mp hb).1 hr.symm))
    simpa using card_le_card_of_injOn row (t := univ) (by intros; simp) hi
  have hB : B.card ≤ Fintype.card C := by
    have hi : Set.InjOn col (B : Set V) := by
      intro a ha b hb hc
      have ha' := (mem_filter.mp ha).2
      have hb' := (mem_filter.mp hb).2
      exact hinj a b (le_antisymm
        (hb' a (mem_filter.mp ha).1 hc)
        (ha' b (mem_filter.mp hb).1 hc.symm)) hc
    simpa using card_le_card_of_injOn col (t := univ) (by intros; simp) hi
  have hcover : S ⊆ A ∪ B := by
    intro z hz
    by_cases haz : z ∈ A
    · exact mem_union_left _ haz
    by_cases hbz : z ∈ B
    · exact mem_union_right _ hbz
    have haz' : ¬∀ a ∈ S, row a = row z → col a ≤ col z := by
      intro h; exact haz (mem_filter.mpr ⟨hz, h⟩)
    have hbz' : ¬∀ b ∈ S, col b = col z → row b ≤ row z := by
      intro h; exact hbz (mem_filter.mpr ⟨hz, h⟩)
    push Not at haz' hbz'
    obtain ⟨a, ha, har, hac⟩ := haz'
    obtain ⟨b, hb, hbc, hbr⟩ := hbz'
    have hr : row a < row b := har ▸ hbr
    have hc : col a ≠ col b := by rw [hbc]; exact ne_of_gt hac
    have hab : a ≠ b := fun h => lt_irrefl _ (h ▸ hr)
    let p : {s : Finset V // s.card = 2} := ⟨{a, b}, by simp [hab]⟩
    have hcorner : Corner row col p.val z := by
      apply (corner_pair_iff row col a b z hr).mpr
      exact ⟨hc, har.symm, hbc.symm⟩
    have hv := gridMap_value row col hn hinj p z hcorner
    have hnot := hfree p (insert_subset ha (singleton_subset_iff.mpr hb))
    rw [hv] at hnot
    exact (hnot hz).elim
  exact (card_le_card hcover).trans ((card_union_le A B).trans (Nat.add_le_add hA hB))

end Grid

/-- The upper half of the answer holds for every n, not just perfect squares. -/
theorem upper (n : ℕ) (hn : 3 ≤ n) :
    ∃ f : PairMap (Fin n), ∀ S : Finset (Fin n), f.Free S →
      S.card ≤ 2 * (Nat.sqrt n + 1) := by
  classical
  let m := Nat.sqrt n + 1
  have hc : Fintype.card (Fin n) ≤ Fintype.card (Fin m × Fin m) := by
    simp only [Fintype.card_fin, Fintype.card_prod]
    exact le_of_lt (Nat.lt_succ_sqrt n)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  let row := fun v : Fin n => (e v).1
  let col := fun v : Fin n => (e v).2
  have hi : ∀ a b, row a = row b → col a = col b → a = b := by
    intro a b hr hc
    exact e.injective (Prod.ext hr hc)
  have hn' : 3 ≤ Fintype.card (Fin n) := by simpa using hn
  refine ⟨gridMap row col hn', ?_⟩
  intro S hS
  simpa only [Fintype.card_fin, ← two_mul] using gridMap_upper row col hn' hi S hS

/-- Maximum cardinality of a free set for one particular pair map. -/
noncomputable def independenceNumber (f : PairMap V) : ℕ := by
  classical
  exact ((univ : Finset (Finset V)).filter f.Free).sup Finset.card

theorem card_le_independenceNumber (f : PairMap V) {S : Finset V} (hS : f.Free S) :
    S.card ≤ independenceNumber f := by
  classical
  exact le_sup (mem_filter.mpr ⟨mem_univ _, hS⟩)

theorem independenceNumber_le (f : PairMap V) (b : ℕ)
    (h : ∀ S, f.Free S → S.card ≤ b) : independenceNumber f ≤ b := by
  classical
  exact Finset.sup_le_iff.mpr (fun S hS => h S (mem_filter.mp hS).2)

/-- The original extremal function: the minimum, over all pair maps, of their
largest free-set size. We use it below only for n ≥ 9, where the domain is nonempty. -/
noncomputable def g (n : ℕ) : ℕ :=
  sInf {a : ℕ | ∃ f : PairMap (Fin n), independenceNumber f = a}

/-- Full integer form of the answer: both bounds, uniformly for all n ≥ 9. -/
theorem full_answer (n : ℕ) (hn : 9 ≤ n) :
    Nat.sqrt n ≤ 2 * g n ∧ g n ≤ 2 * (Nat.sqrt n + 1) := by
  classical
  obtain ⟨f, hf⟩ := upper n (by omega)
  have hne : {a : ℕ | ∃ f : PairMap (Fin n), independenceNumber f = a}.Nonempty :=
    ⟨independenceNumber f, f, rfl⟩
  constructor
  · obtain ⟨f₀, hf₀⟩ : ∃ f₀ : PairMap (Fin n), independenceNumber f₀ = g n :=
      Nat.sInf_mem hne
    obtain ⟨T, hT, hTc⟩ := f₀.lower (by simpa using hn)
    have hm := card_le_independenceNumber f₀ hT
    simp only [Fintype.card_fin] at hTc
    omega
  · calc
      g n ≤ independenceNumber f := Nat.sInf_le ⟨f, rfl⟩
      _ ≤ 2 * (Nat.sqrt n + 1) := independenceNumber_le f _ hf

/-- The complete original order-of-magnitude conclusion, with explicit constants.
No question about sharp leading constants or an exact formula for g(n) is
asserted in Erdős 1025. -/
theorem erdos_1025 (n : ℕ) (hn : 9 ≤ n) :
    (1 / 4 : ℝ) * Real.sqrt n ≤ g n ∧ (g n : ℝ) ≤ 4 * Real.sqrt n := by
  have h := full_answer n hn
  have hlow : (Nat.sqrt n : ℝ) ≤ 2 * (g n : ℝ) := by exact_mod_cast h.1
  have hupp : (g n : ℝ) ≤ 2 * ((Nat.sqrt n : ℝ) + 1) := by exact_mod_cast h.2
  have hs : (3 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast (Nat.le_sqrt.mpr hn : 3 ≤ Nat.sqrt n)
  have hl : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have hr : Real.sqrt n ≤ (Nat.sqrt n : ℝ) + 1 := Real.real_sqrt_le_nat_sqrt_succ
  constructor <;> linarith

#print axioms erdos_1025

end Erdos1025
