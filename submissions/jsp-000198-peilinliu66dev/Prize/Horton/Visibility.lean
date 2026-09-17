/-
Copyright (c) 2026 JSP-000198 formalization contributors.
Released under the MIT license; see Prize/LICENSE_MIT.
Adapted from tester-lean/jsp-000198-horton-lean,
commit 313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0.
Mathematical construction: J. D. Horton.
Local port to Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/

import Prize.Horton.Basic

namespace Prize.Horton

open Prize.Geometry

theorem IsHorton.not_upperVisible_even_indices {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {a b : ℕ}
    (hab : a < b) (hb : b < 2 ^ (depth + 1))
    (ha0 : a % 2 = 0) (hb0 : b % 2 = 0) : ¬UpperVisible p a b := by
  have ha : a = 2 * (a / 2) := by omega
  have hb' : b = 2 * (b / 2) := by omega
  rw [pow_succ] at hb
  rw [ha, hb']
  exact h.not_upperVisible_even (by omega) (by omega)

theorem IsHorton.not_upperVisible_odd_odd_even {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {a b c : ℕ}
    (hab : a < b) (hbc : b < c) (hc : c < 2 ^ (depth + 1))
    (ha1 : a % 2 = 1) (hb1 : b % 2 = 1) (hc0 : c % 2 = 0) :
    ¬UpperVisible p a c := by
  intro hv
  have ha : a = 2 * (a / 2) + 1 := by omega
  have hb : b = 2 * (b / 2) + 1 := by omega
  have hc' : c = 2 * (c / 2) := by omega
  rw [pow_succ] at hc
  have hp : orient (p a) (p b) (p c) < 0 := by
    rw [ha, hb, hc']
    exact h.below (by omega) (by omega) (by omega)
  have hn := hv b hab hbc
  rw [orient_swap_right] at hn
  linarith

theorem IsHorton.not_upperVisible_even_odd_odd {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {a b c : ℕ}
    (hab : a < b) (hbc : b < c) (hc : c < 2 ^ (depth + 1))
    (ha0 : a % 2 = 0) (hb1 : b % 2 = 1) (hc1 : c % 2 = 1) :
    ¬UpperVisible p a c := by
  intro hv
  have ha : a = 2 * (a / 2) := by omega
  have hb : b = 2 * (b / 2) + 1 := by omega
  have hc' : c = 2 * (c / 2) + 1 := by omega
  rw [pow_succ] at hc
  have hp : orient (p b) (p c) (p a) < 0 := by
    rw [ha, hb, hc']
    exact h.below (by omega) (by omega) (by omega)
  have hn := hv b hab hbc
  rw [orient_swap_right, ← orient_cycle (p a) (p b) (p c)] at hn
  linarith

theorem IsHorton.upper_four_all_odd {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {a b c d : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d < 2 ^ (depth + 1))
    (vab : UpperVisible p a b) (vac : UpperVisible p a c)
    (vad : UpperVisible p a d) (vbc : UpperVisible p b c)
    (vbd : UpperVisible p b d) (vcd : UpperVisible p c d) :
    a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 1 ∧ d % 2 = 1 := by
  have hab0 : ¬(a % 2 = 0 ∧ b % 2 = 0) := fun ⟨ha, hb⟩ =>
    h.not_upperVisible_even_indices hab (by omega) ha hb vab
  have hac0 : ¬(a % 2 = 0 ∧ c % 2 = 0) := fun ⟨ha, hc⟩ =>
    h.not_upperVisible_even_indices (by omega) (by omega) ha hc vac
  have had0 : ¬(a % 2 = 0 ∧ d % 2 = 0) := fun ⟨ha, hd0⟩ =>
    h.not_upperVisible_even_indices (by omega) hd ha hd0 vad
  have hbc0 : ¬(b % 2 = 0 ∧ c % 2 = 0) := fun ⟨hb, hc⟩ =>
    h.not_upperVisible_even_indices hbc (by omega) hb hc vbc
  have hbd0 : ¬(b % 2 = 0 ∧ d % 2 = 0) := fun ⟨hb, hd0⟩ =>
    h.not_upperVisible_even_indices (by omega) hd hb hd0 vbd
  have hcd0 : ¬(c % 2 = 0 ∧ d % 2 = 0) := fun ⟨hc, hd0⟩ =>
    h.not_upperVisible_even_indices hcd hd hc hd0 vcd
  have ha011 : ¬(a % 2 = 0 ∧ b % 2 = 1 ∧ c % 2 = 1) :=
    fun ⟨ha, hb, hc⟩ =>
      h.not_upperVisible_even_odd_odd hab hbc (by omega) ha hb hc vac
  have hb011 : ¬(b % 2 = 0 ∧ c % 2 = 1 ∧ d % 2 = 1) :=
    fun ⟨hb, hc, hd1⟩ =>
      h.not_upperVisible_even_odd_odd hbc hcd hd hb hc hd1 vbd
  have hc110 : ¬(a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 0) :=
    fun ⟨ha, hb, hc⟩ =>
      h.not_upperVisible_odd_odd_even hab hbc (by omega) ha hb hc vac
  have hd110 : ¬(a % 2 = 1 ∧ b % 2 = 1 ∧ d % 2 = 0) :=
    fun ⟨ha, hb, hd0⟩ =>
      h.not_upperVisible_odd_odd_even hab (by omega) hd ha hb hd0 vad
  omega

/-- Four pairwise upper-visible points cannot occur in a Horton configuration. -/
theorem IsHorton.not_upper_four {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton depth p) {a b c d : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d < 2 ^ depth)
    (vab : UpperVisible p a b) (vac : UpperVisible p a c)
    (vad : UpperVisible p a d) (vbc : UpperVisible p b c)
    (vbd : UpperVisible p b d) (vcd : UpperVisible p c d) : False := by
  induction depth generalizing p a b c d with
  | zero => simp only [pow_zero] at hd; omega
  | succ depth ih =>
    obtain ⟨ha1, hb1, hc1, hd1⟩ :=
      h.upper_four_all_odd hab hbc hcd hd vab vac vad vbc vbd vcd
    have ha : a = 2 * (a / 2) + 1 := by omega
    have hb : b = 2 * (b / 2) + 1 := by omega
    have hc : c = 2 * (c / 2) + 1 := by omega
    have hd' : d = 2 * (d / 2) + 1 := by omega
    rw [pow_succ] at hd
    apply ih h.odd (a := a / 2) (b := b / 2) (c := c / 2) (d := d / 2)
      (by omega) (by omega) (by omega) (by omega)
    · exact upperVisible_odd (by simpa only [← ha, ← hb] using vab)
    · exact upperVisible_odd (by simpa only [← ha, ← hc] using vac)
    · exact upperVisible_odd (by simpa only [← ha, ← hd'] using vad)
    · exact upperVisible_odd (by simpa only [← hb, ← hc] using vbc)
    · exact upperVisible_odd (by simpa only [← hb, ← hd'] using vbd)
    · exact upperVisible_odd (by simpa only [← hc, ← hd'] using vcd)

theorem IsHorton.not_lowerVisible_odd_indices {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {a b : ℕ}
    (hab : a < b) (hb : b < 2 ^ (depth + 1))
    (ha1 : a % 2 = 1) (hb1 : b % 2 = 1) : ¬LowerVisible p a b := by
  have ha : a = 2 * (a / 2) + 1 := by omega
  have hb' : b = 2 * (b / 2) + 1 := by omega
  rw [pow_succ] at hb
  rw [ha, hb']
  exact h.not_lowerVisible_odd (by omega) (by omega)

theorem IsHorton.not_lowerVisible_even_even_odd {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {a b c : ℕ}
    (hab : a < b) (hbc : b < c) (hc : c < 2 ^ (depth + 1))
    (ha0 : a % 2 = 0) (hb0 : b % 2 = 0) (hc1 : c % 2 = 1) :
    ¬LowerVisible p a c := by
  intro hv
  have ha : a = 2 * (a / 2) := by omega
  have hb : b = 2 * (b / 2) := by omega
  have hc' : c = 2 * (c / 2) + 1 := by omega
  rw [pow_succ] at hc
  have hp : 0 < orient (p a) (p b) (p c) := by
    rw [ha, hb, hc']
    exact h.above (by omega) (by omega) (by omega)
  have hn := hv b hab hbc
  rw [orient_swap_right] at hn
  linarith

theorem IsHorton.not_lowerVisible_odd_even_even {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {a b c : ℕ}
    (hab : a < b) (hbc : b < c) (hc : c < 2 ^ (depth + 1))
    (ha1 : a % 2 = 1) (hb0 : b % 2 = 0) (hc0 : c % 2 = 0) :
    ¬LowerVisible p a c := by
  intro hv
  have ha : a = 2 * (a / 2) + 1 := by omega
  have hb : b = 2 * (b / 2) := by omega
  have hc' : c = 2 * (c / 2) := by omega
  rw [pow_succ] at hc
  have hp : 0 < orient (p b) (p c) (p a) := by
    rw [ha, hb, hc']
    exact h.above (by omega) (by omega) (by omega)
  have hn := hv b hab hbc
  rw [orient_swap_right, ← orient_cycle (p a) (p b) (p c)] at hn
  linarith

theorem IsHorton.lower_four_all_even {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton (depth + 1) p) {a b c d : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d < 2 ^ (depth + 1))
    (vab : LowerVisible p a b) (vac : LowerVisible p a c)
    (vad : LowerVisible p a d) (vbc : LowerVisible p b c)
    (vbd : LowerVisible p b d) (vcd : LowerVisible p c d) :
    a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 ∧ d % 2 = 0 := by
  have hab1 : ¬(a % 2 = 1 ∧ b % 2 = 1) := fun ⟨ha, hb⟩ =>
    h.not_lowerVisible_odd_indices hab (by omega) ha hb vab
  have hac1 : ¬(a % 2 = 1 ∧ c % 2 = 1) := fun ⟨ha, hc⟩ =>
    h.not_lowerVisible_odd_indices (by omega) (by omega) ha hc vac
  have had1 : ¬(a % 2 = 1 ∧ d % 2 = 1) := fun ⟨ha, hd1⟩ =>
    h.not_lowerVisible_odd_indices (by omega) hd ha hd1 vad
  have hbc1 : ¬(b % 2 = 1 ∧ c % 2 = 1) := fun ⟨hb, hc⟩ =>
    h.not_lowerVisible_odd_indices hbc (by omega) hb hc vbc
  have hbd1 : ¬(b % 2 = 1 ∧ d % 2 = 1) := fun ⟨hb, hd1⟩ =>
    h.not_lowerVisible_odd_indices (by omega) hd hb hd1 vbd
  have hcd1 : ¬(c % 2 = 1 ∧ d % 2 = 1) := fun ⟨hc, hd1⟩ =>
    h.not_lowerVisible_odd_indices hcd hd hc hd1 vcd
  have ha100 : ¬(a % 2 = 1 ∧ b % 2 = 0 ∧ c % 2 = 0) :=
    fun ⟨ha, hb, hc⟩ =>
      h.not_lowerVisible_odd_even_even hab hbc (by omega) ha hb hc vac
  have hb100 : ¬(b % 2 = 1 ∧ c % 2 = 0 ∧ d % 2 = 0) :=
    fun ⟨hb, hc, hd0⟩ =>
      h.not_lowerVisible_odd_even_even hbc hcd hd hb hc hd0 vbd
  have hc001 : ¬(a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 1) :=
    fun ⟨ha, hb, hc⟩ =>
      h.not_lowerVisible_even_even_odd hab hbc (by omega) ha hb hc vac
  have hd001 : ¬(a % 2 = 0 ∧ b % 2 = 0 ∧ d % 2 = 1) :=
    fun ⟨ha, hb, hd1⟩ =>
      h.not_lowerVisible_even_even_odd hab (by omega) hd ha hb hd1 vad
  omega

theorem IsHorton.not_lower_four {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton depth p) {a b c d : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d < 2 ^ depth)
    (vab : LowerVisible p a b) (vac : LowerVisible p a c)
    (vad : LowerVisible p a d) (vbc : LowerVisible p b c)
    (vbd : LowerVisible p b d) (vcd : LowerVisible p c d) : False := by
  induction depth generalizing p a b c d with
  | zero => simp only [pow_zero] at hd; omega
  | succ depth ih =>
    obtain ⟨ha0, hb0, hc0, hd0⟩ :=
      h.lower_four_all_even hab hbc hcd hd vab vac vad vbc vbd vcd
    have ha : a = 2 * (a / 2) := by omega
    have hb : b = 2 * (b / 2) := by omega
    have hc : c = 2 * (c / 2) := by omega
    have hd' : d = 2 * (d / 2) := by omega
    rw [pow_succ] at hd
    apply ih h.even (a := a / 2) (b := b / 2) (c := c / 2) (d := d / 2)
      (by omega) (by omega) (by omega) (by omega)
    · exact lowerVisible_even (by simpa only [← ha, ← hb] using vab)
    · exact lowerVisible_even (by simpa only [← ha, ← hc] using vac)
    · exact lowerVisible_even (by simpa only [← ha, ← hd'] using vad)
    · exact lowerVisible_even (by simpa only [← hb, ← hc] using vbc)
    · exact lowerVisible_even (by simpa only [← hb, ← hd'] using vbd)
    · exact lowerVisible_even (by simpa only [← hc, ← hd'] using vcd)

theorem IsHorton.upperVisible_card_le_three {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton depth p) {S : Finset ℕ} (hS : ∀ i ∈ S, i < 2 ^ depth)
    (hv : ∀ a ∈ S, ∀ b ∈ S, a < b → UpperVisible p a b) : S.card ≤ 3 := by
  by_contra hc
  have hc4 : 4 ≤ S.card := by omega
  let e : Fin 4 ↪o ℕ := S.orderEmbOfCardLe hc4
  have hm (i : Fin 4) : e i ∈ S := S.orderEmbOfCardLe_mem hc4 i
  have ho {i j : Fin 4} (hij : i < j) : e i < e j := e.strictMono hij
  exact h.not_upper_four (ho (by decide : (0 : Fin 4) < 1))
    (ho (by decide : (1 : Fin 4) < 2)) (ho (by decide : (2 : Fin 4) < 3))
    (hS _ (hm 3))
    (hv _ (hm 0) _ (hm 1) (ho (by decide)))
    (hv _ (hm 0) _ (hm 2) (ho (by decide)))
    (hv _ (hm 0) _ (hm 3) (ho (by decide)))
    (hv _ (hm 1) _ (hm 2) (ho (by decide)))
    (hv _ (hm 1) _ (hm 3) (ho (by decide)))
    (hv _ (hm 2) _ (hm 3) (ho (by decide)))

theorem IsHorton.lowerVisible_card_le_three {depth : ℕ} {p : ℕ → Point}
    (h : IsHorton depth p) {S : Finset ℕ} (hS : ∀ i ∈ S, i < 2 ^ depth)
    (hv : ∀ a ∈ S, ∀ b ∈ S, a < b → LowerVisible p a b) : S.card ≤ 3 := by
  by_contra hc
  have hc4 : 4 ≤ S.card := by omega
  let e : Fin 4 ↪o ℕ := S.orderEmbOfCardLe hc4
  have hm (i : Fin 4) : e i ∈ S := S.orderEmbOfCardLe_mem hc4 i
  have ho {i j : Fin 4} (hij : i < j) : e i < e j := e.strictMono hij
  exact h.not_lower_four (ho (by decide : (0 : Fin 4) < 1))
    (ho (by decide : (1 : Fin 4) < 2)) (ho (by decide : (2 : Fin 4) < 3))
    (hS _ (hm 3))
    (hv _ (hm 0) _ (hm 1) (ho (by decide)))
    (hv _ (hm 0) _ (hm 2) (ho (by decide)))
    (hv _ (hm 0) _ (hm 3) (ho (by decide)))
    (hv _ (hm 1) _ (hm 2) (ho (by decide)))
    (hv _ (hm 1) _ (hm 3) (ho (by decide)))
    (hv _ (hm 2) _ (hm 3) (ho (by decide)))

end Prize.Horton
