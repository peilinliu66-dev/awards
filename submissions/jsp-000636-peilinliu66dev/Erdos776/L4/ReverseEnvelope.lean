import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega

/-!
# L4: the reverse-envelope argument

This file isolates the order-theoretic core of L4 from the binomial-cascade
calculations.  It proves that any monotone shadow operation satisfying the
displayed reverse steps forces every feasible recurrence below `Ghat`, which
contradicts the independently forced state at level `r - 2`.

The remaining cascade layer must prove `ReverseSteps` and `TopStepIdentities`
for the Kruskal--Katona shadow.  Keeping that interface explicit prevents a
numerical checker from being mistaken for a proof of the symbolic identities.
-/

namespace Erdos776.L4

/-- The bounding sequence `Ĝ` in `docs/L4_PROOF.md`. -/
def Ghat (r i : ℕ) : ℕ :=
  if i = 2 then
    (r + 4).choose 2
  else if i = 3 then
    (r + 3).choose 3 + 3
  else if i = 4 then
    (r + 2).choose 4 + (r + 1).choose 3 + 6
  else if i = 5 then
    (r + 2).choose 5 + r.choose 4 + (r - 1).choose 3 + 10
  else if i = 6 then
    (r + 2).choose 6 + r.choose 5 + (r - 2).choose 4 +
      (r - 3).choose 3 + 21
  else if i = 7 then
    (r + 2).choose 7 + r.choose 6 + (r - 2).choose 5 +
      (r - 4).choose 4 + (r - 5).choose 3 + 120
  else
    (r + 2).choose i + r.choose (i - 1) + (r - 2).choose (i - 2) +
      (r - 4).choose (i - 3) + (r - 5).choose (i - 4) +
      (23 : ℕ).choose (i - 5)

/-- The recurrence forced by feasibility of the L4 profile. -/
def IsL4Chain (shadow : ℕ → ℕ → ℕ) (r : ℕ) (c : ℕ → ℕ) : Prop :=
  c (r + 1) = r ∧
    ∀ i, 2 ≤ i → i ≤ r → c i = r + shadow (i + 1) (c (i + 1))

/-- The reverse-step inequalities called Lemma RS in the manuscript. -/
def ReverseSteps (shadow : ℕ → ℕ → ℕ) (r : ℕ) : Prop :=
  ∀ i, 3 ≤ i → i ≤ r - 2 →
    Ghat r (i - 1) < r + shadow i (Ghat r i + 1)

/-- The closed form for the state forced three levels below the top. -/
def forcedTopValue (r : ℕ) : ℕ :=
  (r + 2).choose 4 + r.choose 3 + (r - 2).choose 2 + (3 * r - 9)

/-- The general formula for `Ĝ` specialized to the comparison level. -/
theorem ghat_at_top (r : ℕ) (hr : 29 ≤ r) :
    Ghat r (r - 2) =
      (r + 2).choose 4 + r.choose 3 + (r - 2).choose 2 +
        (r - 4) + (r - 5) + (23 : ℕ).choose (r - 7) := by
  have h4 : (r + 2).choose (r - 2) = (r + 2).choose 4 := by
    simpa only [show r + 2 - 4 = r - 2 by omega] using
      (Nat.choose_symm (n := r + 2) (k := 4) (by omega))
  have h3 : r.choose (r - 3) = r.choose 3 := by
    simpa only using (Nat.choose_symm (n := r) (k := 3) (by omega))
  have h2 : (r - 2).choose (r - 4) = (r - 2).choose 2 := by
    simpa only [show r - 2 - 2 = r - 4 by omega] using
      (Nat.choose_symm (n := r - 2) (k := 2) (by omega))
  have h1a : (r - 4).choose (r - 5) = r - 4 := by
    simpa only [Nat.choose_one_right, show r - 4 - 1 = r - 5 by omega] using (Nat.choose_symm (n := r - 4) (k := 1) (by omega))
  have h1b : (r - 5).choose (r - 6) = r - 5 := by
    simpa only [Nat.choose_one_right, show r - 5 - 1 = r - 6 by omega] using (Nat.choose_symm (n := r - 5) (k := 1) (by omega))
  simp only [Ghat, if_neg (show r - 2 ≠ 2 by omega),
    if_neg (show r - 2 ≠ 3 by omega), if_neg (show r - 2 ≠ 4 by omega),
    if_neg (show r - 2 ≠ 5 by omega), if_neg (show r - 2 ≠ 6 by omega),
    if_neg (show r - 2 ≠ 7 by omega)]
  rw [show r - 2 - 1 = r - 3 by omega,
    show r - 2 - 2 = r - 4 by omega,
    show r - 2 - 3 = r - 5 by omega,
    show r - 2 - 4 = r - 6 by omega,
    show r - 2 - 5 = r - 7 by omega,
    h4, h3, h2, h1a, h1b]

/-- The tapering corrector is strictly smaller than the final margin. -/
theorem corrector_lt_r (r : ℕ) (hr : 29 ≤ r) :
    (23 : ℕ).choose (r - 7) < r := by
  rcases lt_or_eq_of_le hr with hr' | rfl
  · by_cases h30 : r = 30
    · subst r
      simp
    · have hr31 : 31 ≤ r := by omega
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      omega
  · simp

/-- The final positive margin, including the exceptional cases 29 and 30. -/
theorem ghat_lt_forcedTopValue (r : ℕ) (hr : 29 ≤ r) :
    Ghat r (r - 2) < forcedTopValue r := by
  rw [ghat_at_top r hr]
  unfold forcedTopValue
  have hc := corrector_lt_r r hr
  omega

/-- Lemma L4-T, stated as the exact value needed by the envelope argument. -/
def ForcedTop (r : ℕ) (c : ℕ → ℕ) : Prop :=
  c (r - 2) = forcedTopValue r

/-- The state one level below the top, in the proof of Lemma L4-T. -/
def topRValue (r : ℕ) : ℕ :=
  (r + 2).choose 2 + (r - 1)

/-- The state two levels below the top, in the proof of Lemma L4-T. -/
def topRm1Value (r : ℕ) : ℕ :=
  (r + 2).choose (r - 1) + r.choose 2 + r

/--
The three concrete cascade evaluations used in Lemma L4-T.  This is a
deliberately narrow interface for the future numerical-cascade module.
-/
def TopStepIdentities (shadow : ℕ → ℕ → ℕ) (r : ℕ) : Prop :=
  shadow (r + 1) r = (r + 2).choose 2 - 1 ∧
  shadow r (topRValue r) = (r + 2).choose (r - 1) + r.choose 2 ∧
  shadow (r - 1) (topRm1Value r) =
    (r + 2).choose (r - 2) + r.choose (r - 3) +
      (r - 2).choose (r - 4) + (r - 4) + (r - 5)

/-- Lemma L4-T follows from its three explicit cascade evaluations. -/
theorem forcedTop_of_topStepIdentities
    (shadow : ℕ → ℕ → ℕ) (r : ℕ) (c : ℕ → ℕ)
    (hr : 15 ≤ r)
    (hchain : IsL4Chain shadow r c)
    (htop : TopStepIdentities shadow r) : ForcedTop r c := by
  have hcr : c r = topRValue r := by
    rw [hchain.2 r (by omega) (by omega), hchain.1, htop.1]
    unfold topRValue
    have hpos : 0 < (r + 2).choose 2 := Nat.choose_pos (by omega)
    omega
  have hcrm1 : c (r - 1) = topRm1Value r := by
    have hrec := hchain.2 (r - 1) (by omega) (by omega)
    rw [show r - 1 + 1 = r by omega, hcr, htop.2.1] at hrec
    unfold topRm1Value
    omega
  have hcrm2 := hchain.2 (r - 2) (by omega) (by omega)
  rw [show r - 2 + 1 = r - 1 by omega, hcrm1, htop.2.2] at hcrm2
  unfold ForcedTop forcedTopValue
  rw [hcrm2]
  have h4 : (r + 2).choose (r - 2) = (r + 2).choose 4 := by
    simpa only [show r + 2 - 4 = r - 2 by omega] using
      (Nat.choose_symm (n := r + 2) (k := 4) (by omega))
  have h3 : r.choose (r - 3) = r.choose 3 := by
    simpa only using (Nat.choose_symm (n := r) (k := 3) (by omega))
  have h2 : (r - 2).choose (r - 4) = (r - 2).choose 2 := by
    simpa only [show r - 2 - 2 = r - 4 by omega] using
      (Nat.choose_symm (n := r - 2) (k := 2) (by omega))
  rw [h4, h3, h2]
  omega

/--
Lemma IND from the paper.  Notice that this proof uses only monotonicity,
the recurrence, the level-2 capacity, and Lemma RS.
-/
theorem chain_le_ghat
    (shadow : ℕ → ℕ → ℕ) (r : ℕ) (c : ℕ → ℕ)
    (hmono : ∀ k, Monotone (shadow k))
    (hchain : IsL4Chain shadow r c)
    (hcapacity : c 2 ≤ (r + 4).choose 2)
    (hreverse : ReverseSteps shadow r) :
    ∀ i, 2 ≤ i → i ≤ r - 2 → c i ≤ Ghat r i := by
  intro i hi hir
  induction i, hi using Nat.le_induction with
  | base =>
      simpa [Ghat] using hcapacity
  | succ i hi ih =>
      have hir' : i ≤ r := by omega
      have hrec := hchain.2 i hi hir'
      have hrs : Ghat r i < r + shadow (i + 1) (Ghat r (i + 1) + 1) := by
        simpa using hreverse (i + 1) (by omega) (by omega)
      by_contra hnot
      have hlarge : Ghat r (i + 1) + 1 ≤ c (i + 1) := by omega
      have hshadow := hmono (i + 1) hlarge
      have : Ghat r i < c i := by
        rw [hrec]
        exact lt_of_lt_of_le hrs (Nat.add_le_add_left hshadow r)
      exact (Nat.not_lt_of_ge (ih (by omega))) this

/--
The final, short logical core of L4: the reverse envelope and the forced top
state are incompatible with level-2 capacity.
-/
theorem not_l4_chain_of_forcedTop_gt
    (shadow : ℕ → ℕ → ℕ) (r : ℕ)
    (hr : 4 ≤ r)
    (hmono : ∀ k, Monotone (shadow k))
    (hreverse : ReverseSteps shadow r)
    (htop : Ghat r (r - 2) < forcedTopValue r) :
    ¬ ∃ c : ℕ → ℕ,
      IsL4Chain shadow r c ∧
      c 2 ≤ (r + 4).choose 2 ∧
      ForcedTop r c := by
  rintro ⟨c, hchain, hcapacity, hforced⟩
  have hbound := chain_le_ghat shadow r c hmono hchain hcapacity hreverse
    (r - 2) (by omega) (by omega)
  unfold ForcedTop at hforced
  rw [hforced] at hbound
  exact (Nat.not_lt_of_ge hbound) htop

/-- L4's contradiction when Lemma L4-T is already available. -/
theorem not_l4_chain_with_forcedTop
    (shadow : ℕ → ℕ → ℕ) (r : ℕ)
    (hr : 29 ≤ r)
    (hmono : ∀ k, Monotone (shadow k))
    (hreverse : ReverseSteps shadow r) :
    ¬ ∃ c : ℕ → ℕ,
      IsL4Chain shadow r c ∧
      c 2 ≤ (r + 4).choose 2 ∧
      ForcedTop r c :=
  not_l4_chain_of_forcedTop_gt shadow r (by omega) hmono hreverse
    (ghat_lt_forcedTopValue r hr)

/--
L4's contradiction reduced exactly to monotonicity and the displayed cascade
evaluations (Lemma RS and the three top steps of Lemma L4-T).
-/
theorem not_l4_chain
    (shadow : ℕ → ℕ → ℕ) (r : ℕ)
    (hr : 29 ≤ r)
    (hmono : ∀ k, Monotone (shadow k))
    (hreverse : ReverseSteps shadow r)
    (htop : TopStepIdentities shadow r) :
    ¬ ∃ c : ℕ → ℕ,
      IsL4Chain shadow r c ∧
      c 2 ≤ (r + 4).choose 2 := by
  rintro ⟨c, hchain, hcapacity⟩
  exact not_l4_chain_with_forcedTop shadow r hr hmono hreverse
    ⟨c, hchain, hcapacity, forcedTop_of_topStepIdentities shadow r c (by omega) hchain htop⟩

end Erdos776.L4
