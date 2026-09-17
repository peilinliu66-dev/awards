import Erdos776.Uniform.GlobalThreshold

/-!
# Supersolutions for the lower-window recurrence

This is the formal comparison principle used throughout Sections 3--11 of
the uniform proof.  Once a numerical sequence pays each incoming load after
shadowing, monotonicity of the canonical Kruskal--Katona shadow keeps the
exact lower-window recurrence below it.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- A supersolution for the constant-load part of the lower-window recurrence. -/
def IsLowerWindowSupersolution (r : ℕ) (V : ℕ → ℕ) : Prop :=
  r - 6 ≤ V (r + 1) ∧
    ∀ i, 2 ≤ i → i ≤ r →
      r + canonicalShadow (i + 1) (V (i + 1)) ≤ V i

theorem lowerWindowProfile_eq_of_le
    {r i : ℕ} (hi : i ≤ r) : lowerWindowProfile r i = r := by
  simp [lowerWindowProfile]
  omega

@[simp] theorem lowerWindowChain_top_value (r : ℕ) :
    lowerWindowChain r (r + 1) = r - 6 := by
  rw [lowerWindowChain_step r (r + 1) le_rfl,
    lowerWindowProfile, if_pos rfl, lowerWindowChain_above_top,
    canonicalShadow_zero, Nat.add_zero]

/-- The exact recurrence stays below every supersolution. -/
theorem lowerWindowChain_le_supersolution
    {r : ℕ} {V : ℕ → ℕ} (hV : IsLowerWindowSupersolution r V) :
    ∀ i, 2 ≤ i → i ≤ r + 1 → lowerWindowChain r i ≤ V i := by
  intro i hi2 hir
  apply Nat.decreasingInduction'
      (P := fun k => lowerWindowChain r k ≤ V k)
      (m := i) (n := r + 1) ?_ hir
  · rw [lowerWindowChain_top_value]
    exact hV.1
  · intro k hkr hik ih
    have hk2 : 2 ≤ k := hi2.trans hik
    have hkle : k ≤ r := by omega
    rw [lowerWindowChain_step r k (by omega), lowerWindowProfile_eq_of_le hkle]
    have hshadow := canonicalShadow_mono (k + 1) (by omega) ih
    exact (Nat.add_le_add_left hshadow r).trans (hV.2 k hk2 hkle)

/-- A capacity-bounded supersolution proves the exact lower-window predicate. -/
theorem lowerWindowFits_of_supersolution
    {r : ℕ} {V : ℕ → ℕ}
    (hV : IsLowerWindowSupersolution r V)
    (hcap : ∀ i, 2 ≤ i → i ≤ r + 1 → V i ≤ (r + 4).choose i) :
    LowerWindowFits r := by
  intro i hi2 hir
  by_cases htop : i = r + 2
  · subst i
    simp
  · have hir' : i ≤ r + 1 := by omega
    exact (lowerWindowChain_le_supersolution hV i hi2 hir').trans
      (hcap i hi2 hir')

/-- It is enough to give supersolution steps as equalities. -/
theorem isLowerWindowSupersolution_of_eq
    {r : ℕ} {V : ℕ → ℕ}
    (htop : r - 6 ≤ V (r + 1))
    (hstep : ∀ i, 2 ≤ i → i ≤ r →
      V i = r + canonicalShadow (i + 1) (V (i + 1))) :
    IsLowerWindowSupersolution r V := by
  refine ⟨htop, ?_⟩
  intro i hi2 hir
  exact (hstep i hi2 hir).ge

end Erdos776.Uniform
