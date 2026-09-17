import JSP619Assembly

/-! Unconditional endpoints for the original Erdős 752 question.
The explicit constants are uniform over finite nonempty simple graphs. -/

noncomputable section
namespace JSP619
universe u

theorem erdos_752_nat {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s k : ℕ) (hs : 1 ≤ s) (hk : 576 ≤ k)
    (hdeg : ∀ v, k ≤ G.degree v)
    (hgirth : ∀ v (p : G.Walk v v), p.IsCycle → 2 * s < p.length) :
    k ^ s ≤ (24 * 192 ^ s) * (cycleLengths G).card :=
  erdos752_nat_from_moore mooreBound_proved G s k hs hk hdeg hgirth

theorem erdos_752_explicit {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s k : ℕ) (hs : 1 ≤ s) (hk : 576 ≤ k)
    (hdeg : ∀ v, k ≤ G.degree v)
    (hgirth : ∀ v (p : G.Walk v v), p.IsCycle → 2 * s < p.length) :
    (1 / (24 * (192 : ℝ) ^ s)) * (k : ℝ) ^ s ≤ (cycleLengths G).card :=
  erdos752_from_moore mooreBound_proved G s k hs hk hdeg hgirth

theorem erdos_752 (s : ℕ) (hs : 1 ≤ s) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ,
      ∀ (V : Type u) [Fintype V] [DecidableEq V] [Nonempty V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
        k₀ ≤ k → (∀ v, k ≤ G.degree v) →
        (∀ v (p : G.Walk v v), p.IsCycle → 2 * s < p.length) →
        c * (k : ℝ) ^ s ≤ (cycleLengths G).card := by
  refine ⟨erdos752Constant s, erdos752Constant_pos s, 576, ?_⟩
  intro V _ _ _ G _ k hk hdeg hgirth
  exact erdos752_from_moore mooreBound_proved G s k hs hk hdeg hgirth

#print axioms erdos_752_nat
#print axioms erdos_752_explicit
#print axioms erdos_752
end JSP619
