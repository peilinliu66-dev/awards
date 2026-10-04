import Erdos524.RandomPolynomialBlocks
import Erdos524.RandomPolynomialSplit
import Erdos524.FactorialBlockProbability
import Erdos524.InversePolynomialScale

/-! Actual independent sparse blocks, conditional only on the displayed full-polynomial probability budget. -/

namespace Erdos524.SparseBlockBorelCantelli

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
open Erdos524.RandomPolynomialModel Erdos524.FactorialSparseMesh
open Erdos524.InversePolynomialScale Erdos524.EnvelopeBlocking

noncomputable def lowerBudget (c a D : ℝ) (N : ℕ) : ℝ :=
  Real.exp (c * Real.sqrt (Real.log (Real.log (N : ℝ)))) / Real.log (N : ℝ) -
    D * Real.exp (-a * Real.log (N : ℝ))

theorem ae_frequent_fresh_small_of_budget
    {c a D q : ℝ} (hc : 0 < c) (ha : 0 < a) (hD : 0 ≤ D)
    (hprob : ∀ᶠ N : ℕ in atTop, Even N →
      lowerBudget c a D N ≤ P.real {ω | fullNorm ω N ≤ q * normalizer (N : ℝ)}) :
    ∀ᵐ ω ∂P, ∃ᶠ j in atTop,
      freshNorm (endpoint j) (blockLength j) ω ≤ q * normalizer (blockLength j : ℝ) := by
  let E := fun j ↦ {ω | freshNorm (endpoint j) (blockLength j) ω ≤ q * normalizer (blockLength j : ℝ)}
  have hmeas : ∀ j, MeasurableSet (E j) := fun j ↦
    measurableSet_le (measurable_freshNorm _ _) measurable_const
  have hdiv : ∑' j, P (E j) = ⊤ := by
    apply tsum_eq_top_of_eventual_harmonic
    filter_upwards [blockLength_tendsto_atTop.eventually hprob,
      eventually_factorial_harmonic_budget hc ha hD] with j hp hj
    have hp := hp (blockLength_even j)
    have hre : P.real (E j) = P.real {ω | fullNorm ω (blockLength j) ≤ q * normalizer (blockLength j : ℝ)} := by
      unfold Measure.real E
      rw [freshNorm_event_law]
    apply (ENNReal.ofReal_le_iff_le_toReal (by finiteness : P (E j) ≠ ⊤)).mpr
    change 1 / (j + 2 : ℝ) ≤ P.real (E j)
    rw [hre]
    exact hj.trans hp
  exact ae_frequently_of_independent hmeas (factorial_fresh_events_independent _) hdiv

theorem ae_frequent_full_small_of_budget_and_old
    {c a D q Q : ℝ} (hc : 0 < c) (ha : 0 < a) (hD : 0 ≤ D)
    (hprob : ∀ᶠ N : ℕ in atTop, Even N →
      lowerBudget c a D N ≤ P.real {ω | fullNorm ω N ≤ q * normalizer (N : ℝ)})
    (v : ℕ → ℝ)
    (hold : ∀ᵐ ω ∂P, ∀ᶠ j in atTop, fullNorm ω (endpoint j) ≤ v j)
    (hscale : ∀ᶠ j in atTop,
      q * normalizer (blockLength j : ℝ) + v j ≤ Q * normalizer (endpoint (j + 1) : ℝ)) :
    ∀ᵐ ω ∂P, ∃ᶠ N in atTop, fullNorm ω N ≤ Q * normalizer (N : ℝ) := by
  filter_upwards [ae_frequent_fresh_small_of_budget hc ha hD hprob, hold] with ω hf ho
  have hg : ∃ᶠ j in atTop, fullNorm ω (endpoint (j + 1)) ≤ Q * normalizer (endpoint (j + 1) : ℝ) := by
    apply ((hf.and_eventually ho).and_eventually hscale).mono
    intro j hj
    have hs := fullNorm_add_le ω (endpoint j) (blockLength j)
    have he : endpoint j + blockLength j = endpoint (j + 1) :=
      Nat.add_sub_of_le (endpoint_strictMono.monotone (Nat.le_succ j))
    rw [he] at hs
    linarith [hj.1.1, hj.1.2, hj.2]
  apply frequently_atTop.2
  intro N
  obtain ⟨j, hjN, hj⟩ := frequently_atTop.1 hg N
  exact ⟨endpoint (j + 1), hjN.trans ((Nat.le_succ j).trans (endpoint_strictMono.id_le _)), hj⟩

end Erdos524.SparseBlockBorelCantelli
