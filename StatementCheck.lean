import Erdos524.Main

/-! Independently spelled-out public endpoint specification; author self-check, not an independent verifier attestation. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

noncomputable def submittedSignMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ =>
    (1/2:ℝ≥0∞) • Measure.dirac (-1:ℝ)+(1/2:ℝ≥0∞) • Measure.dirac (1:ℝ))

noncomputable def submittedPolynomial (ω : ℕ → ℝ) (n : ℕ) : C(Set.Icc (-1:ℝ) 1,ℝ) :=
  ⟨fun x => ∑ k ∈ Finset.range (n+1), ω k*(x:ℝ)^k,by fun_prop⟩

/-- All coefficients, the entire closed interval, the original index convention,
    the two exact constants and the almost-sure quantifier are explicit here. -/
theorem submitted_original_statement :
    ∀ᵐ ω ∂submittedSignMeasure,
      (liminf (fun n : ℕ => Real.log (‖submittedPolynomial ω n‖/Real.sqrt (n:ℝ)) /
        (Real.log (Real.log (n:ℝ)))^(1/3:ℝ)) atTop=-(3*Real.pi^2/4)^(1/3:ℝ)) ∧
      (limsup (fun n : ℕ => ‖submittedPolynomial ω n‖/
        Real.sqrt ((n:ℝ)*Real.log (Real.log (n:ℝ)))) atTop=Real.sqrt 2) := by
  exact Erdos524.erdos_524

#print axioms submitted_original_statement
#check submitted_original_statement
