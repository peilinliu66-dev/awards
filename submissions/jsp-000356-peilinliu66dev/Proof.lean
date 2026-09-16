import JSP356Asymptotic
import JSP356UpperBridge

/-!
Complete original-question lower bound and accompanying density-zero upper
bound for Erdős problem 437 / JSP-000356. The mathematical answer is known;
this package supplies a Lean formalization with explicit sequence semantics.
-/

namespace JSP356

theorem erdos_437 : OriginalLowerQuestion ∧ DensityZeroUpperQuestion :=
  ⟨original_lower_question, densityZeroUpperQuestion⟩

end JSP356

#print axioms JSP356.erdos_437
#print axioms JSP356.erdos_437_real
