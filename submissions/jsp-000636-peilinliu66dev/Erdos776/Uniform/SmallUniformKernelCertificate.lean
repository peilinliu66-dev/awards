import Erdos776.Uniform.FiniteProfileChecker

/-! Kernel-checked finite certificate extracted unchanged from the upstream
finite uniform certificate. MIT: mthiim and contributors (2026). -/

namespace Erdos776.Uniform

/-- One finite computation certifying upper-core data and obstruction for 18 values. -/
def smallUniformFiniteCheck : Bool :=
  (List.range 18).all fun d =>
    upperCoreCheck (11 + d) && fullProfileOverflowCheck (11 + d)

theorem smallUniformFiniteCheck_verified :
    smallUniformFiniteCheck = true := by
  set_option maxRecDepth 100000 in
    decide +kernel

end Erdos776.Uniform

#print axioms Erdos776.Uniform.smallUniformFiniteCheck_verified
