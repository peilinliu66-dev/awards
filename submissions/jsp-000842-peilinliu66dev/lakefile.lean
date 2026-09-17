import Lake
open Lake DSL

package jsp000842

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib Proof where
  roots := #[`Proof, `JSP842, `JSP842Assembly, `JSP842Ore,
    `JSP842Arithmetic, `JSP842DenseSubset, `JSP842ClosedBound,
    `JSP842ThresholdBound, `JSP842Maximal, `JSP842CycleBridge]
