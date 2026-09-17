import Lake
open Lake DSL

package jsp000636

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib Erdos776

@[default_target]
lean_lib Proof where
  roots := #[`Proof, `JSP636UpperBound, `JSP636SmallParameters, `JSP636Maximum, `JSP636ExactThreshold, `JSP636]
