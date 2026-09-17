import Lake
open Lake DSL

package jsp000656

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib Proof where
  roots := #[`Proof, `JSP656, `JSP656Random, `JSP656ChoiceNumber, `JSP656ListColoring]
