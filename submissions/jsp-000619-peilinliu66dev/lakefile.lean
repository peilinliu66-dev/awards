import Lake
open Lake DSL

package jsp000619

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib Proof where
  roots := #[`Proof, `JSP619Moore, `JSP619ExpansionPath, `JSP619LocalExpansion, `JSP619CycleSplice, `JSP619Basic, `JSP619CycleCore, `JSP619Layers, `JSP619Bands, `JSP619Components, `JSP619Expansion, `JSP619CycleExtraction, `JSP619Assembly, `JSP619]
