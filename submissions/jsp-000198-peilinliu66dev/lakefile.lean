import Lake
open Lake DSL

package jsp000198

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib EmptyPentagon
lean_lib Prize

@[default_target]
lean_lib Proof where
  roots := #[`FinalClassification, `JSP198NicolasCaseIAComplete, `JSP198NicolasCaseIASampledSupport, `JSP198NicolasSampledCapAssembly, `JSP198NicolasCaseIAOuterJoin, `JSP198NicolasCaseIAJoinCertificates, `JSP198NicolasCaseIAEndpointsB, `JSP198NicolasCaseIABCertificates, `JSP198NicolasCaseIAArcSupport, `JSP198NicolasCaseIAPropagation, `JSP198NicolasCaseIAChord, `JSP198NicolasCaseIAChordCertificate, `JSP198NicolasCaseIAEndpoint, `JSP198NicolasCaseIANinePoint, `JSP198NicolasCaseIASupport, `JSP198NicolasPartialCover, `JSP198NicolasPartialCoverAdapter, `JSP198NicolasPartialCoverOrder, `JSP198NicolasCaseICapacity, `JSP198NicolasCaseISampled, `JSP198NicolasCaseIArc, `Proof, `JSP198FiniteRamsey, `ESConvex, `ESSelection, `ES25, `JSP198NicolasLocal, `HexagonNormalization, `ModelBridge, `HortonBranch, `JSP198NicolasGlobal, `JSP198NicolasMatching, `JSP198NicolasSectorOrder, `JSP198NicolasCoherentCover, `JSP198NicolasRadialCoherence, `JSP198NicolasSweptOrder, `JSP198NicolasCaseICCover, `JSP198NicolasCaseIRuns, `JSP198NicolasOnePointGlue, `JSP198NicolasCaseIIBridge, `JSP198NicolasCaseIISelection, `JSP198NicolasCaseII, `JSP198NicolasCaseICGeometry, `JSP198NicolasCaseIC, `JSP198NicolasCaseIScopeBridge, `JSP198NicolasCaseIBSupport, `JSP198NicolasCaseIB, `FinalAssemblyAdapter]
