# Third-party source attribution

The files `Erdos131Research/Upstream/ConvexHausdorff.lean` and
`Erdos131Research/Upstream/ConvexSupport.lean` reproduce the corresponding
generic lemmas from deancureton/MovingSofa at commit
`4d5569131940815f47a9ccf3e90a4c5043c56127`.

`Erdos131Research/ConvexBodyLimits.lean` adapts the compactness and volume
continuity arguments in `MovingSofa/Convex/Limits.lean` from the same commit
to arbitrary finite dimension and to the coordinate convention of the
non-dividing-set project. The original repository is licensed Apache 2.0;
the license is reproduced in `MovingSofa-LICENSE.txt`.

Source: https://github.com/deancureton/MovingSofa/tree/4d5569131940815f47a9ccf3e90a4c5043c56127

These adaptations are included in the complete compiled and audited endpoint; see BUILD_REPORT.json.

`Erdos131Research/Upstream/NormalizedDifference.lean` extracts only generic
normalization lemmas from the Apache-2.0 files `PZ/OneStepAssembly.lean` and
`PZ/FiniteHullDeterminant.lean` in plby/lean-proofs at commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. Their copyright/license/author
notice is retained. Namespaces and imports are adapted to avoid an unused
dependency on the non-averaging descent assembly.
