# Bounded prior-work and submission check

Checked on 2026-09-17 at 05:36:58 UTC. The public issues endpoint
returned 498 records through #499, including issues and pull requests.
Titles and bodies were searched for the exact JSP identifier, Erdős
number, and original problem URL. No matching record was found.
The snapshot summary and SHA-256 are in
`verification/official-search-summary.json`.

A single focused public GitHub code query for `"erdosproblems.com/1012"`
returned 25 results with `incomplete_results=false`. Eight returned Lean
files were inspected. The query and inspection summaries are preserved
in `verification/public-code-query.json` and
`verification/public-code-review.json`.

- Formal Conjectures mirrors in `ryantuck/erdos-ai`, paths
  `deepmind/deepmind/1012.lean` and `deepmind/deepmind-v2/1012.lean`,
  each contained four `sorry` proofs, including the principal endpoints.
- The main [lean-genius E1012 file](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos1012Problem.lean)
  had four custom axioms: `ore_theorem`, `bondy_theorem`,
  `woodall_pancyclic`, and `threshold_tight`; its terminal wrappers
  depend on those assumptions.
- That repository's OQ01 file also had four custom axioms; OQ02 assumed
  two vertex-pancyclic axioms. OQ04 and OQ01OQ02 supplied threshold
  arithmetic, rather than a full graph-existence proof; OQ01OQ02 imports
  OQ01. A further file concerned bipartite exceptions and had a `sorry`.

No inspected file supplied the complete graph-existence proof formalized
in this package. This is bounded public evidence, not global priority:
it excludes unindexed or differently named code, private work, and changes
after the checks. The cited related public formalization work is disclosed
without claiming exclusive authorship of the problem or proof method.

The mathematics is classical. This package requests Lean formalization
recognition for the explicit estimate f(k)=5k+5, not mathematical discovery
credit or a claim to the sharper known Woodall result. The catalog's
`Eligible to claim: No` remains subject to organizer assessment.
