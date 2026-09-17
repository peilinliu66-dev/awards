# Proof guide: empty convex polygon thresholds

All branches below are implemented and the unconditional original-model endpoints have passed the independent package build.

## 1. Statement and geometric model

For integers k>=3 and N>=0, let F(N,k) mean that every finite general-position point set P in the real plane with |P|>=N contains k points V in convex position with no point of P outside V in the interior of conv(V). This is the actual predicate `Prize.Geometry.ForcesEmptyKGon N k`.

The final statement is

\[
F(N,3)\iff N\ge3,\quad
F(N,4)\iff N\ge5,\quad
F(N,5)\iff N\ge10,
\]

an actual least g6 with

\[
g6\le B,\qquad F(N,6)\iff N\ge g6,
\]

and, for every k>=7 and every N, an N-point general-position set with no empty convex k-gon. Here B=`Horton.es25Bound` is the finite Ramsey bound defined below.

The reused small-polygon library uses an orientation-based general-position predicate and exactly-N forcing. `ModelBridge` proves equivalence with the collinearity-based predicate and the at-least-N model. The cardinality bridge uses the proved operation of deleting convex-hull vertices: restricting to an arbitrary subset would not preserve emptiness relative to the original ambient set.

## 2. Reused complete branches

The exact triangle and quadrilateral thresholds, and Harborth's exact pentagon threshold, are supplied by the [fixed PR283 formalization](https://github.com/CollinYuanjieRen/awards/tree/b8bb4f7803f921a7970abc880291ad9372111360/submissions/jsp-000198-smallk-cyr). Its proofs include the forcing bounds and the smaller counterexamples. The local development ports and imports these proofs rather than claiming them as newly written mathematics or Lean code.

For k>=7, the [fixed Horton formalization](https://github.com/tester-lean/jsp-000198-horton-lean/tree/313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0) constructs exactly N integer-coordinate points in general position for every N and proves the absence of an empty convex k-gon. This gives the complete infinite branch, not a finite search or a counterexample at one cardinality.

The remaining discussion concerns the added six-gon route, following [Nicolás, *The Empty Hexagon Theorem*](https://doi.org/10.1007/s00454-007-1343-6), with a classical Erdős–Szekeres prerequisite.

## 3. A proved finite convex-25 bound

Define

\[
T(0)=0,\qquad T(t+1)=2^{2T(t)},\qquad B=T(50).
\]

`JSP198FiniteRamsey` proves the finite ordered-triple Ramsey statement used at this bound. Color each increasing triple of distinct points by the sign of its orientation. General position rules out zero. The selection theorem supplies 25 points whose increasing triples have one common strict sign.

`ESConvex` proves that either common sign forces convex independence. In the positive case, the cyclic-neighbor orientations supply a supporting affine functional for each vertex, strictly separating it from the convex hull of the others. Reversing the order treats the negative case. `ES25` combines these results to prove that every general-position set of cardinality at least B contains 25 points in convex position.

There is no Ramsey or Erdős–Szekeres hypothesis left in `Horton.exists_convex25_at_bound`. B is a formal finite natural number and is not evaluated.

## 4. Safe reduction to a minimal outer polygon

Starting with a convex 25-point subset, the finite minimality argument chooses a convex 25-point set S with the proved `MinimalConvex` property. Set

\[
Q=P\cap\operatorname{conv}(S),
\]

implemented as `hullCut P S`. The hull vertices of Q are exactly S, Q remains in general position, and `MinimalOuter Q` holds. The minimality property controls every competing convex subset inside this hull, not only a chosen local replacement.

The source also proves that an empty polygon relative to Q is empty relative to P. Consequently a putative hexagon-free P with |P|>=B yields a hexagon-free Q with a minimal outer layer of exactly 25 vertices. This is `hexagon_free_minimal25_reduction`.

Write `inner Q` for Q with its hull vertices removed and iterate this operation to obtain the convex layers.

## 5. Verified Nicolás geometry and reductions

The local modules prove the geometric constructions used in the layer argument: replacement counting from minimality, supporting caps, empty triangles with a specified base, three-plus-three and four-plus-two empty-hexagon gluing, and transport between the inner and original configurations. The global modules construct actual directed boundary cycles and radial sectors, prove their coverage and uniqueness properties, and establish the required finite cell-count bounds.

If the third iterated inner set is empty, `hasEmptySix_of_three_layers` closes the argument for an outer layer of at least 25 vertices. Otherwise choose an actual point o in that iterated inner set. The remaining argument uses the second-layer boundary cycle and sectors defined by actual third-layer edges about o.

The Case II proof and its scope bridge give an empty hexagon or an `ActualCaseIRun` R. Its vertices follow the real boundary successor from a vertex that cannot match left to the first vertex that cannot match right; preceding vertices match right. Every sector used by this run has a singleton fiber in the whole second layer. Vertices outside the run remain unrestricted.

Writing m for the second-layer cardinality and l for `R.length`, the verified reductions handle:

| Range | Geometric conclusion |
|---|---|
| l+1=m | I.C is proved; a full separated run yields the sector distinctness needed to invoke it. |
| l+2=m | I.B is proved from singleton fibers on the run. |
| l+3<=m | I.A is proved by the sampled replacement and partial-cap contradiction below. |

In I.B exactly one vertex lies outside the run. This fact derives global sector injectivity within that branch. The left-match alternative constructs a genuine coherent cover and excludes the tight count by a proved convex insertion lemma. The other alternative constructs an actual full run and applies I.C. Neither alternative assumes the cover or insertion conclusion.

## 6. Complete I.A: actual sampled replacement

Let k be the length of the actual short run, A its second-layer predecessor and B its successor. Write a_j,b_j for the endpoints of the actual third-layer sector edge assigned to run vertex j. Only sectors on the run have singleton fibers; vertices outside the run may share sectors.

`exists_actual_caseIArc` constructs a genuine clockwise third-layer boundary cycle with strictly increasing selected indices and no wraparound before the last selected endpoint. The sampled replacement is

    T = {A,a_0,...,a_k,b_k,B}.

The arc and the short-run bound prove that these k+4 points are distinct and lie in the inner set. The proof uses the sampled set, not all intermediate third-layer vertices.

The endpoint modules derive their determinant signs from the actual run, the actual boundary edges, the radial sectors, general position, and the no-left/no-right stopping conditions. Explicit finite sign certificates prove the cross-end supports; every identity is checked by `ring` and every sign step by ordered-field reasoning. Repeated nonessential labels, including b_0=a_k, are allowed. No SAT answer is imported as a theorem.

The proved convex-arc propagation and actual cyclic order extend these supports to every edge of the sampled chain. `caseIA_sampled_edge_support` proves that each of A->a_0, a_j->a_(j+1), a_k->b_k and b_k->B supports all of T in its closed right half-plane. This statement has no extra point-support hypothesis.

Define D to be the outer hull vertices strictly on the positive side of at least one of these sampled edges. The partial-cover proof establishes

    D ⊆ first endpoint fan ∪ (union of the k right channels) ∪ last endpoint fan.

It constructs the genuine join triangles and uses viewing ranks to propagate a visible edge forward or backward along the finite run. Shared-endpoint joins are included. This is a partial-chain cover, not an assumed cover or a substituted whole-cycle cover.

If there is no empty hexagon, the two endpoint fans each have at most two points and each right channel at most one. Consequently |D|<=k+4.

For every point of T, an incident sampled edge supports T. Outside D the same edge has negative orientation, by the definition of D and general position. The previously proved `replacement_card_lt` therefore applies to T and D in the actual minimal outer configuration, giving

    k+4 = |T| < |D|.

This contradicts the cover bound. `hasEmptySix_of_caseIA_run` proves I.A with exactly the actual run, its local singleton condition and k+3<=|C2|. `remainingCaseIACore` discharges its universal closure.

## 7. Unconditional original-model assembly

The actual-run reduction is now closed in every case. Combining the four-layer theorem with the three-layer theorem and safe normalization gives an empty hexagon whenever |P|>=B.

The at-least-N forcing predicate is monotone in N. Well-ordering applied to the proved bound gives a genuine least g6<=B and, for every N, F(N,6) iff g6<=N. No numerical value such as g6=30 is inferred.

`erdos216_classification` combines this with the exact small values and all Horton counterexamples. `finite_threshold_iff` states, for every k>=3, (there exists N with F(N,k)) iff k<=6. The printed unconditional endpoint reports contain only the three standard logical axioms. The complete development is a formalization and integration of known mathematics.
