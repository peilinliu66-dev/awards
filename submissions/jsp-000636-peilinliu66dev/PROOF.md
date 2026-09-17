# Proof guide: the complete strict threshold for Erdős 776

**Build status: PASS.** The full all-parameter theorem, all 11 native finite-table groups, and the independent package build passed locally. The exact final trust boundary and reproduction records are recorded in [README.md](README.md).

The small-parameter mathematics and universal bound follow [He and Tang, arXiv:2602.09803v2](https://arxiv.org/html/2602.09803v2). The complete \(r\ge4\) proof is reused from [mthiim's fixed development](https://github.com/mthiim/erdos_776/tree/1ca43203123642edaac45bf00b6fc333c848b4c9). The contribution here is the Lean extension and connection of these results, not a claim of a new mathematical solution.

## 1. The actual maximum and the strict cutoff

An admissible family is an antichain \(\mathcal F\subseteq2^{[n]}\) such that every occupied size has at least \(r\) members. Its occupied levels are

\[
L(\mathcal F)=\{|A|:A\in\mathcal F\},\qquad
g(n,r)=\max_{\mathcal F}|L(\mathcal F)|.
\]

The set of attainable level counts is finite and nonempty: the empty family is admissible and attains zero. `JSP636.g` takes its finite maximum and is proved equal to the upstream `Erdos776.Uniform.extremalOccupiedLevels`.

`OptimalLevels n r k` combines existence of an admissible family with \(k\) occupied levels and an upper bound of \(k\) for every admissible family. It is equivalent to \(g(n,r)=k\). The intended theorem, for every \(r\ge2\) and \(N\in\mathbb N\), is

\[
(\forall n>N,\ g(n,r)=n-3)\ \Longleftrightarrow\ b(r)\le N,
\qquad
b(r)=
\begin{cases}
3&r=2,\\
8&r=3,\\
2r+4&4\le r\le10,\\
2r+5&r\ge11.
\end{cases}
\]

The strict inequality preserves the original cutoff convention. The upstream existence-only interfaces are left intact; they are not used to define the maximum-based \(r=2\) threshold.

## 2. The uniform upper bound

For \(r\ge2\) and \(n\ge4\), every admissible family satisfies \(|L(\mathcal F)|\le n-3\). It suffices to lower the multiplicity requirement to two. Sizes zero and \(n\) cannot occur because each contains only one possible set.

Suppose singletons occur. Let \(X\) consist of their elements, so \(|X|\ge2\). Antichainness forces every nonsingleton member to lie in \(U=[n]\setminus X\), with \(|U|\le n-2\). A member of size \(n-2\), if present, would have to equal \(U\). There could therefore be at most one such member, contradicting multiplicity two. All occupied sizes lie in \(1,\ldots,n-3\).

If size \(n-1\) occurs, pass to complements: admissibility and the number of occupied levels are preserved, and the previous case applies. If neither extreme size occurs, all occupied sizes lie in \(2,\ldots,n-2\), again only \(n-3\) possibilities.

The source proves and later uses the stronger singleton bound: if \(r\ge2\), \(n\ge r+2\), and size one occurs, then

\[
L(\mathcal F)\subseteq\{1,\ldots,n-r-1\}.
\]

The same argument has \(|X|\ge r\); size \(n-r\) cannot have \(r\) distinct members. This strengthening handles the outer levels in the \((n,r)=(8,3)\) obstruction.

## 3. Finite profile checks produce actual antichains

The inherited `profile_criterion` and its Boolean-check soundness theorems are proved in the upstream Lean dependency chain. They are not additional assumptions of the final theorem.

Let \(\partial_k(m)\) be the Kruskal–Katona minimum lower-shadow size of \(m\) distinct \(k\)-sets, computed by the canonical binomial expansion. For an exact constant profile \(r\) on levels \(2,\ldots,n-2\), set

\[
m_{n-2}=r,\qquad m_i=r+\partial_{i+1}(m_{i+1}).
\]

Necessity follows by counting the disjoint contributions of the chosen level and the shadows forced by higher levels. Hence the cumulative requirements must fit the capacities \(m_i\le\binom ni\). For sufficiency, take the initial colex segment \(C_i\) of size \(m_i\) and choose \(C_i\setminus\partial C_{i+1}\). The colex-shadow properties proved in the core give exactly \(r\) members on each specified level and exclude containment between different chosen levels. The result is an actual finite antichain.

`JSP636SmallParameters` verifies the finite checks for

\[
(r,n)=(2,4),\ldots,(2,12),\quad (3,9),\ldots,(3,12),
\]

and invokes this proved construction theorem. These 13 checks use ordinary kernel-checked `decide`; no externally supplied table is assumed. For every \(n\ge13\), the upstream \(r=4\) theorem supplies a family with \(n-3\) occupied levels and at least four members on each. The same family satisfies either smaller multiplicity requirement. This covers the entire infinite success ranges \(r=2,n\ge4\) and \(r=3,n\ge9\). Section 2 upgrades existence to equality with the maximum.

## 4. The last failure for multiplicity two

On three points, two distinct singletons give an admissible family with one occupied level. An admissible family cannot occupy both sizes one and two: with two distinct singleton members, any two-element set contains at least one of them. Sizes zero and three are impossible. Consequently

\[
g(3,2)=1\ne0=3-3.
\]

Every proposed cutoff below three therefore fails at \(n=3\); all \(n>3\) succeed by Section 3. Thus the least strict cutoff is three. Mere existence of a zero-level family at \(n=3\) would not prove the required maximum statement.

## 5. The last failure for multiplicity three

Consider an admissible family on eight points. If size one or seven occurs, the strengthened singleton estimate, applied directly or after taking complements, bounds the number of occupied levels by four.

Otherwise, a family with five occupied levels would have to occupy every size \(2,3,4,5,6\), with at least three members per level. The necessary cumulative profile is

| Level \(i\) | 6 | 5 | 4 | 3 | 2 |
|---|---:|---:|---:|---:|---:|
| Required \(m_i\) | 3 | 18 | 37 | 43 | 29 |

Indeed, the successive shadow values are

\[
\partial_6(3)=15,\quad\partial_5(18)=34,\quad
\partial_4(37)=40,\quad\partial_3(43)=26.
\]

For example, the canonical expansions

\[
18=\binom65+\binom54+\binom43+\binom32,\quad
37=\binom74+\binom33+\binom22,\quad
43=\binom73+\binom42+\binom21
\]

give the stated shadow values. The final requirement \(m_2=29\) exceeds \(\binom82=28\). This contradicts the proved profile necessity theorem. In Lean, the closed arithmetic check is connected to `constantProfileLevelTwoOverflowCheck_sound`; the argument does not enumerate all possible families.

Thus \(g(8,3)\le4<5\), whereas every \(n>8\) succeeds by Section 3. The least strict cutoff is eight.

## 6. Reusing the complete large-parameter proof

The fixed upstream theorem

```lean
Erdos776.Uniform.erdos776_lastFailure (r : ℕ) (hr : 4 ≤ r)
```

provides nonexistence at \(b(r)\) and existence for every \(n>b(r)\), with the two formulas for \(4\le r\le10\) and \(r\ge11\). Its development includes colex/shadow machinery, the profile criterion, constructions, obstructions, and the symbolic large-parameter argument. This substantial proof is reused with its attribution and license, rather than represented as new work in this package.

The original finite certificates for \(4\le r\le10\) and \(11\le r\le28\) have been replaced by kernel-checked proofs. The remaining finite lower-window check is exactly

```lean
(List.range 349).all (fun d => lowerWindowCheck (29 + d)) = true
```

covering \(29\le r\le377\). It is verified in 11 native groups starting at

```text
29, 61, 93, 125, 157, 189, 221, 253, 285, 317, 349
```

The first ten groups have 32 values and the last has 29. Ordinary Lean range arguments combine them into the original Boolean formula without changing its meaning. The infinite range \(r\ge378\) remains covered by the upstream symbolic proof, not a finite extrapolation.

All 11 groups have passed locally, but they use `native_decide`. In Lean 4.33.1 each contributes a generated native-evaluation axiom, for example `Erdos776.Uniform.lowerWindowNative285_certificate._native.native_decide.ax_1_1`. The assembled result was checked to depend on the standard three axioms and these 11 generated axioms; the [actual report](verification/terminal-axioms.log) records all three final endpoints. The native evaluator is therefore an explicitly disclosed trust component. An isolated successful pure-kernel \(r=377\) probe is not used as a substitute for the full table.

## 7. All cutoffs and exact multiplicity

For \(r\ge4\), combine upstream existence with Section 2 to obtain actual optimality at every \(n>b(r)\). Upstream nonexistence at \(b(r)\) rules out optimality there. Together with Sections 4–5, this proves for every \(r\ge2\):

\[
g(b(r),r)\ne b(r)-3,\qquad
\forall n>b(r),\quad g(n,r)=n-3.
\]

If \(N<b(r)\), the point \(n=b(r)\) refutes the assertion that every \(n>N\) succeeds. If \(b(r)\le N\), every \(n>N\) is above \(b(r)\), so succeeds. This proves the stated equivalence for all candidate cutoffs and the uniqueness of the least cutoff.

Finally, from every occupied level of an at-least-\(r\) family, choose \(r\) members and take their finite union \(\mathcal E\). It remains an antichain because \(\mathcal E\subseteq\mathcal F\). Different levels have different set sizes, so each new level contains exactly its chosen members. Since \(r>0\), all original occupied levels survive, and no new levels appear. Thus exact and at-least multiplicity have identical attainable level counts and identical maxima. `exists_exact_subfamily` and `exact_attainability_iff` formalize this construction; `erdos776_original_exact_multiplicity` transports the full strict-cutoff theorem to the original convention.

The final endpoint signatures contain no assumed construction, obstruction, or threshold conclusion. Their assembled compilation and independent package verification both passed; see the [local build record](verification/local-build.json).
