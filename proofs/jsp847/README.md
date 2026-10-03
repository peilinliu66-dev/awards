# JSP-000847 / Erdős 1017: a uniform dense clique-partition saving

For every finite simple graph with `n` vertices and `e` edges, this project proves

```
5000 * cp(G) + e(G) <= 5001 * floor(n^2 / 4).
```

Here `cp(G)` is the minimum number of complete subgraphs in an **exact edge partition**. The proof also produces an actual partition with this bound. For `e > A = floor(n^2/4)`, it gives the explicit saving

```
cp(G) <= A - ceil((e-A)/5000).
```

This supplies a nontrivial sharpening for every positive edge surplus in Erdős’s [1971 question, printed page 101, item 11](https://www.renyi.hu/~p_erdos/1971-25.pdf). The bound applies to arbitrary finite vertex types, including the empty graph, with both parities and every density covered.

- Main proof: [Erdos1017/Final.lean](Erdos1017/Final.lean), `Erdos1017.exists_partition_dense_saving` and `Erdos1017.uniform_integer_dense_saving`.
- Exact partition and statement definitions: [Erdos1017/Definitions.lean](Erdos1017/Definitions.lean).
- Mathematical proof: [MATHEMATICS.md](MATHEMATICS.md).
- Scope and attribution: [SCOPE_AND_ATTRIBUTION.md](SCOPE_AND_ATTRIBUTION.md).
- Reproduction and audit: [VERIFICATION.md](VERIFICATION.md).

## Verified source version

On 2026-10-03, all **23 project modules** were freshly rebuilt with Lean **4.33.0** and the pinned Mathlib revision. The separate [Audit.lean](Audit.lean) check also exited successfully. The weighted foundation and both final endpoints depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The 24 Lean files and pinned project configuration published here are byte-identical to that verified source set. [SOURCE_SHA256SUMS.txt](SOURCE_SHA256SUMS.txt) binds the logs to the source bytes. Early development comments containing “UNCOMPILED” are historical comments retained to preserve those exact checked bytes; [the final verification report](VERIFICATION.md) and [logs](logs/) record the current successful result.

Lean formalization: [@peilinliu66-dev](https://github.com/peilinliu66-dev), with AI assistance. The mathematical foundations and adapted proof route are attributed explicitly in [SCOPE_AND_ATTRIBUTION.md](SCOPE_AND_ATTRIBUTION.md). Original formalization sources are provided under the [Apache 2.0 license](LICENSE).
