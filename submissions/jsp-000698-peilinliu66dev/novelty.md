# Bounded prior-work and submission check

Checked on 2026-09-17 at approximately 04:55 UTC.

The public GitHub issues endpoint for TheJustinSunPrize/awards, paginated
with state=all, returned 478 records through #479, including Issues and
pull requests. Titles and bodies were searched for JSP-000698, Erdős 842,
the original erdosproblems.com/842 URL, and cycle/triangle keywords.
No exact identifier or URL match was found. Three broader topic hits were
inspected: [#418](https://github.com/TheJustinSunPrize/awards/pull/418)
concerns a triangle/four-cycle-free extremal construction, while
[#462](https://github.com/TheJustinSunPrize/awards/pull/462) and
[#463](https://github.com/TheJustinSunPrize/awards/issues/463) concern an
odd-cycle/triangle Ramsey comparison. They do not address this problem.

One focused GitHub code API query, `"erdosproblems.com/842" language:Lean`,
returned total_count=0 and incomplete_results=false. The returned API
summary is preserved as `verification/public-code-query.json`.

This is a bounded public search. It does not cover every comment,
unindexed or differently named code, private work, or submissions made
after the snapshot. It did not identify an earlier complete public Lean
formalization and does not prove global priority.

The mathematics is known: Fleischner–Stiebitz (1992) proved the theorem,
and the proof route follows Petrov's 2015 finite parity and polynomial
argument. Source references and the exact formal statement are in the
[README](README.md). The claimed contribution is this Lean formalization.

The checked catalog says Solved; Lean proof: No; Eligible to claim: No.
Formalization recognition and eligibility require organizer review; no
award or payment is asserted by this package.
