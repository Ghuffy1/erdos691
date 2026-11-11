# Verification report

**Overall verdict — verification passed for the complete arithmetic criterion.**

The selected proof commit is **4d44c64d562f1b15cae4c93037d54f064a935873** in **Ghuffy1/erdos691**, branch **main**. The full ordinary-density criterion for every set A passed a clean build, explicit source checks, fifteen axiom audits, module kernel checks, and fresh-environment replay in private hosted Ubuntu CI. A separate native-Windows run checked commit `87514692c7a814ea3f500eb72bfba45da8a2bf54`. All seven proof, configuration and verification-script hashes agree between the two runs.

## Required judgments

| Question | Judgment | Evidence |
| --- | --- | --- |
| Does the proof address the original question? | Yes, through the proposed full arithmetic criterion | Arbitrary A, ordinary density of positive multiples, an A-independent family class, and both implications are checked in the statement bridge. |
| Did the selected proof commit pass verification? | Yes | The private CI run checked `4d44c64d562f1b15cae4c93037d54f064a935873` and every recorded command returned 0. |
| Is the criterion fully proved? | Yes | The avoiding-family construction and the positive-survival converse are both present, for all required inputs. |
| Does the formalization meet Lean completeness requirements? | Meets | All fifteen declarations use only `propext`, `Classical.choice`, and `Quot.sound`. |

These judgments concern the theorem and its formalization. The proposed structural answer remains subject to the organizers' mathematical and scope review. Novelty and first priority remain unestablished.

## Original source and correspondence

The original question is Erdős 691, P. Erdős, *Some unconventional problems in number theory* (1979), printed p. 77. Its prize entry is JSP-000563. [Original paper](https://www.numdam.org/article/AST_1979__61__73_0.pdf)

The main theorem is `Erdos691.Adaptive.erdos691`. `HasMultiplesDensityOne` counts positive multiples and takes their ordinary natural density. `AdmissibleTest` has no A parameter. Its fields specify finite positive divisor-closed levels, root {1}, strictly increasing prime cutoffs, support, projection compatibility, and a reciprocal-mass bound for every parent. `MeetsEveryTest` requires an intersection with every such family.

`Erdos691Audit.original_statement_verified` expands the density and every family condition separately from the structure. `exact_fiber_characterization` checks that the quotient-image fiber is precisely the intended multiplier fiber. Zero is excluded from the counted integers and divisors. Empty and finite sets, the divisor 1, unbounded exponents, and arbitrary infinite sets are included. The indexing difference between the manuscript and code is detailed in [SCOPE.md](../submission/SCOPE.md). The complete requirement mapping is in [coverage.json](coverage.json).

The proof uses the formalized classical Davenport–Erdős transfer, the geometric prime-valuation model, conditional survival, finite weighted pruning and divisor closure, and an infinite inductive construction. The reverse implication uses positive survival through all levels. The manuscript presents the same criterion and proof. Its six-page PDF has SHA256 `a122c99e018d44c2cb7e6f8582f87abe0d38554eaed215100f634e2547789ddd`.

## Exact versions and execution

| Item | Recorded value |
| --- | --- |
| Lean | 4.34.0, compiler revision shown in the version logs |
| Mathlib | 5ed2965256430c3649e86755f9576b54eca72435 |
| Other dependencies | Eight further revisions, checked before and after each run against lake-manifest.json |
| Selected source | 4d44c64d562f1b15cae4c93037d54f064a935873 |
| Main source SHA256 | 2a1ebd41e7b532deae42ee0f27e5c9d93dd9b04a2bb554a16f7e1d8b8865718d |
| Windows | Windows-10-10.0.19045-SP0, separate clean source checkout, native execution |
| Ubuntu CI | Linux-7.0.0-1017-azure-x86_64-with-glibc2.39, GitHub-hosted isolated runner |
| CI run | [42966106312](https://github.com/Ghuffy1/erdos691/actions/runs/42966106312), completed successfully |
| Checkout action | v7.0.1, pinned by full SHA |
| Toolchain bootstrap | Elan v4.2.4, downloaded artifact SHA256 verified |
| Dependency objects | Official pinned Mathlib caches, actual Git revisions and tracked-source cleanliness checked |
| Input stability | Source and configuration hashes unchanged in both runs |

The native run used a fresh source checkout and a separate copy of the trusted dependency cache. Local Docker isolation was unavailable. The hosted Linux run used a fresh ephemeral runner, independently fetched dependencies, read-only repository permission, and checkout credential persistence disabled. Its successful execution supplies the separate machine and OS check. The source checker and kernel replayer both use Lean's kernel. An independently implemented kernel and external human mathematical review remain pending.

## Actual command results

All durations are seconds. The default build included Erdos691, Challenge and Audit. Each module was then explicitly built and its source checked.

| Check | Windows | Ubuntu CI | Exit codes |
| --- | --- | --- | --- |
| lean-version | 11.828 | 0.816 | 0 / 0 |
| lake-version | 0.625 | 0.064 | 0 / 0 |
| default-build | 327.984 | 38.651 | 0 / 0 |
| build-Erdos691 | 5.547 | 5.130 | 0 / 0 |
| check-Erdos691 | 37.922 | 21.748 | 0 / 0 |
| build-Challenge | 5.297 | 1.770 | 0 / 0 |
| check-Challenge | 14.375 | 2.874 | 0 / 0 |
| build-Audit | 5.109 | 1.769 | 0 / 0 |
| check-Audit | 16.047 | 2.673 | 0 / 0 |
| kernel-Erdos691 | 37.063 | 7.038 | 0 / 0 |
| kernel-Challenge | 41.578 | 6.077 | 0 / 0 |
| kernel-fresh-Challenge | 1276.078 | 434.002 | 0 / 0 |

The full-environment replay checked the submitted theorem and expanded statement bridge together with their imported safe declarations. Its successful completion is recorded in each platform's kernel-fresh-Challenge.log. [Windows result](windows/result.json), [Ubuntu result](linux/result.json)

## Axioms and static checks

Every one of the fifteen declarations in Audit.lean reports exactly the three standard Lean foundations. The complete outputs are preserved in each platform's check-Audit.log. The targets include the two implications, main theorem, full-solution wrapper, arithmetic fiber bridge, original statement bridge, and principal probability and construction lemmas.

A separate lexical review of the three proof and audit source files found no placeholder proofs, newly introduced axioms, unsafe declarations, native evaluation, environment initialization, or custom elaborators. Static review supplements the transitive axiom checks and kernel replay. [Static review](static-review.json)

The optional prize audit helper's preflight passed on the Windows source revision. Its recorded result is retained in [preflight.json](preflight.json). The actual builds, declaration checks, and replays were executed by the supplied reproducible script. The evidence states the methods and levels actually completed.

## Attribution, licensing and remaining review

The four team contributors receive equal credit, with Ghuffy1 as owner and coordinator. Names are alphabetized by surname in the manuscript. Contributions, AI assistance, and the adapted classical source are recorded in AUTHORS.md and THIRD_PARTY_NOTICES.md. The upstream file's Apache 2.0 declaration is preserved, accompanied by the license and modification NOTICE. The code is prepared under Apache 2.0 and the manuscript and original documentation under CC BY 4.0.

The full-text comparisons with the identified Hall book sections, Hall's 1990 chapter, and Hill's dissertation remain incomplete. These checks and the related closed PRs are recorded in submission/RELATED_WORK.md. The repository makes no verified first-priority claim. The organizers must complete their mathematical review, contributor and identity checks, and award process. Every claimant personally confirms their own claim.

The repository remains private. This report records completed verification and preserves the user-controlled public-release decision.
