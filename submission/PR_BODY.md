## Submission type

- [x] Mathematical solver information
- [x] Lean proof or formalization author information

This combined submission presents a complete arithmetic criterion for the density-one property and its formal proof. The upstream file-level Apache 2.0 declaration is preserved with its full license and modification notice. The statement, mathematical solution and contribution attribution are submitted for the organizers’ review.

## Problem

- Problem ID is **JSP-000563**, corresponding to **Erdős problem 691**.
- The original question is on printed p. 77 of P. Erdős, *Some unconventional problems in number theory*, Astérisque 61 (1979), 73–82. [Primary source](https://www.numdam.org/article/AST_1979__61__73_0.pdf)
- The proposed change records the full necessary-and-sufficient criterion and its complete Lean formalization in the existing catalog entry. The organizers retain control of eligibility, claim statuses, and award records.
- The proof manuscript is *A divisor-closed criterion for Behrend sequences*, November 11, 2026, Theorem 1.1 and Definition 1.2, pp. 1–2, with proofs on pp. 3–6. [Pinned manuscript](https://github.com/Ghuffy1/erdos691/blob/87514692c7a814ea3f500eb72bfba45da8a2bf54/paper/proof.pdf)
- Related closed PRs are 3697, 3795, 4295, and 4507. Their scope and source limitations are recorded in [Related work](https://github.com/Ghuffy1/erdos691/blob/87514692c7a814ea3f500eb72bfba45da8a2bf54/submission/RELATED_WORK.md). The present target is the universal arithmetic criterion for every set A.

## Formal statement

- The complete mathematical solution is supplied by the manuscript linked above.
- Mathematical review is requested. Organizer acceptance and external human review are pending.
- The statement is proposed for review against the original open-ended question. It has no claimed prior maintainer approval.
- The target is `Erdos691.Adaptive.erdos691 (A : Set ℕ)`, proving `HasMultiplesDensityOne A ↔ MeetsEveryTest A`. [Statement and proof](https://github.com/Ghuffy1/erdos691/blob/87514692c7a814ea3f500eb72bfba45da8a2bf54/Erdos691.lean#L5748)
- The expanded bridge is `Erdos691Audit.original_statement_verified`. [Expanded statement](https://github.com/Ghuffy1/erdos691/blob/87514692c7a814ea3f500eb72bfba45da8a2bf54/Challenge.lean)
- A is arbitrary. Multiples and divisors are positive. Density is ordinary natural density. The test class is independent of A and imposes finite divisor-closed levels, root {1}, increasing prime cutoffs, projection compatibility, and the prescribed reciprocal-mass bound for every parent. Both implications and all boundary cases are covered. [Correspondence](https://github.com/Ghuffy1/erdos691/blob/87514692c7a814ea3f500eb72bfba45da8a2bf54/submission/SCOPE.md)

## Proof submission

```json
[
  {
    "repository": "https://github.com/Ghuffy1/erdos691",
    "branch": "main",
    "commit": "87514692c7a814ea3f500eb72bfba45da8a2bf54"
  }
]
```

The selected commit is an ancestor of the prepared local main branch. Public branch membership will be checked after the authorized repository release. The complete formal proof is in `Erdos691.lean`. `Challenge.lean` checks the expanded original statement, and `Audit.lean` prints the target definitions and fifteen transitive axiom lists.

## Reproduction

- Lean is `leanprover/lean4:v4.34.0`, pinned in `lean-toolchain`.
- Mathlib is `5ed2965256430c3649e86755f9576b54eca72435`. All nine dependency revisions are pinned in `lake-manifest.json`.
- [Build instructions](https://github.com/Ghuffy1/erdos691/blob/87514692c7a814ea3f500eb72bfba45da8a2bf54/submission/REPRODUCTION.md)

```sh
lake exe cache get
python scripts/verify.py --expect-commit 87514692c7a814ea3f500eb72bfba45da8a2bf54 --fresh
```

The verification entry builds the three project modules, checks the source files explicitly, audits the declarations, and runs kernel replay. All fifteen declarations are expected to use only `propext`, `Classical.choice`, and `Quot.sound`. The actual checked results and execution limitations are supplied in the accompanying verification record. Its evidence commit is recorded by the prepared repository after completion.

## Pre-submission Lean verification

The optional `lean-verify` workflow at awards commit `f8801a856529dce27e738c6b305e46d76e7c387c` was used to organize the audit. The technical report identifies the exact proof commit, actual commands, execution environment, source hashes, standard axioms, kernel replay, and unavailable verification levels. It does not substitute for the organizers' independent mathematical and formal review.

## Attribution

- Mathematical solver team, equal contribution, in alphabetical surname order is **Will Howe (H0W4RD-dev), Grant Huffman (Ghuffy1), Jensen Kohlmeyer (JENW1N), and Liam Kruer (lkruer)**.
- The same team receives equal credit for its formalization contribution. **Ghuffy1** is the repository owner and submission coordinator. Account-to-person attribution is supplied by the team and awaits the organizers' independent confirmation.
- OpenAI AI tools assisted mathematical exploration, checking, formalization, and manuscript and submission preparation. Agent-generated local commits are labeled accordingly.
- The classical Davenport–Erdős Lean dependency is adapted from **yuta0x89/ErdosProblems**, commit `1aa94199fd3874e25b2126a0ff153e144e3e9c04`. Its mathematical authors and formal source remain separately credited. Its embedded Apache 2.0 declaration is preserved, and the full license and modification NOTICE are included. [Source credit](https://github.com/Ghuffy1/erdos691/blob/87514692c7a814ea3f500eb72bfba45da8a2bf54/THIRD_PARTY_NOTICES.md)
- No external independent human verifier is claimed. Internal mathematical review and formal checks are described at their actual level.
- The manuscript and [authorship record](https://github.com/Ghuffy1/erdos691/blob/87514692c7a814ea3f500eb72bfba45da8a2bf54/AUTHORS.md) document the proposed credits. Novelty and first priority remain unestablished pending full-text comparisons with Hall and Hill and external review.

## Submission checklist

- [x] The prepared catalog patch changes only the relevant allowed detail fields.
- [x] The mathematical target covers the full original all-A criterion, with both implications.
- [x] The complete mathematical manuscript and formal statement correspondence are supplied.
- [x] Both contribution types, all four team members, AI assistance, and reused formal code are identified.
- [x] The upstream Apache 2.0 notice, license copy, attribution and modification notice are included, with the licensing basis explained.
- [ ] The authorized public repository contains the selected proof commit on main, and all pinned links resolve.
- [ ] Contributor confirmations and any required private team-representation arrangements have been completed.
- [ ] This exact PR contains only catalog text and references, with no proof source, dependencies, binaries, or private claim materials.

The remaining boxes describe later release or submission steps. They are intentionally unsigned in this private draft.
