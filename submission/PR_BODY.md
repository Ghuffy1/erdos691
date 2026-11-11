## Submission type

- [x] Mathematical solver information
- [x] Lean proof or formalization author information

This combined submission presents a complete arithmetic criterion for the density-one property and its formal proof. The upstream file-level Apache 2.0 declaration is preserved with its full license and modification notice. The statement, mathematical solution and contribution attribution are submitted for the organizers’ review.

## Problem

- Problem ID is **JSP-000563**, corresponding to **Erdős problem 691**.
- The original question is on printed p. 77 of P. Erdős, *Some unconventional problems in number theory*, Astérisque 61 (1979), 73–82. [Primary source](https://www.numdam.org/article/AST_1979__61__73_0.pdf)
- The proposed change records the full necessary-and-sufficient criterion and its complete Lean formalization in the existing catalog entry. The organizers retain control of eligibility, claim statuses, and award records.
- The proof manuscript is *A divisor-closed criterion for Behrend sequences*, November 11, 2026, Theorem 1.1 and Definition 1.2, pp. 1–2, with proofs on pp. 3–6. [Pinned manuscript](https://github.com/Ghuffy1/erdos691/blob/ae09eff8eada7ed7df222e5da6b5e0e3e36a75cb/paper/proof.pdf)
- Related closed PRs are 3697, 3795, 4295, and 4507. Their scope and source limitations are recorded in [Related work](https://github.com/Ghuffy1/erdos691/blob/ae09eff8eada7ed7df222e5da6b5e0e3e36a75cb/submission/RELATED_WORK.md). The present target is the universal arithmetic criterion for every set A.

## Formal statement

- The complete mathematical solution is supplied by the manuscript linked above.
- Mathematical review is requested. Organizer acceptance and external human review are pending.
- The statement is proposed for review against the original open-ended question and awaits maintainer approval.
- The target is `Erdos691.Adaptive.erdos691 (A : Set ℕ)`, proving `HasMultiplesDensityOne A ↔ MeetsEveryTest A`. [Statement and proof](https://github.com/Ghuffy1/erdos691/blob/ae09eff8eada7ed7df222e5da6b5e0e3e36a75cb/Erdos691.lean#L5748)
- The expanded bridge is `Erdos691Audit.original_statement_verified`. [Expanded statement](https://github.com/Ghuffy1/erdos691/blob/ae09eff8eada7ed7df222e5da6b5e0e3e36a75cb/Challenge.lean)
- A is arbitrary. Multiples and divisors are positive. Density is ordinary natural density. The test class is independent of A and imposes finite divisor-closed levels, root {1}, increasing prime cutoffs, projection compatibility, and the prescribed reciprocal-mass bound for every parent. Both implications and all boundary cases are covered. [Correspondence](https://github.com/Ghuffy1/erdos691/blob/ae09eff8eada7ed7df222e5da6b5e0e3e36a75cb/submission/SCOPE.md)

## Proof submission

```json
[
  {
    "repository": "https://github.com/Ghuffy1/erdos691",
    "branch": "main",
    "commit": "ae09eff8eada7ed7df222e5da6b5e0e3e36a75cb"
  }
]
```

The selected commit is contained in main in the original repository owned by Ghuffy1. The complete formal proof is in `Erdos691.lean`. `Challenge.lean` checks the expanded original statement, and `Audit.lean` prints the target definitions and fifteen transitive axiom lists.

## Reproduction

- Lean is `leanprover/lean4:v4.34.0`, pinned in `lean-toolchain`.
- Mathlib is `5ed2965256430c3649e86755f9576b54eca72435`. All nine dependency revisions are pinned in `lake-manifest.json`.
- [Build instructions](https://github.com/Ghuffy1/erdos691/blob/ae09eff8eada7ed7df222e5da6b5e0e3e36a75cb/submission/REPRODUCTION.md)

```sh
lake exe cache get
python scripts/verify.py --expect-commit ae09eff8eada7ed7df222e5da6b5e0e3e36a75cb --fresh
```

The verification entry builds the three project modules, checks the source files explicitly, audits the declarations, and runs kernel replay. All fifteen declarations use only `propext`, `Classical.choice`, and `Quot.sound`. All twelve recorded commands passed in both Windows and private hosted Ubuntu runs. The fifteen axiom audits report only the three standard foundations. The full-environment replay passed on both systems.

## Pre-submission Lean verification

A fresh full verification of the selected commit completed successfully on November 11, 2026. The clean build, explicit builds and source checks for all three modules, fifteen transitive axiom audits, module kernel checks, and fresh-environment kernel replay all returned exit code 0. The proof, configuration and verification script remained byte-identical throughout.

- Checked source commit is `ae09eff8eada7ed7df222e5da6b5e0e3e36a75cb`.
- [Completed verification run](https://github.com/Ghuffy1/erdos691/actions/runs/42968222607)
- [Final report and raw logs](https://github.com/Ghuffy1/erdos691/blob/32a44b30caae0f6d664bc38ea974a68bad7debac/verification/final-20261111/report.md)
- Lean 4.34.0 and all nine dependency revisions were checked against their pins.
- The replayer uses Lean's kernel. Independent human review and a separately implemented kernel check remain pending.

The original question, both directions, boundary cases, arithmetic fibers and A-independent test class were reviewed against the manuscript and expanded statement. The organizers' own mathematical and formal review remains pending.

## Attribution

- Mathematical solver team, equal contribution, in alphabetical surname order is **Will Howe (H0W4RD-dev), Grant Huffman (Ghuffy1), Jensen Kohlmeyer (JENW1N), and Liam Kruer (lkruer)**.
- The same team receives equal credit for its formalization contribution. **Ghuffy1** is the repository owner and submission coordinator. Account-to-person attribution is supplied by the team and awaits the organizers' independent confirmation.
- OpenAI AI tools assisted mathematical exploration, checking, formalization, and manuscript and submission preparation. Agent-generated local commits are labeled accordingly.
- The classical Davenport–Erdős Lean dependency is adapted from **yuta0x89/ErdosProblems**, commit `1aa94199fd3874e25b2126a0ff153e144e3e9c04`. Its mathematical authors and formal source remain separately credited. Its embedded Apache 2.0 declaration is preserved, and the full license and modification NOTICE are included. [Source credit](https://github.com/Ghuffy1/erdos691/blob/ae09eff8eada7ed7df222e5da6b5e0e3e36a75cb/THIRD_PARTY_NOTICES.md)
- External independent human review remains pending. Internal mathematical review and formal checks are described at their actual level.
- The manuscript and [authorship record](https://github.com/Ghuffy1/erdos691/blob/ae09eff8eada7ed7df222e5da6b5e0e3e36a75cb/AUTHORS.md) document the proposed credits. Novelty and first priority remain unestablished pending full-text comparisons with Hall and Hill and external review.

## Submission checklist

- [x] The PR changes only the relevant catalog's solver attribution, Lean proof information and supporting sources.
- [x] The submitted criterion covers the original all-A question and has a complete proof at the specified commit, with only the three standard Lean foundations.
- [x] The full mathematical manuscript is linked, and the mathematical and formalization contributions are identified separately.
- [x] Ghuffy1 submits the team's contribution from its original repository. The selected commit is on main, with statement correspondence, reproduction commands and axiom results supplied.
- [x] The PR contains only catalog text and public evidence references. Private identity, payment and personal claim materials remain outside it.

The four equal contributors are credited in full above and in the manuscript. The catalog follows the repository's abbreviated display convention. First priority remains unestablished. The outstanding literature comparisons and external review are explicitly disclosed.
