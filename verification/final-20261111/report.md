# Final pre-submission verification

**Overall verdict — verification passed.**

The exact source commit **ae09eff8eada7ed7df222e5da6b5e0e3e36a75cb** passed the full pre-submission run on November 11, 2026. [Completed CI run](https://github.com/Ghuffy1/erdos691/actions/runs/42968222607)

| Required judgment | Result |
| --- | --- |
| Correspondence to the original question | Passed for the proposed all-A divisor-closed criterion. |
| Verification of the exact selected commit | Passed, with every recorded command returning 0. |
| Completeness of the criterion | Both implications are fully proved for arbitrary A, with the expanded statement and exact fiber bridge checked. |
| Lean completeness | Meets. All fifteen audited declarations use only the three standard Lean foundations. |

The original source is Erdős 691, *Some unconventional problems in number theory* (1979), printed p. 77, corresponding to JSP-000563. The full coverage explanation is in [SCOPE.md](../../submission/SCOPE.md). The main theorem is `Erdos691.Adaptive.erdos691` and the expanded bridge is `Erdos691Audit.original_statement_verified`.

## Fresh execution

The run used Linux-7.0.0-1017-azure-x86_64-with-glibc2.39, Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`, and all eight other pinned dependencies. Actual checkout revisions and tracked-source cleanliness were checked before and after. All seven proof, configuration and verification-script hashes remained unchanged.

The clean build included all three project modules. Explicit module builds and source checks followed. The axiom audit covered fifteen declarations. Module replay checked both the main proof and the expanded statement, and fresh-environment replay checked their full imported environment.

| Command | Exit code | Seconds |
| --- | --- | --- |
| lean-version | 0 | 0.819 |
| lake-version | 0 | 0.064 |
| default-build | 0 | 36.822 |
| build-Erdos691 | 0 | 3.722 |
| check-Erdos691 | 0 | 20.030 |
| build-Challenge | 0 | 2.319 |
| check-Challenge | 0 | 2.573 |
| build-Audit | 0 | 1.620 |
| check-Audit | 0 | 2.522 |
| kernel-Erdos691 | 0 | 6.927 |
| kernel-Challenge | 0 | 5.874 |
| kernel-fresh-Challenge | 0 | 406.684 |

The raw outputs and their SHA256 values are preserved alongside this report. [Machine-readable result](result.json)

## Package and publication audit

The complete tracked repository and its four-commit history were inspected. All 80 tracked files passed the applicable syntax, source-version, reference and privacy checks. The six-page manuscript matches its reviewed PDF digest. Private claim drafts, dependency caches, credentials, and payment data are excluded from the tracked repository. [Preflight record](preflight.json)

The awards change is limited to the existing JSP-000563 catalog record's status, formalization reference, attribution basis and publication details. The original question, surrounding records, eligibility flag and claim-status fields are preserved. [Catalog audit](catalog-audit.json)

Ghuffy1 is the repository owner and submission coordinator. Will Howe, Grant Huffman, Jensen Kohlmeyer and Liam Kruer receive equal credit in alphabetical surname order. AI assistance and the classical source are credited. The embedded Apache 2.0 source notice is retained with the license and modification notice.

## Trust and remaining review

The run uses Lean's kernel and trusted pinned dependency caches. A separately implemented kernel and independent human review remain for subsequent review. Earlier Windows and Ubuntu checks are preserved in the parent verification directory.

The result establishes the precise mathematical criterion. JSP's assessment of the proposed answer, authorship, priority and award eligibility remains pending. The Hall book sections, Hall's 1990 chapter and Hill's dissertation comparisons remain unfinished, so first priority is unestablished. These limitations are disclosed in the submission.

The user authorized submission after this final check passed. The repository is being released for the contribution review. Each contributor's later award claim and identity verification remain separate steps.
