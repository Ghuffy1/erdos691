# A divisor-closed criterion for Behrend sequences

Private preparation of the combined mathematical and Lean submission for **Erdős problem 691 / JSP-000563**.

The GitHub owner and submission coordinator is **Ghuffy1**. Will Howe (**H0W4RD-dev**), Grant Huffman (**Ghuffy1**), Jensen Kohlmeyer (**JENW1N**), and Liam Kruer (**lkruer**) receive equal team contribution credit. The paper uses alphabetical surname order. AI assistance and the separately credited classical formalization are documented in [AUTHORS.md](AUTHORS.md) and [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

## Mathematical result

For every set of positive integers A, its positive multiples have ordinary natural density one if and only if A meets every admissible family of finite divisor-closed prime-block sets. The admissibility conditions involve finite arithmetic and are independent of A.

- [Proof manuscript](paper/proof.pdf), Theorem 1.1 and Definition 1.2.
- [Complete Lean proof](Erdos691.lean), `Erdos691.Adaptive.erdos691`.
- [Expanded statement and bridge](Challenge.lean), `Erdos691Audit.original_statement_verified`.
- [Statement correspondence](submission/SCOPE.md).

## Reproduce

Install Git, the official Elan toolchain manager, and Python 3.9 or later. From a fresh checkout of the selected proof commit, run

```sh
lake exe cache get
python scripts/verify.py --fresh
```

The script checks the exact Lean version and all nine dependency revisions, builds all three project modules, explicitly checks their source files, audits fifteen declarations, and replays the proof and statement bridge through Lean's kernel. A fresh checkout supplies an empty project build directory. The Mathlib download command retrieves pinned dependency caches. The verification script itself performs no downloads.

For individual commands and trust boundaries, read [submission/REPRODUCTION.md](submission/REPRODUCTION.md). The toolchain is Lean **4.34.0** and Mathlib is pinned to **5ed2965256430c3649e86755f9576b54eca72435**.

## Submission materials

The [readiness audit](submission/READINESS.md) records completed checks and outstanding release conditions. The [PR draft](submission/PR_BODY.md) and catalog patch are prepared for the standard GitHub route. They target the existing JSP-000563 entry. Repository ownership, public links, contributor identity, source rights, priority, and the organizers' review must be established at the appropriate submission stage.

The original repository is **Ghuffy1/erdos691**, created with private visibility. Public release remains subject to the user's instruction.
