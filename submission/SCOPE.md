# Original statement and formal correspondence

The original question asks for necessary and sufficient conditions on an integer set A for its positive multiples to have ordinary natural density one. The primary source is P. Erdős, *Some unconventional problems in number theory* (1979), printed p. 77. The current identifiers are Erdős 691 and JSP-000563. Several historical PRs incorrectly equate JSP-000563 with Erdős 563. This submission uses the catalog's actual density-one question. [Original source](https://www.numdam.org/article/AST_1979__61__73_0.pdf)

The proposed answer is Theorem 1.1 and Definition 1.2 of `paper/proof.pdf`. It is submitted for mathematical and scope review. Its class of finite divisor-closed prime-block families is independent of A.

| Original obligation | Formal declaration | Correspondence |
| --- | --- | --- |
| Arbitrary sets of positive integers | `erdos691 (A : Set ℕ)` and `multiples` | Zero is excluded from both the divisor and the counted multiples. A possible zero member of A has no effect. |
| Ordinary natural density one | `HasMultiplesDensityOne`, `Erdos691Audit.DensityOne` | The count over 1 through N+1 divided by N+1 tends to 1. This is ordinary natural density. |
| A condition independent of A | `AdmissibleTest` | The structure has no A parameter. A appears only in the intersection predicate. |
| Finite divisor-closed levels and root | `AdmissibleTest.level`, `start`, `downward` | Each level is a finite set, the root is {1}, and every positive divisor is retained. |
| Increasing prime-block cutoffs | `increasing`, `supported` | Cutoffs are strictly increasing and each integer uses the specified block of primes. |
| Consistent projections | `projects` | Removing new-block prime powers yields a parent in the preceding level. |
| Prescribed mass for every parent | `retention`, `exact_fiber_characterization` | The finite quotient-image fiber equals the multiplier fiber in the manuscript. |
| Both directions | `meets_every_test_of_density_one`, `density_one_of_meets_every_test`, `erdos691` | The construction handles every A, every level, and every parent. |
| Expanded statement check | `Erdos691Audit.original_statement_verified` | Spells out the arithmetic hypotheses independently of the test structure. |

The manuscript numbers primes from 1 and transitions from 1. Lean numbers primes from 0 and expresses the transition from k to k+1. Thus the paper's prime block becomes `Finset.Ico`, and its loss `2^(-k-2)` becomes `1 / 2^(k+3)` for the transition out of Lean level k.

The paper uses Davenport–Erdős as a cited classical theorem. The formal source includes the proof of the classical input. The paper and Lean construction both use finite weighted subsets followed by divisor closure. Empty sets, finite sets, the divisor 1, arbitrarily large exponents, and infinite prime support are covered by the unrestricted theorem.

Formal verification establishes this precise criterion. Mathematical acceptance of it as a resolution of the open question, novelty, and priority remain subject to review.
