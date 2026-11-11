# Prize rules and preparation audit

Reviewed November 11, 2026. The awards repository is pinned to `f8801a856529dce27e738c6b305e46d76e7c387c`. A current clone resolved to this same commit. Relevant documents are preserved under `rules-snapshot/` with their attribution and license.

## Applicable route

JSP-000563 is outside the 50-problem MathDB pilot. Its applicable route is the standard contribution PR to TheJustinSunPrize/awards. The original proof belongs in the submitting account's external repository. Only catalog text and proof references belong in the awards PR. The prepared local repository is intended for `Ghuffy1/erdos691`. Its remote has yet to be created. [Contribution rules](https://github.com/TheJustinSunPrize/awards/blob/f8801a856529dce27e738c6b305e46d76e7c387c/CONTRIBUTING.md)

## Requirement mapping

| Requirement | Prepared evidence or disposition |
| --- | --- |
| Complete solution of the original problem | `paper/proof.pdf`, Theorem 1.1, with both directions and all sets A. Mathematical acceptance remains for the organizers. |
| Complete formal proof | `Erdos691.lean`, `Erdos691.Adaptive.erdos691` and `fullSolution`. |
| Original problem and exact location | Erdős 691, 1979 source p. 77, catalog JSP-000563. Recorded in `SCOPE.md`. |
| Exact formal statement and correspondence | `Challenge.lean`, `SCOPE.md`, and the independent fiber characterization. |
| Original repository owned by submitter | Intended owner Ghuffy1. Local preparation cannot establish ownership of a future GitHub repository. |
| Named branch and full commit | `main` and the selected proof SHA recorded in `proof-version.json`. |
| Reproducible version and dependencies | Exact Lean pin, nine dependency SHAs, `REPRODUCTION.md`, and `scripts/verify.py`. |
| Every target and bridge checked | Default build covers all three modules. Explicit source checks and fifteen axiom audits are recorded in the verification report. |
| Disclose all proof assumptions | Standard Lean foundations are listed for every audited declaration. Verification records identify the achieved checking levels. |
| Separate solver and formalizer attribution | `AUTHORS.md`, `THIRD_PARTY_NOTICES.md`, and the two attribution fields in the PR draft. |
| AI disclosure | Manuscript acknowledgment, `AUTHORS.md`, and PR attribution. |
| Respect third-party rights | Existing classical source credited. Its redistribution permission remains unresolved and is a release condition. |
| Check overlapping submissions | `RELATED_WORK.md` records the searches and four related closed PRs, with the limits of the inspection. |
| Permitted awards changes | `catalog.patch` updates only the relevant detail entry's status, proof, attribution, and publication fields. Index, eligibility, claim states, and award records are maintained by the organizers. |
| Public proof evidence | Prepared manuscript and source links become public only after a user-authorized release. Draft links identify their intended destination. |
| No private identity or payment materials in public files | Claim working materials are kept in the ignored `private/` directory. The manuscript retains only the author emails explicitly requested for the paper. |
| Personal claims | Each claimant personally submits and confirms their own claim. Four private drafts are supplied. |
| Identity verification | Each applicant follows the current repository's email-verification instructions after a claim. Identity verification has not occurred. |
| Candidate review | The organizers start the role-specific 14-day public-notice period. Local preparation starts no notice period. |
| Team representation | Ghuffy1 is the requested coordinator. Team authorization, legal payee, and any internal distribution require the team's own private confirmation. |
| Final award | Tier, priority, acceptance, recipient confirmation, and payment are decisions of the prize organizers. |

## Current catalog screening

The catalog currently records Open, Lean proof No, and Eligible to claim No. Under the repository's definitions, eligibility becomes possible after a complete solution and complete Lean proof are recorded. The current flag does not bar preparing or submitting a complete solution for review. [Catalog](https://github.com/TheJustinSunPrize/awards/blob/f8801a856529dce27e738c6b305e46d76e7c387c/problems/catalog-0501-0600.md#JSP-000563), [Eligibility definitions](https://github.com/TheJustinSunPrize/awards/blob/f8801a856529dce27e738c6b305e46d76e7c387c/problems/README.md#legacy-eligibility-and-claim-status-columns)

## Website and repository differences

The website Selection Rules describe broad eligibility, team representation, the 70/30 solver/formalizer division, public access, and intellectual-property requirements. Some website language discusses partial completion, while the contribution instructions explicitly accept complete original-problem solutions. This package supplies the full criterion and both directions. The website FAQ permits some Lean-only identity waivers, while the current repository requires an identity email from every applicant. The drafts follow the current repository's explicit procedure. The website also describes a collective team payee. The repository requires personal claims. Any collective-recipient arrangement therefore needs confirmation from the prize team before anyone purports to claim for another member. [Selection Rules](https://www.hejustinsun.com/prize/rules), [Claim guidance](https://www.hejustinsun.com/prize/claim), [FAQ](https://www.hejustinsun.com/prize/faq)

The prize publishes no complete internal grading matrix. This preparation checks the public submission requirements. It assigns no tier, amount, guaranteed eligibility, or priority. [Assessment guidance](https://github.com/TheJustinSunPrize/awards/blob/f8801a856529dce27e738c6b305e46d76e7c387c/docs/grading.md)

The Lean pre-submission skill is optional. Its source, statement, dependency, target, axiom, and replay checks guide the technical report. Any unavailable isolation or external-checker level is disclosed in that report. [Verification guidance](https://github.com/TheJustinSunPrize/awards/blob/f8801a856529dce27e738c6b305e46d76e7c387c/docs/verification.md)
