# Recurring differences from overlapping arithmetic progressions

Combined mathematical-solution and formalization submission for Erdős Problem 332, catalogued as **JSP-000276**.

Submitted by Ghuffy1 in [JSP PR #5566](https://github.com/TheJustinSunPrize/awards/pull/5566). The proof repository is public for independent review. [Submission receipt](submission/receipt.json)

**Repository owner and lead submitter — Grant Huffman (@Ghuffy1).** Will Howe (@H0W4RD-dev), Grant Huffman (@Ghuffy1), Jensen Kohlmeyer (@JENW1N), and Liam Kruer (@lkruer) receive equal contribution credit. The author order follows surnames. [Attribution record](AUTHORS.md)

## Mathematical materials

- [Proof manuscript](paper/recurring_differences.pdf), with all four authors, correspondence addresses, and an AI acknowledgment.
- [Manuscript source](paper/recurring_differences.tex).
- [Formal proof](Erdos332.lean).
- [Original-question entry point and explicit sufficient condition](Submission.lean).
- [Statement correspondence and coverage](docs/statement-correspondence.md).
- [Prior work and related submissions](docs/prior-work.md).

The main results give a bounded-contact criterion, an exact finite circular-gap criterion with gap bound `2*g*H + 4*C`, and a centered finite-family intersection theorem. The manuscript also proves auxiliary constructions and consequences. The precise formal coverage is recorded separately from the manuscript's additional results.

## Reproduce the verification

Install the version of Lean named in `lean-toolchain`. The manifest fixes mathlib and all transitive package revisions.

```sh
lake exe cache get
python scripts/verify.py --kernel-replay
```

The command builds the project, checks the independent recurring-pair statement bridge, audits every proof theorem, verifies dependency revisions, and replays the compiled proof in a fresh kernel environment. It writes raw logs and a machine-readable result under `.verification-run/`.

`Erdos332Submission.erdos_332` states the original implication with an explicit sufficient-condition predicate and a positive natural-number gap bound. Its main components are `Erdos332.main_bounded_contact`, `Erdos332.main_finite_test`, and `Erdos332.centered_finite_intersection`. [Verification entry](verification/Audit.lean) · [Statement bridge](verification/Challenge.lean)

## Submission and review

[Submission materials](submission/README.md) contain the proposed catalog-only patch, the submitted contribution PR body, individual unsigned claim drafts, and the requirements matrix. Each award applicant submits and confirms their own claim. Ghuffy1 coordinates the joint contribution submission.

The owner authorized publication and submission after final verification. The contribution PR is open for review. Mathematical acceptance, full-problem scope acceptance, priority, identity verification, and awards belong to the prize's external process. The open-ended nature of Erdős 332 and the earlier density-only submissions are addressed explicitly in the coverage and prior-work documents.

## Provenance and rights

OpenAI's ChatGPT assisted the mathematical development, checking, exposition, formalization, and repository preparation. The equal-contribution designation and account mapping were supplied by the owner. Each contributor's personal confirmation remains part of the attribution process.

The work was developed privately before preparation of this repository. The source provenance record links the exact prior local proof bytes. A private commit timestamp supplies provenance information. Independently corroborated public history is required for a public priority determination.

Authored material carries the [rights notice](LICENSE). [Third-party notices](THIRD_PARTY_NOTICES.md) identify the licenses and origins of dependencies and adapted submission formats.
