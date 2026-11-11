# Private submission materials

The current route is the legacy contribution-PR process. JSP-000276 is absent from the 50-problem MathDB pilot register at official revision `b1bfe454d37db2838ef76756830aeb23c40de95e`.

This directory is preparation material. The owner authorizes publication and submission separately.

## Materials

- `contribution-pr.md` is the combined mathematical-solution/formalization contribution draft.
- `awards.patch` changes the permitted fields of the single catalog entry. The eligibility and claim-status fields are reserved for maintainers.
- `claims/` contains one unsigned award-claim draft for each contributor. Each applicant must submit through their own account after the contribution PR has merged, subject to the applicable rules.
- `requirements.json` and `readiness.md` map the official requirements to evidence and outstanding external actions.
- `source-record.json` pins the original problem, manuscript, formal source revision, and technical checks.
- [Final preparation audit](final-audit.json) records 27 completed checks covering the package, exact source, author metadata, official forms, catalog patch, repository visibility, and private-material scan.

## Release sequence

1. The authors confirm attribution and scope, and the owner authorizes public release.
2. The owner makes the external proof repository accessible for public review and confirms the pinned commit remains on `main`.
3. The owner opens the catalog-only contribution PR using the prepared draft and patch. Recheck the official base before applying the patch.
4. Maintainers review the mathematical contribution and verify its formal coverage. A successful local build supports that review.
5. After the required contribution PR merge, each claimant submits their own claim and sends their own identity-confirmation email.
6. Maintainers establish candidate status and the category-specific public-notice clock, resolve challenges, and obtain written recipient confirmations.

The public review clock begins with the official candidate notice. Dates for that stage are entered from the actual event. The preparation carries no award amount, payment allocation, recipient signature, or invented review date.
