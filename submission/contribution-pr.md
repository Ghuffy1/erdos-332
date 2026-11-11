# JSP-000276 / Erdős 332 — progression-based sufficient conditions

Private contribution-PR draft for Ghuffy1. Publication and submission await the owner's authorization. The catalog changes below are proposed outcomes for review.

## Submission type

- [x] Mathematical solver information
- [x] Lean proof or formalization author information

## Problem

- **Problem ID** — JSP-000276, corresponding to Erdős Problem 332.
- **Original source** — Erdős and Graham, *Old and New Problems and Results in Combinatorial Number Theory* (1980), printed page 50. [Original monograph](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- **Maintained statement** — [Erdős 332 at commit 4b5e5275a2734adace65d6c0a87e5bb508dc0363](https://github.com/google-deepmind/formal-conjectures/blob/4b5e5275a2734adace65d6c0a87e5bb508dc0363/FormalConjectures/ErdosProblems/332.lean). It asks the solver to supply a sufficient condition and leaves its mathematical suitability to human judgment.
- **Current entry** — Open, Lean proof No, Eligible to claim No.
- **Proposed change** — Record the proposed progression-based solution and its formalization, with equal author credits. The attached catalog-only patch requests Solved and a verified Lean source as the review outcome. Eligibility and claim-status fields are reserved for maintainers.
- **Related issue** — No claim issue has been opened for this preparation.
- **Related PRs** — [384](https://github.com/TheJustinSunPrize/awards/pull/384), [1510](https://github.com/TheJustinSunPrize/awards/pull/1510), [2240](https://github.com/TheJustinSunPrize/awards/pull/2240), and [3093](https://github.com/TheJustinSunPrize/awards/pull/3093). The density-only submission was withdrawn as a known partial result. Other records contain the JSP/Erdős numbering mismatch described in the [comparison](https://github.com/Ghuffy1/erdos-332/blob/782f2dcf1105c4ddc3ecde89120d8e78a535b57a/docs/prior-work.md). The present conditions concern overlapping progression pairs and admit zero-upper-Banach-density examples.
- **Mathematical manuscript** — [Recurring Differences from Overlapping Arithmetic Progressions](https://github.com/Ghuffy1/erdos-332/blob/6d65e28f986b8434d9448e6e4ba73e7ddd17ef43/paper/recurring_differences.pdf), version prepared 11 November 2026, by Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer. Theorems 1.1 and 1.2 are on page 2, with proofs in Sections 4–6.

## Formal statement

- **Complete mathematical solution supplied with the formal proof** — The manuscript linked above, with its [typesetting source](https://github.com/Ghuffy1/erdos-332/blob/6d65e28f986b8434d9448e6e4ba73e7ddd17ef43/paper/recurring_differences.tex).
- **Mathematical review status** — Proposed sufficient-condition answer awaiting independent full-problem suitability review. Prior internal checking is supporting evidence.
- **Formal statement location** — [Submission.lean](https://github.com/Ghuffy1/erdos-332/blob/6d65e28f986b8434d9448e6e4ba73e7ddd17ef43/Submission.lean).
- **Main target** — `Erdos332Submission.erdos_332`.
- **Statement origin** — An explicit supplied condition for the open-ended maintained statement. Maintainer approval of the proposed mathematical scope is requested.
- **Correspondence** — The predicate states the progression assumptions and either bounded contact or the finite circular-gap test. The conclusion uses infinitely many ordered pairs with signed difference and a positive natural-number gap bound. The [correspondence record](https://github.com/Ghuffy1/erdos-332/blob/782f2dcf1105c4ddc3ecde89120d8e78a535b57a/docs/statement-correspondence.md) and [target manifest](https://github.com/Ghuffy1/erdos-332/blob/782f2dcf1105c4ddc3ecde89120d8e78a535b57a/verification/targets.json) retain the exact scope and additional manuscript results.

The main components are

- `Erdos332.main_bounded_contact`, [source line 1061](https://github.com/Ghuffy1/erdos-332/blob/6d65e28f986b8434d9448e6e4ba73e7ddd17ef43/Erdos332.lean#L1061).
- `Erdos332.main_finite_test`, [source line 1077](https://github.com/Ghuffy1/erdos-332/blob/6d65e28f986b8434d9448e6e4ba73e7ddd17ef43/Erdos332.lean#L1077), with bound `2*g*H + 4*C` and a non-strict threshold.
- `Erdos332.centered_finite_intersection`, [source line 1138](https://github.com/Ghuffy1/erdos-332/blob/6d65e28f986b8434d9448e6e4ba73e7ddd17ef43/Erdos332.lean#L1138).

The auxiliary sparse examples, classification, and corollaries in the manuscript have prose proofs and are outside the machine-checked targets.

## Proof submission

```json
[
  {
    "repository": "https://github.com/Ghuffy1/erdos-332",
    "branch": "main",
    "commit": "6d65e28f986b8434d9448e6e4ba73e7ddd17ef43"
  }
]
```

The selected commit belongs to `main`. `Submission.lean` proves the original-question implication through the progression results in `Erdos332.lean`. The original proof repository is owned by Ghuffy1.

## Reproduction

- **Lean** — `leanprover/lean4:v4.34.1`, pinned in [lean-toolchain](https://github.com/Ghuffy1/erdos-332/blob/6d65e28f986b8434d9448e6e4ba73e7ddd17ef43/lean-toolchain).
- **Mathlib** — `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- **All package revisions** — [lake-manifest.json](https://github.com/Ghuffy1/erdos-332/blob/6d65e28f986b8434d9448e6e4ba73e7ddd17ef43/lake-manifest.json).
- **Instructions** — [reproduction record](https://github.com/Ghuffy1/erdos-332/blob/782f2dcf1105c4ddc3ecde89120d8e78a535b57a/docs/reproduction.md).

```sh
git clone https://github.com/Ghuffy1/erdos-332.git
cd erdos-332
git checkout 6d65e28f986b8434d9448e6e4ba73e7ddd17ef43
lake exe cache get
lake build
lake env lean verification/Audit.lean
lake env lean verification/Challenge.lean
lake env leanchecker --fresh --verbose Submission
```

The evidence helper `python scripts/verify.py --kernel-replay` records these checks, verifies committed bytes and dependency revisions, and checks that every expected theorem has an axiom result.

## Pre-submission Lean verification

- **Checked revision** — `6d65e28f986b8434d9448e6e4ba73e7ddd17ef43`.
- **Method** — Native Lean build, independent statement bridges, all-target transitive axiom audit, fresh kernel replay, and hosted Linux reproduction.
- **Date** — 11 November 2026.
- **Technical result** — All checks passed for 64 audited declarations.
- **Axioms** — `propext`, `Classical.choice`, and `Quot.sound`.
- **Report** — [verification report](https://github.com/Ghuffy1/erdos-332/blob/782f2dcf1105c4ddc3ecde89120d8e78a535b57a/verification/report.md), with [raw evidence](https://github.com/Ghuffy1/erdos-332/blob/782f2dcf1105c4ddc3ecde89120d8e78a535b57a/verification/evidence).
- **Hosted run** — [GitHub Actions 43052549499](https://github.com/Ghuffy1/erdos-332/actions/runs/43052549499), successful at the selected commit.
- **Trust and scope** — The replay uses Lean's kernel. Independent-implementation checking and independent mathematical acceptance remain outstanding.

## Attribution

The owner proposes the following credits, with names ordered alphabetically by surname.

- **Mathematical authors** — Will Howe (@H0W4RD-dev), Grant Huffman (@Ghuffy1), Jensen Kohlmeyer (@JENW1N), and Liam Kruer (@lkruer), with equal contribution credit for the joint mathematical submission.
- **Formalization authors** — The same four authors, with equal contribution credit for the joint formalization submission.
- **Owner and lead contribution submitter** — Grant Huffman (@Ghuffy1).
- **Independent human verifier** — Awaiting the prize's independent review.

These are owner-declared credits. Individual role descriptions and identity confirmations remain part of the prize review. [Author record](https://github.com/Ghuffy1/erdos-332/blob/6d65e28f986b8434d9448e6e4ba73e7ddd17ef43/AUTHORS.md) · [Citation metadata](https://github.com/Ghuffy1/erdos-332/blob/6d65e28f986b8434d9448e6e4ba73e7ddd17ef43/CITATION.cff)

OpenAI's ChatGPT assisted development, checking, mathematical exposition, formalization, and repository preparation. This assistance is acknowledged in the paper and source records.

The technical verification is an automated self-check. Independent human mathematical verification and contributor identity verification are requested through the official process. Each future claimant will submit their own claim and identity confirmation.

## Submission checklist

- [x] The proposed patch is limited to the permitted fields of the relevant catalog entry.
- [x] The mathematical manuscript, statement correspondence, exact source commit, reproduction commands, and axiom evidence are supplied.
- [x] The selected commit is in the named branch.
- [x] The catalog patch contains references and attribution, with the formal source and artifacts hosted in the external repository.

The applicant personally completes the following confirmations from the official submission checklist before opening the PR.

- [ ] I changed only the relevant catalog's solver attribution, Lean proof information or supporting sources and supplied the applicable evidence.
- [ ] The submitted result fully solves the original problem. Any submitted Lean proof is complete at the specified commit, with no `sorry`, `admit` or added unproved assumptions replacing proof steps.
- [ ] For Lean, I have linked the complete mathematical solution and its proof or publication evidence provided earlier, or supplied them in this PR, and identified the mathematical solver and Lean formalization author separately.
- [ ] For Lean, I am claiming my own contribution in the original personal or organization repository, with verifiable contribution evidence for an organization repository. The selected commit is in the named branch, and I supplied statement correspondence, reproduction commands and axiom audit results.
- [ ] This PR contains no Lean source files, archives, binaries, vendored dependencies or private identity/contact/payment information.

This draft requests full-problem scope review of the proposed sufficient-condition answer. It carries no award, recipient, payment, or completed public-review claim.

---
Adapted from The Justin Sun Prize contribution template at revision `b1bfe454d37db2838ef76756830aeb23c40de95e`, under CC BY 4.0. Changes supply the present source, authors, verification evidence, and private-preparation status.
