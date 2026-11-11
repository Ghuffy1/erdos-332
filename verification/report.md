# Verification report

**Passed for the submitted progression results. Ready for contribution submission and independent prize review.**

## Exact versions

- Formal proof revision `6d65e28f986b8434d9448e6e4ba73e7ddd17ef43` on `main`.
- Final verification checkout `4b0076ece6b77c470d676702fe037049076ac999`. Its formal source, audit entries, helper, toolchain, and dependency manifest are identical to the formal proof revision.
- Revised manuscript `cf1e6ab6401ce288dcb4194fdfe314c2edb2fc84`, ten pages. This revision adds antecedent citations and places the references on a separate page.
- Lean `4.34.1` and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Official rules at `TheJustinSunPrize/awards` revision `b1bfe454d37db2838ef76756830aeb23c40de95e`.

The current [source record](../submission/source-record.json) gives file hashes and the distinct proof, manuscript, and verification revisions. Earlier evidence remains in the history and in `verification/evidence/`.

## Original statement and mathematical review

The original question asks for sufficient conditions ensuring bounded gaps in differences that occur infinitely often. The maintained statement leaves the condition for the solver to supply and its mathematical suitability to human judgment. `Erdos332Submission.erdos_332` supplies the explicit progression predicate and proves the implication using infinite ordered-pair recurrence and a positive natural-number gap bound.

The formalized main components are the bounded-contact criterion, the exact finite circular-gap criterion with bound `2*g*H + 4*C`, and the centered finite-family bounded-gap theorem. The finite criterion includes equality in its overlap threshold. [Statement correspondence](../docs/statement-correspondence.md) · [Target declarations](targets.json)

The final mathematical review rechecked every manuscript section, the signed congruence and hull identity, the two-window endpoint argument, bounded perturbations, the centered-family construction, and the auxiliary examples. It included the cases `H = 1` and the rational limit `a = 0, b = 1`. The manuscript's additional examples, classifications, density consequences, and reciprocal-sum consequences have prose proofs. [Full mathematical review](final-review/mathematical-review.md)

The reviewed contribution is submitted as an answer in the original open-ended sufficient-condition formulation. The prize's independent mathematical review determines full-problem suitability. Worldwide priority and award eligibility remain part of that external process. [Prior-work comparison](../docs/prior-work.md)

## Executed formal checks

The final local verification finished at `2026-11-11T16:37:53.658972+00:00`. Every command returned exit 0.

```sh
lake build
lake env lean verification/Audit.lean
lake env lean verification/Challenge.lean
lake env leanchecker --fresh --verbose Submission
```

The local run rebuilt the submitted modules from a clean project build directory. Both default modules, `Erdos332` and `Submission`, passed. The independently written statement bridges passed, and all 64 expected declaration records were present. All nine dependency repositories matched their pinned commits with clean tracked source trees. [Machine-readable result](final-review/results.json)

The complete transitive axiom union was

```text
propext
Classical.choice
Quot.sound
```

The submitted source uses complete proofs. The scan found no admitted steps, custom mathematical axioms, native-decision trust additions, or kernel-check suppression. The fresh replay rechecked the imported and submitted environment using the pinned Lean kernel. Independent-implementation checking remains outside the completed checks.

[Clean build](final-review/build.log) · [Axiom audit](final-review/axioms.log) · [Statement bridges](final-review/challenge.log) · [Fresh kernel replay](final-review/kernel-replay.log)

The final hosted Linux run also passed at checkout `4b0076ece6b77c470d676702fe037049076ac999`, including its fresh replay. [GitHub Actions run](https://github.com/Ghuffy1/erdos-332/actions/runs/43057640603) · [Hosted receipt](final-review/ci-run.json) · [Proof-check output](final-review/ci-proof-check.log)

## Attribution, publication, and submission

Ghuffy1 is the repository owner and lead contribution submitter. Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer receive equal contribution credit in surname order. AI assistance is disclosed in the manuscript and author record. Individual role and identity confirmation follows the official claim process. [Authors](../AUTHORS.md)

The owner authorized public release and contribution submission after final verification. The release audit checks repository content, history, workflow logs, official forms, source links, and the catalog-only patch. The current upstream entry remains Open / Lean proof No / Eligible to claim No until the maintainers review the proposed change.

Contribution-PR submission, mathematical acceptance, individual claims, identity verification, candidate publication, public review, and awards are distinct stages of the official process. The prepared individual claims remain unsigned for their applicants. [Submission readiness](../submission/readiness.md)
