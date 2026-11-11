# Verification report

**Technical verification passed for the declared formal targets. Full-problem acceptance, attribution, and award eligibility await the prize's independent review.**

## Checked revision

- Repository `Ghuffy1/erdos-332`
- Branch `main`
- Proof commit `6d65e28f986b8434d9448e6e4ba73e7ddd17ef43`
- Lean `4.34.1`
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
- Rule snapshot `TheJustinSunPrize/awards` at `b1bfe454d37db2838ef76756830aeb23c40de95e`
- Original maintained statement at `google-deepmind/formal-conjectures` commit `4b5e5275a2734adace65d6c0a87e5bb508dc0363`

The proof commit is present on the named branch. The checked proof files, manuscript, toolchain, and manifest match that commit byte-for-byte. All nine dependency repositories match their pinned revisions and have clean tracked source trees. The [source record](../submission/source-record.json) and [run result](evidence/results.json) preserve the hashes.

## Explicit judgments

| Question | Judgment | Basis |
| --- | --- | --- |
| Does the proof address the specified original question? | Yes, through the supplied progression conditions | `Submission.lean` gives an explicit predicate on sets and proves the original implication with infinite-pair recurrence and a positive natural-number gap bound. |
| Did the specified commit pass the checks? | Yes | Local build, all target checks, dependency checks, axiom audit, and fresh kernel replay completed with exit 0. Hosted Linux CI also passed at the same commit. |
| Has it been independently established as a complete resolution of the original open-ended problem? | Pending mathematical scope judgment | The maintained problem explicitly leaves the mathematical suitability of a proposed sufficient condition to human judgment. The earlier density-only result was withdrawn as partial. |
| Does it meet proof-completeness requirements? | The declared theorems are complete in the checked environment. Whole-problem acceptance is pending | The proof contains no admitted steps or additional mathematical axioms. The paper's auxiliary examples and corollaries have prose proofs and are outside the machine-checked targets. |

## Formal scope

The main entry point is `Erdos332Submission.erdos_332`. It proves

```text
sufficientCondition A → HasBoundedGaps (recurrentDifferences A).
```

The sufficient condition consists of explicit finite progression models with escaping bases, positive coprime step quotients, nonnegative lengths, and bounded displacement from the set. It then requires either positive normalized overlap together with bounded cross-row contact on infinitely many models, or the finite circular-gap inequality on infinitely many models.

The component targets are `Erdos332.main_bounded_contact`, `Erdos332.main_finite_test`, and `Erdos332.centered_finite_intersection`. The finite-test conclusion retains the exact bound `2*g*H + 4*C` and permits equality in the hypothesis.

`recurrentDifferences` uses infinitely many ordered pairs of natural numbers, with signed integer differences. `natural_gap_bound` supplies the explicit conversion to the positive natural-number bound in the maintained statement. `verification/Challenge.lean` gives another statement bridge using independently written recurrence and bounded-gap definitions. [Target locations and coverage](targets.json) · [Correspondence matrix](../docs/statement-correspondence.md)

The formal proof covers the two main sufficient conditions and the centered-family bounded-gap theorem. The manuscript's separated-union classification, explicit sparse constructions, sharpness examples, and density/reciprocal-sum consequences are supplied in prose. Their scope remains explicit throughout the package.

## Executed checks

The native run completed on 11 November 2026. Each command returned exit 0.

```sh
lake build
lake env lean verification/Audit.lean
lake env lean verification/Challenge.lean
lake env leanchecker --fresh --verbose Submission
```

The build includes both default modules, `Erdos332` and `Submission`. The audit checks 64 declarations, comprising the main proof, the original-question bridge, and the independent statement bridges. The source scan found no proof placeholders, custom axiom declarations, native-decision trust additions, or kernel-check suppression in the submitted proof files.

The transitive axiom union is exactly

```text
propext
Classical.choice
Quot.sound
```

These are the standard classical Lean foundations. The fresh replay rebuilds the imported and submitted declaration environment using the kernel shipped with the pinned toolchain. Independent-implementation checking remains outstanding.

Compiler warnings concern unused argument names, deprecated simplification-lemma names, and style. They do not represent missing proofs. The [full local logs](evidence/results.json) record the commands and durations. [Build](evidence/build.log) · [Axiom audit](evidence/axioms.log) · [Statement bridges](evidence/challenge.log) · [Fresh replay](evidence/kernel-replay.log)

The hosted workflow passed at the same proof commit on Linux. Its run is [43052549499](https://github.com/Ghuffy1/erdos-332/actions/runs/43052549499). The pinned workflow and actions are part of the checked revision. [Run receipt](evidence/ci-run.json) · [Proof-check console output](evidence/ci-proof-check.log)

## Mathematical and priority review

The paper supplies proofs of the two progression criteria and the centered-family theorem, together with explicit sparse examples and boundary constructions. Ruzsa's upper-Banach-density results and the sparse classes of Leth and Goldbring–Leth are credited. Related prize PRs 384, 1510, 2240, and 3093 are disclosed. The prior density-only claim and the mapping errors in other records are described with their source links. [Prior-work comparison](../docs/prior-work.md)

The contribution is proposed for independent assessment as an answer to the open-ended question. Worldwide priority and the sufficiency of the contribution for the prize's complete-solution standard are pending. The current upstream catalog is Open / Lean proof No / Eligible to claim No. The draft catalog change is a proposal for review.

## Attribution and privacy

The repository owner is Ghuffy1. The owner has designated Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer as equal contributors. Their account mapping and addresses appear in the manuscript and [author record](../AUTHORS.md). AI assistance is disclosed. Individual contribution roles, identity verification, and any formalization-claim ownership issues require personal and maintainer confirmation.

The repository remains private. The package contains unsigned personal claim drafts and a catalog-only proposal. Public release and submission await the owner's authorization. The package contains no identity documents, payment addresses, delivery details, or signed recipient confirmations. Authored material is reserved during private preparation, with upstream licenses retained for third-party material and adapted submission formats.

## Remaining actions

The owner and contributors review the prepared declarations and authorize release. Maintainers then determine mathematical scope, proof acceptance, attribution, and priority. Each applicant handles their own claim and identity email, and the prize team records the actual candidate notice and review period. These are external actions required by the official process. [Readiness record](../submission/readiness.md)
