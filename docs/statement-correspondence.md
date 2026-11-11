# Original statement and formal coverage

## Source question

Erdős and Graham ask for conditions that ensure bounded gaps in the differences occurring infinitely often in a set of natural numbers. The catalog mapping is **Erdős 332 = JSP-000276**. The original discussion also considers finite intersections. [Original monograph, printed page 50](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf) · [Problem 332](https://www.erdosproblems.com/332) · [JSP entry](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/problems/catalog-0201-0300.md#JSP-000276)

## Correspondence

| Mathematical item | Formal declaration | Coverage |
| --- | --- | --- |
| Infinitely many ordered pairs with signed difference `d` | `recurring_iff_infinite_pairs` | Equivalence with arbitrarily distant witnesses in an arbitrary subset of the natural numbers |
| Positive integer gap bound for every starting integer | `gapBound`, `syndetic` | Half-open intervals over all integer starts |
| Positive natural-number bound in the maintained statement | `Erdos332Submission.natural_gap_bound` | Explicit conversion of the positive integer bound |
| Original implication with a supplied condition | `Erdos332Submission.erdos_332` | Proves `sufficientCondition A → HasBoundedGaps (recurrentDifferences A)` |
| Two finite progression rows and bounded approximation | `Block`, `points`, `approximates` | Explicit bases, step quotients, lengths, and fixed integer perturbation |
| Escape of minimum bases | `escapes_of_min_bases` | Supplies arbitrarily distant witnesses |
| Actual real hull intersection | `hullOverlap_eq_window` | Proven coordinate identity |
| Finite largest circular gap | `maxGapNumerator_spec`, `maxGapNumerator_min`, `gapCertificate_iff_real_cover` | Least integer gap and equivalent periodic real interval coverage |
| Manuscript Theorem 1.1(1) | `main_bounded_contact` | Positive overlap and bounded contact on infinitely many models imply syndetic recurrent differences |
| Manuscript Theorem 1.1(2) | `main_finite_test` | Exact gap bound `2*g*H + 4*C`, including the non-strict threshold |
| Manuscript Theorem 1.2 | `centered_finite_intersection` | Syndetic intersection for arbitrary finite families of centered pairs |

Declarations without an explicit namespace in the table are in `Erdos332`. `Submission.lean` supplies the concrete predicate in the original open-ended implication. `verification/Challenge.lean` independently expresses recurring differences using the infinite-pair definition and connects the two main sufficient-condition theorems to that statement.

The maintained source is pinned at `4b5e5275a2734adace65d6c0a87e5bb508dc0363`. It explicitly leaves the sufficient condition for the solver to supply and its mathematical suitability to human judgment. [Maintained statement](https://github.com/google-deepmind/formal-conjectures/blob/4b5e5275a2734adace65d6c0a87e5bb508dc0363/FormalConjectures/ErdosProblems/332.lean)

The formal proof permits positive step quotients, which includes the manuscript's step quotients at least two. The centered length inequalities are equivalent to the normalized length assumptions because their denominators are positive. Each family member has its own sequence and limiting circle parameter.

## Additional manuscript results

The manuscript supplies prose proofs of the separated-union classification, exact sparse examples, boundary and order-of-magnitude constructions, positive-density and reciprocal-sum consequences, and the examples concerning finite intersections. These additional results are outside the present machine-checked targets. The release materials identify this boundary explicitly.

## Scope acceptance

Erdős 332 is an open-ended sufficient-condition question. The submitted theorems supply the specified progression criteria, and the manuscript supplies zero-upper-Banach-density examples to explain their mathematical scope. Independent review must determine whether this contribution constitutes a complete answer under the prize's full-problem requirement. This judgment remains pending.

The earlier density-only submission was withdrawn as a known partial result. The proposed contribution addresses different progression hypotheses and includes sparse examples. The prior-work record describes that comparison. [Related submissions](prior-work.md)
