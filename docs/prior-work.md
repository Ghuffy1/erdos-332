# Prior work and related submissions

The source and contribution comparisons below were rechecked on 11 November 2026. The mathematical claim concerns the explicit progression criteria and their consequences. Priority remains subject to independent review.

## Original question and density results

- Erdős and Graham's original discussion asks for weaker hypotheses ensuring bounded gaps in recurrent differences and considers finite intersections, positive density, and reciprocal divergence. The relevant passage is on printed page 50. [Original monograph](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- C. L. Stewart and R. Tijdeman, *On Infinite-Difference Sets*, Canadian Journal of Mathematics 31 (1979), 897–910, establish the positive-upper-density theory, including finite intersections and finite translate covers. Their Theorem 3 gives an earlier realization result for infinite-difference sets with prescribed asymptotic densities. [Published paper](https://doi.org/10.4153/CJM-1979-085-6)
- I. Z. Ruzsa, *On difference sets*, Studia Scientiarum Mathematicarum Hungarica 13 (1978), 319–326, strengthens the density and covering conclusions. Belgikar, Bergelson, Black, and Kruzel restate this as Theorem 1.1 and give the Følner-sequence extension in Theorem 4.1. Applying that extension along long intervals of positive density yields the upper-Banach-density version, including finite intersections. [Ruzsa's original volume](https://real-j.mtak.hu/5479/1/StudScientMath_13.pdf) · [Belgikar et al., version 2](https://arxiv.org/html/2412.01185v2)

## Published sparse settings

- S. Leth, *Some nonstandard methods in combinatorial number theory*, Studia Logica 47 (1988), 265–278, and I. Goldbring and S. Leth, *On supra-SIM sets of natural numbers*, develop sparse sufficient classes. Goldbring–Leth Corollary 4.7 gives an infinite family of translates of a fixed pattern of every finite size inside a supra-SIM set. The manuscript's separated examples have only finitely many translates of each fixed three-point pattern, so they fall outside that class. [Leth](https://doi.org/10.1007/BF00370556) · [Goldbring–Leth](https://arxiv.org/abs/1805.05933)
- Bienvenu, Griesmer, A. N. Le, and T. H. Lê, *Intersective sets for sparse sets of integers*, Ergodic Theory and Dynamical Systems 45 (2025), 1370–1402, supply further sparse settings. Proposition 3.2 gives a zero-upper-Banach-density set of balanced binary integers such that every subset of relative upper density one has full ordinary difference set. Applying their result to every finite tail yields full recurrent difference set. Proposition 6.3 gives generalized admissible-family hypotheses. Its infinite-translation argument also gives recurring pairs by finite pigeonhole. The manuscript's no-recurring-triple examples fail those full family hypotheses. [Published paper, Propositions 3.2 and 6.3](https://doi.org/10.1017/etds.2024.73)
- Syndeticity of recurring prime differences is also prior. Relevant results include Pintz's Theorem 2, the covering argument in Granville–Kane–Koukoulopoulos–Lemke Oliver Section 2, and Huang–Wu Theorem 1.6. These results supply additional established sparse cases. [Pintz](https://arxiv.org/pdf/1305.6289v1) · [Granville et al.](https://arxiv.org/pdf/1410.8198v2) · [Huang–Wu](https://arxiv.org/pdf/1505.00187v3)

## Earlier online examples and discussions

- The Erdős Problem a Day working report gives zero-upper-Banach-density realizations using separated pairs and discusses a finite translate-packing criterion. The manuscript cites that earlier discussion in Section 7. [Working report, Sections 3–4](https://www.erdosproblemaday.com/report/332)
- The Botnet discussion records recurring finite-template conditions, including shifted square prefixes, and explicit sparse examples. The manuscript cites this context in Section 7. [Discussion by jeremy-math-332-worker](https://botnet.com/topics/af009ddc-ed6e-43c1-9bce-a76d1ed84aa0)
- Plasma AI's recurrent-difference note records the explicit sequence `a_n = n(1 + floor(log_2 n))`, whose reciprocal sum diverges while its gaps tend to infinity. The manuscript credits this antecedent in Section 9. [Recurrent difference sets](https://erdosproblems.ai/wiki/research/recurrent_difference_sets)

## Earlier JSP submissions

The open and closed records were checked again before submission.

| PR | Observed status | Relevant comparison |
| --- | --- | --- |
| [384](https://github.com/TheJustinSunPrize/awards/pull/384) | Closed, unmerged, with an author withdrawal | Formalized positive density, upper density, and upper Banach density. The author later described the result as a known partial result and withdrew it under the complete-solution requirement. |
| [1510](https://github.com/TheJustinSunPrize/awards/pull/1510) | Open | Records the baobingzhang formalization as third-party evidence. Its linked pinned source returned HTTP 404 during preparation. Related PR 384 supplies the density-only scope. |
| [2240](https://github.com/TheJustinSunPrize/awards/pull/2240) | Closed, unmerged | The submitted files and text describe scoped components and point to Erdős 276, a different problem from Erdős 332. |
| [3093](https://github.com/TheJustinSunPrize/awards/pull/3093) | Closed, unmerged | The PR text maps JSP-000276 to Erdős 276 and references that different problem. |

The contribution PR links these records for comparison. Their timestamps alone do not establish priority.

## Scope of the proposed contribution

The manuscript proves a bounded-contact condition for long overlapping progression pairs, a finite circular-gap criterion with a non-strict endpoint and explicit bound `2*g*H + 4*C`, and a centered finite-family theorem. It supplies sparse examples to compare these conditions with the earlier classes.

The proposed contribution is the progression mechanism and its precise quantitative and finite-family forms. Established density results, sparse settings, realization methods, template tests, and the elementary harmonic-divergence obstruction receive the prior credit above. The supplied criterion is an explicit answer to the maintained open-ended implication. Its suitability as a complete answer to Erdős 332 is submitted for the prize's mathematical review.

The search supports a proposed contribution for review. It does not establish worldwide priority or exclude inaccessible work.
