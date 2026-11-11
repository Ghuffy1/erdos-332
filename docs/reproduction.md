# Reproduction of the selected proof

The selected proof commit is `6d65e28f986b8434d9448e6e4ba73e7ddd17ef43` on `main` in `Ghuffy1/erdos-332`.

## Environment

- Lean `4.34.1`, pinned by `lean-toolchain`.
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- All remaining package revisions pinned by `lake-manifest.json`.
- Python 3.10 or newer for the optional evidence-collection helper. The direct proof-checking commands below use Lean and Lake.

## Obtain the exact revision

The commands below select the exact formal-proof revision.

```sh
git clone https://github.com/Ghuffy1/erdos-332.git
cd erdos-332
git checkout 6d65e28f986b8434d9448e6e4ba73e7ddd17ef43
lake exe cache get
```

The dependency cache is an optimization. The package sources remain pinned by the manifest.

## Direct checks

```sh
lake build
lake env lean verification/Audit.lean
lake env lean verification/Challenge.lean
lake env leanchecker --fresh --verbose Submission
```

The default build includes both `Erdos332` and `Submission`. The audit prints the submitted target statements and all local theorem axiom dependencies. The challenge file connects independently stated infinite-pair recurrence and a natural-number gap bound to the proof. The fresh replay checks the compiled environment using the kernel bundled with the pinned toolchain.

## Evidence helper

```sh
python scripts/verify.py --kernel-replay
```

The helper additionally checks committed file bytes, records dependency revisions, rejects unexpected axiom names, and preserves commands, exit codes, durations, and full logs in `.verification-run/`.

## Mathematical manuscript

The checked PDF and its typesetting source are under `paper/`. The PDF checksum is recorded in `submission/source-record.json`. The manuscript was typeset with Tectonic 0.17.0. Its content can be regenerated from the source with

```sh
tectonic paper/recurring_differences.tex
```

Rebuilding can change PDF timestamps and corresponding bytes. Reviewers can use the exact pinned PDF artifact for citation and comparison.
