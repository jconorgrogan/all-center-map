# Verification requirements

Requirements checked on September 23, 2026 against
[PalomarSubmission at `1703d7babd984ccc3831cdf89c28221abe34808f`](https://github.com/PalomarRegistry/PalomarSubmission/tree/1703d7babd984ccc3831cdf89c28221abe34808f)
and [PalomarPolicy at `792c7c0b9e798bd02719e795ef11fa2b5929e067`](https://github.com/PalomarRegistry/PalomarPolicy/tree/792c7c0b9e798bd02719e795ef11fa2b5929e067).

The project pins Lean `v4.35.0-rc2`, the current minimum in Palomar's
[toolchain contract](https://github.com/PalomarRegistry/PalomarSubmission/blob/1703d7babd984ccc3831cdf89c28221abe34808f/toolchains.json),
and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The Lean release resolves to commit
`11acb17ec6b07a8f9e9173e6845197929540936b`.

Comparator, `leanexport`, Lean's checker, NanoDa and con-ron are bundled with
that Lean toolchain. Palomar records the toolchain commit and the binary
digests; it no longer selects separate Comparator or exporter revisions.
The sandbox is bubblewrap `v0.12.0`. The standard verification profile uses
x86_64 Ubuntu 24.04, at least 14 GiB host memory, 20 GiB free workspace and a
19,800-second execution budget.

The [public workflow](.github/workflows/release.yml) invokes Palomar's complete
reusable verifier at the pinned commit above, with `mode: full` and the exact
source SHA. Its `mechanical-report-map435preflight` artifact contains
`mechanical-report.json`. A successful full report has `status: pass` and
`stage: complete`, and binds the source repository, commit and
`comparator.json` path. This report is the required preflight evidence for
submission under the [current intake protocol](https://submit.palomar-registry.org/llms.txt).

The selected layout is the repository root: `lean-toolchain`,
`lakefile.toml`, `lake-manifest.json`, `formalization.yaml`,
`comparator.json`, `Challenge.lean`, `Solution.lean` and `LICENSE`.
The Challenge uses the permitted Mathlib statement surface; the proof is in
`Proof/`. Submitted dependencies use public GitHub repositories and full
commit pins.

The current three-target Lean `v4.35.0-rc2` build and standard-axiom audit
passed on macOS ARM (10,797 jobs). [VERIFICATION.md](VERIFICATION.md) links
that evidence and distinguishes it from the historical Linux runs and the
official hosted mechanical report required for submission.
