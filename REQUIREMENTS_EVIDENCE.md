# Current requirements checked on 2026-09-20

Official sources:

- https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md
- https://github.com/PalomarRegistry/PalomarSubmission#required-source-layout
- https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json

The verifier accepts released and RC Lean versions at or above v4.28.0, with
Mathlib pinned to the exact matching toolchain. Stable v4.32.0 is the template's
choice, not a mandatory migration for this proof. This release retains the
verified v4.30.0-rc2/Mathlib 0f9072dd907c6e2e4264ab241a049cab50137f7c pair.
`git ls-remote` resolved lean4export's v4.30.0-rc2 tag to
12581a6b680d8478175596338eb2d53383a323e3 and Verso's matching tag to
0bce2769d753e69fe092f4f2b02cb1428d6287a6.

The public repository is `https://github.com/jconorgrogan/prime-minor-arcs-2-15`.
Comparator, Lean's kernel, and independent NanoDa are recorded as passed in
[RELEASE_STATUS.md](RELEASE_STATUS.md).

The PalomarSubmission source was pinned during this audit at
3561d237dcc4b28482558ad28a64d767d7cc8615. Its verification-profile.json pins
Comparator 575674928e239f5bc452aab72d1dd7b0f1326494,
Landrun 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4, and
NanoDa 68d5ca9db226849b41a6fff59d796ff19d0a8840. The Linux release run used
these pins and the matching exporter commit. The official standard runner is
x86_64 Ubuntu 24.04 with at least 14 GiB memory and 20 GiB free workspace. The
local ARM Linux run is additional evidence.
