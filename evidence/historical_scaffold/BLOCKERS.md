# Release blockers

These conditions are intended to fail mechanically, not live as caveats in a
nominally green repository.

1. **No zero-argument MAP theorem.** The narrowest active constructor,
   `MAPLambdaEndpointSourceWeld.fullUnconditionalMAPEndpoint_of_mapLambda_primitive_sourceLeaves`,
   still takes five analytic inputs. `Challenge.lean` and `Solution.lean` are
   therefore deliberately non-buildable.
2. **Statement bridge not written.** The manuscript calls both logarithmic
   cutoff exponents positive integers. The internal
   `PrimePairEndpoints.AllCenterLocalMAP` quantifies them as unrestricted
   natural numbers. The release statement adds `1 <= B` and `1 <= D`; the
   endpoint must be transported through cutoff monotonicity after it exists.
3. **No source commit.** The directory
   `/Users/computer/Tensor/research/palomar_full_certification_2026-08-29` is not
   a Git checkout. Content hashes are recorded, but they are not a substitute
   for the full 40-character Git commit Palomar records.
4. **Stable migration incomplete.** The current promoted tree is pinned to
   `leanprover/lean4:v4.30.0-rc2`. Only an earlier snapshot was probed under
   stable `v4.32.0`; the current source closure has not been built there.
5. **Linux evaluator unrun.** Comparator, toolchain-matched lean4export, Lean's
   kernel, NanoDa, and Landrun have not run on this candidate.
6. **Release facts need human confirmation.** Responsible maintainer, author
   approval, complete automation/model inventory, cost record, and Apache-2.0
   licensing approval remain explicit `BLOCKED:` fields.
7. **No public immutable release commit.** This directory has no release Git
   `origin` and no submitted SHA. Nothing has been published or submitted.

Run `python3 scripts/check-release-gate.py` to print the current machine-readable
blocker set. The script must exit zero before any expensive Linux verifier run.

