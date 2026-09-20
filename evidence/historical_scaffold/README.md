# All-center MAP Palomar release candidate

This directory is a **fail-closed release candidate**, not a Palomar
submission. It packages only the proposed first entry,
`AllCenterMAP.map_two_fifteenths`, corresponding to manuscript Theorem 1.1.
The prime-pair consequences, Q4, density-one, Goldbach, and decoder results are
outside this Comparator entry.

## Why it is blocked

The promoted Lean tree has conditional constructors ending in
`PrimePairEndpoints.FullUnconditionalMAPEndpoint`, but it does not export a
zero-argument theorem proving the MAP statement. `Challenge.lean` therefore
ends at an intentionally unresolved identifier, and `Solution.lean` imports an
intentionally absent `MAPReleaseEndpoint` module. Neither placeholder uses an
assumption or an admitted proof. A plain `lake build` must fail.

There are two further hard blockers:

- the current source tree is not in a Git repository, so no immutable source
  commit exists for provenance or submission;
- the current full tree has not been replayed under this candidate's stable
  Lean `v4.32.0` pin or through Linux Comparator/NanoDa/Landrun.

`formalization.yaml` also retains explicit `BLOCKED:` fields for maintainer
approval, author endorsement, automation inventory, and cost accounting.

## Exact activation path

1. Prove a theorem with no hypotheses whose conclusion is the literal MAP
   endpoint. Add a release bridge named
   `MAPReleaseEndpoint.zero_argument_map_two_fifteenths`; it must include the
   manuscript's positive cutoff conditions `1 <= B` and `1 <= D`.
2. Put the substantive source tree in a clean public-style Git repository and
   commit it. From this directory run:

   ```sh
   python3 scripts/stage-proof-sources.py /absolute/path/to/committed/map
   ```

   The script copies only the transitive local import closure and writes
   `proof-snapshot.json` with the source remote, full commit SHA, and every file
   hash. It does not edit the source tree.
3. Replace the unresolved Challenge proof only after step 1. Palomar normally
   uses one deliberate Challenge hole so Comparator can test the independent
   Solution. That protocol hole is permitted only after the real zero-argument
   Solution exists; it must never be used to conceal the present blocker.
4. Resolve every `BLOCKED:` metadata field, confirm the proposed Apache-2.0
   repository licence with the author, and update the manuscript's machine
   certification paragraph to name the exact proved declaration and checks.
5. Initialize this directory as the release repository, set its public GitHub
   `origin`, commit, and leave the worktree clean. Do not use a branch or tag as
   the submission identifier.
6. On a fresh Linux host with Git, Go, Ruby, Rust/Cargo, Python 3, and Landlock,
   run:

   ```sh
   ./scripts/verify-linux.sh
   ```

   This checks the release gate, static layout, metadata, stable Lean build,
   proof-side forbidden tokens, axiom report, Comparator statement identity,
   Lean kernel acceptance, and independent NanoDa replay under Landrun.
7. Only after that succeeds, commit any generated manifest corrections, rerun
   from a clean clone at the final full 40-character SHA, and review the exact
   repository, SHA, and `comparator.json` path. Publication and submission are
   separate actions and are not performed by this candidate.

## Stable toolchain choice

The candidate follows the current official template at commit
`128a6c5ce5f48622e69927ccd639cbff401022e8`:

- Lean `leanprover/lean4:v4.32.0`;
- Mathlib tag `v4.32.0`, resolved in the committed manifest to
  `81a5d257c8e410db227a6665ed08f64fea08e997`;
- the template's immutable Comparator, lean4export, NanoDa, and Landrun pins in
  `scripts/verify-comparator.sh`.

Palomar currently accepts released or RC Lean versions at or above `v4.28.0`.
The stable template line is the fastest low-risk target because the repository
already has evidence that an earlier MAP snapshot built under `v4.32.0`.
That earlier probe is not evidence for the current 558-file source snapshot.

See `REQUIREMENTS_EVIDENCE.md`, `MANUSCRIPT_ALIGNMENT.md`, `BLOCKERS.md`, and
`PROVENANCE.md` for the audit trail.

Submission form, when and only when the release is ready:
<https://submit.palomar-registry.org/>.

