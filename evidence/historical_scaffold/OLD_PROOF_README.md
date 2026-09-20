# Proof snapshot gate

This directory intentionally contains no Lean proof sources.

Populate it only from a clean, committed source revision after that revision
exports the zero-argument theorem
`MAPReleaseEndpoint.zero_argument_map_two_fifteenths`. The theorem must prove
the exact manuscript-faithful type in `Solution.lean`, including positivity of
both cutoff exponents. `scripts/stage-proof-sources.py` performs the copy and
records the source revision and file hashes; it refuses the present uncommitted,
endpoint-free tree.

