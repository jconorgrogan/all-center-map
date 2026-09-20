# Frozen MAP proof sources

This directory contains the 1,861 Lean modules in the MAP endpoint's transitive
import closure. The source hashes are recorded in
[`proof-snapshot.json`](../proof-snapshot.json). One module has a recorded
[proof-term optimization](../PROOF_OPTIMIZATION.md); the other 1,860 preserve
the authoring snapshot byte-for-byte.

The release root is `MAPReleaseEndpoint.zero_argument_map_two_fifteenths`.
The separately checked Guth–Maynard root is
`GuthMaynardActualEndpointWeakTheta.actual_guthMaynardTheorem11`.
See [verification scope and evidence](../VERIFICATION.md).

An imported module may also contain historical conditional theorems or
proposition interfaces. Inclusion does not mean every named source paper has
been formalized, nor that every declaration is an advertised release target.
The exact statement and dependency closure of each selected theorem determine
what has been checked.
