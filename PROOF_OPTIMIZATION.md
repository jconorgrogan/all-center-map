# Compact algebraic proof, unchanged theorem

`BHPCanonicalAllCharacterLiteral.lean` previously used `ring` to prove a product
raised to the fourth power and a rearrangement of three factors. Those calls
expanded large local expressions into a dense polynomial proof. The final
theorem's compiled proof had 16,414,694 distinct expression nodes, while its
three supporting declarations had 19,659, 5,312, and 2,233.

The release replaces exactly those two tactic steps with `mul_pow` and `ac_rfl`.
The theorem statements, names, hypotheses, constants, imports, and all other
source text are unchanged. The pinned Lean compiler accepted the candidate and
reported only `propext`, `Classical.choice`, and `Quot.sound`.

On the authoring machine the compiled module shrank from 526,211,976 bytes to
1,230,768 bytes. Candidate compilation took 48.0 seconds. This is a measurement
of the candidate compilation, not a like-for-like Linux build timing comparison.
The optimized module subsequently compiled from source in the Linux build in
6.0 seconds; the original Linux attempt was stopped after more than 14 minutes.

- [Exact two-step diff](evidence/proof-optimization/bhp.diff)
- [Candidate compilation record](evidence/proof-optimization/candidate-compile.json)
- [Compiler output and resource measurements](evidence/proof-optimization/candidate-compile.txt)
- [Baseline proof-expression counts](evidence/proof-optimization/baseline-proof-size.txt)

The original authoring development is untouched. `proof-snapshot.json` records
both hashes for the changed module. The optimized module compiled from source
in the Linux release build.
