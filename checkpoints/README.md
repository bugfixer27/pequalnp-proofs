# Partial proofs of L-meta-652 and L-meta-519

This branch records research in progress under the GitHub handle bugfixer27. Both original project statements remain open in this checkpoint.

## L-meta-652

Lean proves that the three outputs require at least 11 gates and can be computed with 15. The remaining sizes are 11 through 14. The construction is in [Upper.lean](L-meta-652/Upper.lean). The unrestricted lower-bound theorem is `unrestricted_eleven` in [Search.lean](L-meta-652/Search.lean). The file can be checked from this repository’s configured Lean project using `lake env lean ../checkpoints/L-meta-652/Search.lean` in the `lean` directory.

A separate computer-assisted argument reaches 15 using independently verified SAT certificates. [Proof.txt](L-meta-652/Proof.txt) explains the mathematical reduction and how to reproduce the certificate checks. A complete Lean verification of the 15-gate minimum remains open.

## L-meta-519

[Cut.lean](L-meta-519/Cut.lean) and [Pair.lean](L-meta-519/Pair.lean) contain partial results for the graph edge function, including a conditional gate-saving bound after deleting the endpoints of an edge. The lower bound for all graphs in the posted statement remains open.
