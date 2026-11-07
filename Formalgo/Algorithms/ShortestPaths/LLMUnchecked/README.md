# Shortest paths: the LLM-unchecked proof

LLM-generated; not checked by a human. Only `../Statement.lean` needs review.

The proof is not yet consolidated into a single file. Merging the files needs more RAM than the
machine it was written on has, as the merged sorting proof did, so that is left for later.

- `Proof.lean`: the final theorem, `shortestPathsInEPlusVLogV`.
- `Algorithm.lean`: Dijkstra's algorithm with a Fibonacci heap, as a program.
- `Model.lean`: the same algorithm as a plain Lean model.
- `Heap/`: the Fibonacci heap on the model, and its degree bound.
- `Dijkstra/`: correctness and cost of Dijkstra's algorithm on the model, over `WGraph`, a graph with
  a weight on every pair of vertices. `dist_wg` ties it to the statement's `dist`.
- `Run/`: the program runs as the model says.
- `Machine/`: the commands, compiled to word RAM programs, and input and output.
- `Codes.lean`, `IO.lean`, `Context.lean`: the input and output codes, and the model's data.

The framework in `Machine/` duplicates part of `Sorting/Proof.lean` and uses the same names, so this
proof is not imported from `Formalgo.lean`. To check it:

    lake build Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Proof
