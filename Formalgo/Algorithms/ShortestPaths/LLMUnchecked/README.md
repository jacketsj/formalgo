# Shortest paths: the LLM-unchecked proof

LLM-generated; not checked by a human. Only `../Statement.lean` needs review.

The proof is not yet consolidated into a single file. Merging the files needs more RAM than the
machine it was written on has, as the merged sorting proof did, so that is left for later.

- `Proof.lean`: the final theorem, `shortestPaths_wordRAM`, for any spec that accepts the
  shortest-path distances (`AcceptsDist`, stated with Mathlib's walks only, so the proof does not
  import the statement). `../Statement.lean` applies it to `singleSourceShortestPaths`. The
  program first rewrites the input as an edge list (`Run/RunConv.lean`), runs the core on it, and
  puts `n` before the core's output.
- `EInput.lean`: `Input`, the statement's input type; the edge-list input the core reads; and
  `toE`, which turns the input into it.
- `InputCode.lean`: the statement's codes on the tape, and how they match the edge list.
- `Algorithm.lean`: Dijkstra's algorithm with a Fibonacci heap, as a program.
- `Model.lean`: the same algorithm as a plain Lean model.
- `Heap/`: the Fibonacci heap on the model, and its degree bound.
- `Dijkstra/`: correctness and cost of Dijkstra's algorithm on the model, over `WGraph`, a graph with
  a weight on every pair of vertices. `dist_toE` ties it to the distance in `AcceptsDist`.
- `Run/`: the program runs as the model says.
- `Machine/`: the commands, compiled to word RAM programs, and input and output.
- `Codes.lean`, `IO.lean`, `Context.lean`: the edge-list input and output codes, and the model's
  data.

The framework in `Machine/` duplicates part of `Sorting/Proof.lean`, in its own namespace. To check
the proof and the statement:

    lake build Formalgo.Algorithms.ShortestPaths.Statement
