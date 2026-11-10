# Real RAM machine: interface for algorithm proofs

LLM-generated; not checked by a human.

Namespace: `Formalgo.Algorithms.ShortestPaths.LLMUnchecked` (the same as the word-RAM `Machine/`,
so `Cmd`, `Exec`, `Runs`, `Runs.*`, `rstep`, ... are all in scope).

Import `Formalgo.Algorithms.ShortestPaths.LLMUnchecked.RealMachine.Rules` to write and prove a
core; import `...RealMachine.Harness` for the final theorem.

## Files (all build, no `sorry`, axioms: propext, Classical.choice, Quot.sound)

| file | contents |
|---|---|
| `Defs.lean` | `DState`, `DCmd`, `DExec`, `DRuns`, `DCmd.seqs`, `DState.input`, `DState.Out`, `CoreSpec` |
| `Rules.lean` | lift from `Exec`/`Runs`, `DRuns.*` rules, bound-free index rules `DRuns.iconst` etc., the `dstep` tactic |
| `CodeDefs.lean` | `Code.prepend`, `Code.Faithful`, `blockCode`, `GraphShape` |
| `Codes.lean` | `Faithful` instances for the repo's codes over `ℝ` (all four shortest-path types resolve) |
| `GraphCode.lean` | the shortest-path codes: `graphShape_sssp/apsp`, lengths, explicit layouts |
| `Raw.lean` | raw real-RAM commands `RCmd`/`RExec`/`RRuns`, compilation, `RExec.run_halts`, tactics `rr`, `rv` |
| `Compile.lean` | `DCmd.toRaw`, `DExec.toRaw` (each unit of cost ≤ 13 real RAM steps) |
| `Reloc.lean`, `Finish.lean` | generic stages (move input into the data memory; move output, write `L ++ Z` back) |
| `Harness.lean` | `solvableWithin_of_boot` (generic, for any input-specific boot + fix-up) |
| `GraphLayout.lean`, `GraphBoot.lean`, `GraphFix.lean` | the boot and fix-up for graph-shaped inputs |
| `GraphHarness.lean` | `solvableWithin_graph`, `solvableWithin_sssp`, `solvableWithin_apsp` |
| `Test.lean` | end-to-end test: a 6-step core writing `[0, 0]` |

## The machine

```lean
structure DState where
  m : Mem          -- index memory ℕ → ℕ (exactly the memory of `Cmd`/`Exec`)
  d : ℕ → ℝ        -- data memory of reals

inductive DCmd
  | idx (c : Cmd)                   -- any word-RAM command, on the index memory (coercion `Cmd → DCmd`)
  | skip                            -- nothing, cost 0
  | dconst (p : ℕ) (v : ℝ)          -- d[m p] := v
  | dcopy (p q : ℕ)                 -- d[m p] := d[m q]
  | dadd (p q r : ℕ)                -- d[m p] := d[m q] + d[m r]
  | dsub (p q r : ℕ)                -- d[m p] := d[m q] - d[m r]
  | dless (x q r : ℕ)               -- m[x] := if d[m q] < d[m r] then 1 else 0
  | toIdx (x p : ℕ)                 -- m[x] := v, when d[m p] = (v : ℝ) for a natural v
  | ofIdx (p x : ℕ)                 -- d[m p] := (m[x] : ℝ)
  | seq (a b : DCmd)
  | ite (l r : ℕ) (t e : DCmd)      -- if m[l] = m[r]
  | loop (l r : ℕ) (body : DCmd)    -- while m[l] = m[r]
```

Data cells are always addressed through index cells: `d[m p]`. To touch data cell `a`, put `a`
in some index cell first (with a `Cmd`). There is no word bound on the real RAM.

`DExec c s k s'` is big-step semantics with cost `k`:
- `idx c` costs exactly what `Exec B c` says, for any `B` (choose `B` per command, e.g. larger than
  every value that command handles); the data memory is unchanged.
- every data instruction costs `1`; `skip` costs `0`;
- `seq` adds; `ite` costs `k + 2` (true) / `k + 1` (false); `loop` costs `k₁ + k₂ + 2` per round
  and `1` on exit — exactly as for `Cmd`.

`DRuns c s Q := ∃ s' k, DExec c s k s' ∧ Q s' k` (continuation style, like `Runs`).

Each unit of `DExec` cost is at most a constant number of real RAM steps once compiled (the
constant is stated in `Compile.lean`; the harness theorem already accounts for it).

## (a) Reusing word-RAM proofs for data-free code

```lean
theorem DExec.ofExec (d) (h : Exec B c m k m') : DExec c ⟨m, d⟩ k ⟨m', d⟩
theorem DRuns.idx  (h : Runs B c s.m fun m' k => Q ⟨m', s.d⟩ k) : DRuns c s Q
theorem DRuns.ofRuns (h : Runs B c m Q') : DRuns c ⟨m, d⟩ fun s' k => s'.d = d ∧ Q' s'.m k
```
So any existing `Exec`/`Runs` lemma (`Runs.loop`, `rstep`, `vread`, the heap and Dijkstra run
lemmas, ...) applies unchanged to `(c : DCmd)`: prove `Runs B c s.m ...` as before and wrap it
with `DRuns.idx`. Different `idx` blocks may use different `B`.

## (b) Data instructions

For single index instructions there are bound-free rules (the word bound is picked for you):
`DRuns.iconst`, `icopy`, `iload`, `istore`, `iadd`, `isub` (needs `m r ≤ m l`), `iless`, each
with the new index memory abstract plus a frame fact. The tactic `dstep` applies the next
`seqs_cons`/`seq`/`seqs_nil` or one of `iconst icopy iload istore iadd iless dconstR dcopyR daddR
dsubR dlessR ofIdxR` and introduces the new memory and its two facts (use `rename_i` to name
them; `toIdxR`, `isub`, `ite`, `loop` are applied by hand). Continuation states look like
`⟨m', s.d⟩`; `try dsimp only at *` reduces the projections.

`Rules.lean` has, for each instruction, a rule with the new memory written as `Function.update`
(`DRuns.dconst`, `dcopy`, `dadd`, `dsub`, `dless`, `toIdx`, `ofIdx`) and a variant with the new
memory abstract plus a frame fact (`DRuns.dconstR`, `dcopyR`, `daddR`, `dsubR`, `dlessR`,
`toIdxR`, `ofIdxR`), mirroring `Runs.constR` etc. Control flow: `DRuns.seq`, `DRuns.seqs_cons`,
`DRuns.seqs_nil`, `DRuns.skip`, `DRuns.ite`, `DRuns.loop` (invariant `P : DState → ℕ → Prop`,
measure `μ`, as `Runs.loop`), `DRuns.mono`.

`toIdx x p` needs a proof `s.d (s.m p) = (v : ℝ)`: data values that are naturals in the code (the
number of vertices, list lengths, vertex positions, the source) are stored exactly as `(v : ℝ)`.
Comparisons of reals go into an index cell with `dless`, then branch with `ite`/`loop` on index
cells. Equality of reals: two `dless`.

## (c) The core's specification

```lean
noncomputable def DState.input (L : List ℝ) : DState :=
  ⟨fun a => if a = 0 then L.length else 0, fun a => L.getD a 0⟩

def DState.Out (s : DState) (L Z : List ℝ) : Prop :=
  s.m 0 = L.length ∧ L.length ≤ s.m 1 ∧ s.m 2 = Z.length ∧
    (∀ i (h : i < L.length), s.d i = L[i]) ∧ ∀ j (h : j < Z.length), s.d (s.m 1 + j) = Z[j]

def CoreSpec [Code I ℝ] [Code O ℝ] (core : DCmd) (spec : IOSpec I O) (t : I → ℕ) : Prop :=
  ∀ x : I, DRuns core (.input (Code.encode x)) fun s k => ∃ y : O, spec.valid x y ∧
    s.Out (Code.encode x) (Code.encode y) ∧ k ≤ t x ∧ (Code.encode y).length ≤ t x
```
In words: the core starts with the input code `L = Code.encode x : List ℝ` in data cells
`[0, ℓ)`, `ℓ` in index cell `0`, and **every other index and data cell `0`**. It must end with
- index cell `0` still `ℓ`, and data cells `[0, ℓ)` still holding `L` (do not overwrite the
  input; copy it if you need scratch);
- the output code `Z = Code.encode y` in data cells `[m 1, m 1 + m 2)`, with `ℓ ≤ m 1` and
  `m 2 = Z.length` (anywhere after the input; the harness moves it);
- cost at most `t x`, and `Z.length ≤ t x`.
Everything else (other index cells, other data cells) may be left as garbage.

## The harness theorems (in `GraphHarness.lean`)

```lean
theorem solvableWithin_sssp
    {spec : IOSpec (Σ n, Σ G : SimpleGraph (Fin n), (G.edgeSet → NNReal) × ℕ)
      (Σ n, Fin n → NNReal)} {core : DCmd} {t} (hcore : CoreSpec core spec t) :
    RealRAM.withAddSub.semantics.SolvableWithin spec
      fun x => 3850 * (t x + (Code.encode (Value := ℝ) x).length) + 3850

theorem solvableWithin_apsp
    {spec : IOSpec (Σ n, Σ G : SimpleGraph (Fin n), G.edgeSet → NNReal)
      (Σ n, Fin n → Fin n → NNReal)} {core : DCmd} {t} (hcore : CoreSpec core spec t) :
    RealRAM.withAddSub.semantics.SolvableWithin spec
      fun x => 3850 * (t x + (Code.encode (Value := ℝ) x).length) + 3850

-- generic: any graph-shaped input with faithful codes
theorem solvableWithin_graph {I O} [Code I ℝ] [Code O ℝ] [Code.Faithful I ℝ] [Code.Faithful O ℝ]
    (c : ℕ) (hshape : ∀ x : I, GraphShape c (Code.encode x)) {core : DCmd} {spec} {t}
    (hcore : CoreSpec core spec t) :
    RealRAM.withAddSub.semantics.SolvableWithin spec
      fun x => 3850 * (t x + (Code.encode (Value := ℝ) x).length) + 3850
```
`Harness.lean` has the fully generic `solvableWithin_of_boot` (any input type, given an
input-specific raw boot and `DCmd` fix-up with their specs), time `(60 cb + 250) (t x + ℓ x + 1)`.

Lengths (`GraphCode.lean`): `length_encode_sssp_input G w s : ... = n + 3 * G.edgeSet.ncard + 4`,
`length_encode_apsp_input G w : ... = n + 3 * G.edgeSet.ncard + 3`, and
`length_encode_sssp_output`, `length_encode_apsp_output` (`n + 2`, `n * (n + 1) + 2`).
So `t x ≤ c' (E + V log V) + c'` (resp. `V ^ 3`) gives the target bound with `c = 3850 c' + …`.

### The input code layout (both inputs; exact lemmas in `GraphCode.lean`)

`encode_sssp_input G w s`, `encode_apsp_input G w`, `encode_sssp_output f`,
`encode_apsp_output f`, with `adjList G v` (neighbours of `v` as values, increasing),
`edgeList G` (the edges in weight order), `blockCode b = b.length :: b`.


`Code.encode ⟨n, G, w, s⟩ = n :: n :: blocks ++ E :: ws ++ [s]` (APSP: no `[s]`), all naturals as
exact reals, where for each vertex `v = 0, …, n-1` in order the block is `deg v` followed by the
neighbours of `v` in increasing order (as their values `< n`), `E` is the number of edges, and
`ws` lists the edge weights (as reals) in the order of `Code.sym2LinearOrder` on `Sym2 (Fin n)`
(lexicographic on the sorted pair `(min, max)`). The output `⟨n, f⟩ : Σ n, Fin n → NNReal` is
`n :: n :: [f 0, …, f (n-1)]`; `⟨n, f⟩ : Σ n, Fin n → Fin n → NNReal` is
`n :: n :: (row 0) ++ … ++ (row (n-1))` with `row u = n :: [f u 0, …, f u (n-1)]`.

## Name clashes

`Raw.lean` defines `rops`, `ROp`, `RInstr`, `semR`, `RMem`, `RLine`, `RCmd` in this namespace.
`Sorting/LLMUnchecked/RealRAM.lean` has some of the same names in `Formalgo.LLMUnchecked`; do not
open both namespaces.

## How it works (for reference)

Physical layout: real RAM cells `0..7` are scratch, index cell `a` is cell `2 a + 8`, data cell `a`
is cell `2 a + 9`, so index instructions never touch data. The standard tape has the input code
from cell `0`; a graph-specific boot finds the end of the input with three registers (it tags the
first vertex's neighbours and turns degrees into forward pointers), copies it away, a fix-up
restores it, and the generic part moves it into the data memory, zeroes the rest, runs the core,
writes `L ++ Z` back to cells `[0, ℓ + |Z|)`, and halts.
