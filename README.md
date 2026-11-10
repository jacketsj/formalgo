# Formalgo (Formalized Algorithms)
This library is for formalizing algorithmic results. Some examples of statements that have formalized in this library:

- There exists an algorithm running on integer ram that solves sorting of n integers in $O(n \log n)$ time.
- There exists an algorithm running on (transdichotomous) word ram that solves the single-source shortest-path problem on n-vertex m-edge (connected, undirected) graphs in $O(m+n\log n)$ time.
- There exists an algorithm running on real ram that solves the all-pairs shortest-path problem on n-vertex (connected, undirected) graphs in $O(n^3)$ time.

These statements use careful definitions of these computational models.
As an example, here is the first statement, formalized:

```
def sorting : IOSpec (List ℕ) (List ℕ) where
  valid input output := output.Perm input ∧ output.Pairwise (· ≤ ·)

theorem sortsInNLogN_integerRAM :
    ∃ c, IntegerRAM.withAddSub.semantics.SolvableWithin sorting
      fun list => c * list.length * Nat.log 2 list.length + c := /-- O(n log n) --/
  MergeSort.integerRAM sorting fun _ _ => And.intro /-- Proof --/
```

## Principles

This entire library is written with the goal of having easily-aduitable definitions and statements. It does *not* make proving these statements easy, since LLMs can now be used to prove such (challenging) statements.

## Core Overview

The underlying models are carefully defined in `Formalgo/Core`. There are several different abstraction layers worth mentioning. The first layer is what's needed to define our various machines:

- A `Tape` is a memory system for a machine. It is a mapping from addresses (of a given type) to values (of a given type).
- A `ControlFlow` is a finite automaton whose states are `PC` values, and whose characters are `Outcome` values.
- A `Program` is a `ControlFlow` where each `PC` value is prescribed an `Instruction`. Note that an instruction on its own is just a type. It is not intrinsically prescribed meaning.
- `Semantics` prescribe meaning to instructions in the context of a `Tape`. They give an `exec` operation that takes an instruction and a tape, and produces an `Outcome` and an updated `Tape`.
- A `RAM` is a generic, extendable random access machine. This gives a collection of instructions, as well as semantics for those instructions. Importantly, its instructions are for generic address and value types, and they can be “extended”.
- Our `IntegerRAM` and `WordRAM` and other similar types extend `RAM` in order to support random access machines with Integer and fixed-size bit-vectors, respectively (transdichotomous word RAM is handled at a later abstraction layer below).
Our file `Run.lean` allows us to run a program for a given number of steps, for given `Semantics`, one step at a time. It tells us whether or not the program halts in that time.

The second abstraction layer is our `Coding`. That is, encoding and decoding for our machines:

- The basis of this is `Code.lean`, uses `Streams` to encode/decode various highly-expressible types defined in Lean or in MathLib.
- Importantly, we provide default coding for many important types that one would expect to use, such as lists, labelling functions, and things like `SimpleGraph` (which is contained in `Formalgo/Core/Code/Graph.lean`.
- This set of default codes is meant to encapsulate many different valid inputs, work in various different kinds of machine types, and be something that users can trust to encode in a reasonable, expected manner.
- Note, default codes do *not* optimize for constants, nor for ease-of-use. For example, integers on word RAM are encoded in such a way that they can work regardless of how big they are relative to the bit size, at the cost of many extra words (by a constant factor).

The third abstraction layer is used to define an algorithm (something that takes a given “valid” input with an encoding, and produces a “valid” output with a decoding):

- At a high level, an “algorithm” with a given input/output type, a program, and a tape coding of the input/output types. Please note that input/output here refer to *arbitrary lean types*, and it is the tape coding (usually the default coding) that prescribes them meaning in a computational sense. We have two different kinds of “algorithms”, and they are intertwined with a couple other important concepts that we mention first.
- An `IOSpec` defines a map between valid input and output pairs. This is a “problem” in the traditional computer science sense. We note that this is *not* a function, since many problems allow for multiple valid outputs for a given input (e.g. approximation algorithms).
- A `Runnable` takes an `IOSpec` and “algorithm” (in generic sense) and uses `run` to take an input and produce an output (in a given number of steps). Please note that the input and output are *arbitrary lean types*, not pre-encoded or pre-decoded objects. Runnable tells us whether or not the algorithm *solves* the given IOSpec.
- `Algorithm` and `TDAlgorithm` (Transdichotomous Algorithm) take a `Code` and a `Runnable` program. This interfaces an input/output encoding with a program and states whether the algorithm solves the program within $X$ steps.
- `TDAlgorithm` is defined so as its word size scales, $X$ adjusts accordingly. Specifically, it chooses its word size using the size of the input as it would be encoded using natural numbers (i.e. integer RAM). Using some algorithm-specified constants, it either selects a minimum number, or multiples a scale factor by the log of this size value. It then “lifts” the program itself to higher bit-sizes inside `TDWordRAM` (note that programs have to be written with this scaling in mind).

## LLM Usage in development


While LLMs have been helpful to the development of this repository, everything in `Formalgo/Core/` especially has been worked on very carefully. The goal is to have a human-verified and approved way of proving algorithmic statements. Unchecked LLM code (which is not permitted in `Formalgo/Core`) is very clearly marked.
This README.md is entirely human-written.

The proofs of our many statements in `Algorithms` are LLM-generated. The corresponding statements can be found in the `Formalgo/Algorithms` directory. Within the Algorithms directory each problem has its own sub-directory and its statement is at the top level in Statement.lean. This file is human verified. For each problem there is a subdirectory titled *LLM-Unchecked* that contains the proofs of the statements. As the name suggests, these are not carefully checked.


## Credits

The initial version of this library was written by Jack Spalding-Jamieson and Frederick Stock. We welcome other contributors!
