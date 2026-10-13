# Harrison Decision Procedure

`hdp` is a Lean 4 tactic for elementary number theory, based on John Harrison's paper *Automating elementary number-theoretic proofs using Gröbner bases*. It searches for witnesses to divisibility, congruence, and coprimality statements, then constructs proofs checked by Lean.

```lean
import HDP.Tactic

example (a b c : Int) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  hdp
```

Now, the tactic could successfully prove all examples from Harrison's paper, with the exception of one non-linear equation elimination extension. It is also tested and succeed on a few examples from VerusLean.

It uses **Lean 4.34.0** and currently has no external library dependencies.

## How it works

1. Rewrite divisibility and congruence as existential equations, and add facts about remainders and GCDs.

2. Translate hypotheses and goals into polynomials. Use auxiliary variables to combine multiple goal equations into one ideal-membership problem.

3. Run Buchberger's algorithm over rational coefficients and extract witnesses with integer coefficients.

4. Substitute the witnesses and use Lean's `grind` tactic to prove the remaining equations.

This is a research prototype. It implemented features including divisibility, remainder arithmetic, Bézout coprimality, GCD reasoning, constant powers, and multiple existential witnesses and equations. 

However, it only supports `Int` currently, and normalized goal equations must be linear in the existential witnesses. Nonlinear witness elimination is not yet supported.

## Files

| Path                                 | Description                                     |
| ------------------------------------ | ----------------------------------------------- |
| `HDP/Data/`                          | Polynomial arithmetic and Gröbner basis search  |
| `HDP/Tactic/`                        | Preprocessing, problem construction, and proofs |
| `HDP/Tactic.lean`                    | The `hdp` tactic entry point                    |
| `tests/harrison_paper_examples.lean` | Examples from Harrison's paper                  |
| `tests/Integer_ring.lean`            | Verus integer-ring examples                     |
| `tests/simple_tactic.lean`           | Some basic tactic examples                      |
| `tests/data_test.lean`               | Polynomial computation examples                 |

The implementation of Gröbner basis algorithm builds on Cayden Codel's [modular tactic in VerusLean](https://github.com/ccodel/verus-lean/tree/modular/VerusLean/Tactic).
