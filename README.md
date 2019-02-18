# Solvers for nonogram puzzles.

There are two solving algorithms.

## Iterated deduction
One solver simply applies the elementary deductions that humans would apply:
 - Mark squares that are filled or empty in all remaining possible configurations.
 - Eliminate configurations that conflict with marked squares.
 
This repeats until there's no change in the truth values. This technique never makes guesses, but it is surprisingly effective.

## SMT solving

This technique uses the [z3 constraint solver](https://github.com/Z3Prover/z3) to solve the entire puzzle, which it encodes as an SMT formula and prints a satisfying assignment.
