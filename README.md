# Solvers for nonogram puzzles.

There are two solving algorithms.

## Iterated deduction
One solver simply applies the elementary deductions that humans would apply:
 - Mark squares that must be filled or empty in all remaining possible configurations.
 - Eliminate configurations that conflict with marked squares.
 
This repeats until there's no change in the truth values. This technique never makes guesses, but it is surprisingly effective.

## SMT solving

This is using TNT to kill a fly. It uses the `z3` constraint solver to solve the entire puzzle. It encodes the entire puzzle in an SMT formula and
prints the result.
