# Benchmarks

## Four ways to decide a propositional question

`methods.hy` gives the same problems to the four methods hylogic has:
truth tables, resolution, DPLL (with the Tseitin transformation) and Z3
(through the SMT-LIB export). The problems are random 3-SAT formulas with
4.26 clauses per variable, where they are hardest, and pigeonhole problems,
n + 1 pigeons in n holes, which are unsatisfiable and known to be hard for
resolution. Every method had 20 seconds per problem, and all methods that
finished gave the same answer on every problem. Run on 14 October 2026,
Apple Silicon, Python 3.12, Hy 1.3.1, z3-solver 5.1.0.

```
problem                truth table  resolution        DPLL          Z3
3-SAT n=6 #0               5.5 ms      3.5 ms      0.8 ms     43.2 ms   unsat
3-SAT n=6 #1               5.7 ms      5.1 ms      0.8 ms      0.8 ms   sat
3-SAT n=6 #2               6.1 ms      9.2 ms      1.4 ms      0.8 ms   sat
3-SAT n=10 #0            149.2 ms    111.7 ms      2.6 ms      1.4 ms   sat
3-SAT n=10 #1            155.4 ms     89.0 ms      2.9 ms      1.3 ms   sat
3-SAT n=10 #2            151.8 ms    111.8 ms      2.3 ms      1.1 ms   sat
3-SAT n=14 #0           3336.5 ms   1048.3 ms      5.6 ms      1.3 ms   sat
3-SAT n=14 #1           3337.0 ms    508.5 ms      3.8 ms      1.3 ms   sat
3-SAT n=14 #2           3073.2 ms    842.2 ms      3.9 ms      1.3 ms   sat
3-SAT n=20 #0                   -   9913.5 ms     10.4 ms      1.4 ms   unsat
3-SAT n=20 #1                   -   4011.5 ms      9.3 ms      1.4 ms   unsat
3-SAT n=20 #2                   -   4251.6 ms      8.0 ms      1.5 ms   unsat
3-SAT n=40 #0                   -       >20 s     68.6 ms      2.4 ms   sat
3-SAT n=40 #1                   -       >20 s     52.3 ms      2.1 ms   sat
3-SAT n=40 #2                   -       >20 s     42.9 ms      2.2 ms   sat
3-SAT n=80 #0                   -           -    899.9 ms      3.8 ms   sat
3-SAT n=80 #1                   -           -   1043.7 ms      3.5 ms   sat
3-SAT n=80 #2                   -           -   1738.7 ms      4.2 ms   unsat
3-SAT n=160 #0                  -           -       >20 s     44.1 ms   unsat
3-SAT n=160 #1                  -           -  16825.0 ms      9.0 ms   sat
3-SAT n=160 #2                  -           -       >20 s     93.6 ms   unsat
pigeonhole 4->3          229.2 ms    144.6 ms      0.8 ms      0.8 ms   unsat
pigeonhole 5->4                 -       >20 s      5.3 ms      1.1 ms   unsat
pigeonhole 6->5                 -       >20 s     40.6 ms      1.6 ms   unsat
pigeonhole 7->6                 -           -    416.3 ms      3.7 ms   unsat
pigeonhole 8->7                 -           -   4642.9 ms     18.3 ms   unsat
```

A dash means the method was not tried at that size.

What this decided:

- **Arguments use truth tables up to 10 propositions** (about 0.15 s), and
  DPLL beyond that. A truth table takes over 3 s at 14 propositions, but it
  finds the first counterexample in table order, which is easier to follow.
- **DPLL stays in milliseconds up to about 40 variables**, takes 1 to 2 s at
  80, and runs out of time at 160. It has no clause learning, which is what
  makes solvers like Z3 fast.
- **For larger problems, export to a real solver.** Z3 decided every
  problem in milliseconds. `check-with-z3` does this when z3-solver is
  installed.
- **Resolution is the wrong tool for propositional search.** It is slower
  than DPLL at every size and fails on pigeonhole problems as small as 5
  pigeons in 4 holes, as Haken proved it must (1985). It stays the method
  for first-order proofs, where it prints a proof DPLL cannot give.
