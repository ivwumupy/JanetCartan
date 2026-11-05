module

public import JanetCartan.Iteration.RevisedConvergence.Restoration

/-!
# Revised global convergence and restoration

The conditional §18 deductions of `paper-v2.tex`: the literal revised decay
along one adaptive staircase gives one smooth global sum and the exact metric
on the fixed core, followed by restoration with the same `sρ` and coordinate
matrix.  The actual compatible increment and Bernstein producers are separate;
this module does not assert the unconditional existence theorem of `Main`.
-/
