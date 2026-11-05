module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.FixedBall
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Weights
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.SourceBounds

/-!
# One-high interpolation of physical amplitude derivatives

For Step 3 of `app:ch_regular_base:thm:actual-calculus` and
`app:lem:elementary-interpolation-jets` in `paper.tex`:

* ordered coordinate derivatives and Fréchet norms are compared explicitly;
* physical budgets bound the existing `cNorm` on any fixed ball;
* budgets at `μ` and `μ+s` interpolate to `μ+j`, with exponent `j/s`, including
  both endpoints and uniformly in frequency;
* frequency-only weights factor out exactly;
* finite source Fréchet bounds, and hence the source premises of the L²
  realization on compact smooth tests, follow from the physical budget.

Global coordinate budgets let us translate the proved unit-ball interpolation
estimate. Thus the interpolation constant does not even require the fixed-box
support hypothesis used by the operator realization.
-/
