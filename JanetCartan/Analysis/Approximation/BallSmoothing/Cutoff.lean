module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Cutoff.Bounds

/-!
# The actual uniformly controlled cutoff for ball smoothing

`unitCutoff n R` is smooth, real, between zero and one, equal to one on the
closed unit ball, and compactly supported in the radius-`1+1/(4R)` ball for
every `R ≥ 1`. One fixed support lies in the closed ball of radius two.
The same numerical constants, chosen before `R`, bound all pointwise jets
and the global native `cNorm` by exactly one power of `R` per derivative.

Consumer: the inward finite-moment formula
`app:ch_regular_base:eq:extension-radial-formula`, and its low estimate in
`main:lem:smoothing`.
-/
