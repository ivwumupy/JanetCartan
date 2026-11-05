module

public import JanetCartan.Analysis.Fourier.Periodic.Cutoff.Vector

/-!
# Smooth real periodic Fourier multipliers

The fixed real-even cutoff and the finite-sum operator `periodicCutoff` implement the
Fourier cutoff used in `main:lem:smoothing` and Appendix B of paper.tex. The imported
API proves smoothness, reality, real linearity, the exact multiplier identity, support
below `2R`, and reproduction of continuous fields with Fourier support below `R`.
Quantitative smoothing and tail estimates are separate from these algebraic identities.
-/
