module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.Assembly

/-!
# Primitive half-order jets imply modified normal bounds

For `app:ch_background:prop:bg-adjoint`, the actual arbitrary complex normal
is smooth across inverse-chart boundaries, has common compact measurement
support, and its jets commute with the compact spectator integral. The exact
physical-to-cycles normalization is retained. Primitive weighted mixed jets
through `2 * (n + 1)` give position derivative bounds `C * A^2`, uniformly over
smooth regularizers with a fixed scaled-derivative budget. The density-jet premise
of the downstream conversion to `GraphNormalAmplitudeBounds` is discharged.

`PrimitiveJetGeometry.exists_graphNormalAmplitudeBounds_of_isCompact` chooses
the common support box and constant before the amplitude and regularizer.
The modified carrier L² consumer must instantiate the primitive geometry and
amplitude reserves and prove the actual normal identity. No operator estimate
is assumed or asserted here.
-/
