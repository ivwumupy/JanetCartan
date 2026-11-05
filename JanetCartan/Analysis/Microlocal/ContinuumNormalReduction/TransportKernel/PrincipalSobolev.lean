module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.PrincipalSobolev.PrimitiveBounds
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.PrincipalSobolev.L2Bounds

/-!
# Sobolev smoothing for the localized diagonal correction

For the bounded-frequency error following `app:ch_background:eq:bg-real-symbol`,
the localized literal diagonal kernel defines an operator on Euclidean Lebesgue
L². Its Hilbert adjoint is the conjugated kernel with positions and matrix
indices exchanged, retaining the literal frequency normalization.

`exists_localizedDiagonalCorrectionOperator_sobolev_of_primitiveNorms` proves
uniform all-data L²-to-integer-Fourier-Sobolev bounds for both operators. At
budget order `s ≥ 2`, all output orders through `s` are covered with one high
norm of order `s + 2`. The fixed cutoff jets and support volumes enter only
the uniform constant. Smoothness and localized jets are instantiated from
primitive inputs; compact-test density proves the all-data assertion.

The parent construction supplies the stated chart geometry and coverage of
both diagonal slices on the two cutoff supports. These are the geometric
inputs to the primitive producer, not assumed smoothing estimates.
-/
