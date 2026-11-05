module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Regularity.Elapsed

/-!
# Regularity of the literal annular source kernels

`elapsedAnnularSourceKernelObservation_regularity` derives joint smoothness,
frequency measurability, all finite external derivative/source-integral
identities, and fixed compact physical supports from the original primitive
elapsed data. The two Boolean indices select the four published physical and
demodulated forward/adjoint kernels. Neither phase is required to be globally
smooth: closed supported sets lie inside their open smooth neighborhoods.

The derivative identity retains the physical Fourier constant and differentiates
the actual integrand, including the output demodulator. Compact source support
supplies integrability and domination at each unrestricted frequency.

Consumer: the quantitative annular kernel-jet assembly, followed by its Sobolev
deduction. Sources: `app:ch_response:lem:energy-carrier-jets` and
`app:ch_response:eq:direct-envelope-profile`. Quantitative decay bounds are the
separate amplitude-jet and source-integration obligations of that assembly.
-/
