module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialBuffers.Geometry
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialBuffers.Primitives

/-!
# Coefficient-independent radial buffers and their primitive root controls

`exists_finite_radial_initial_buffers` constructs a finite cover of the actual
radial source closure, suitable for transporting the original flow.
`fieldRoot_radial_buffer_primitives` derives the mask constructor's primitive
inputs from the original uniform geometry constructor's fixed state controls
and global root conclusion. The parent retains assembly with flow transport,
the actual physical masks and the uniform interior gap
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:thm:no-return`).
-/
