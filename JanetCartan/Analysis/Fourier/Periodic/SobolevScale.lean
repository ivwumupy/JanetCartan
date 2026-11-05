module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Density
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.WeakDerivative
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.DifferenceQuotient
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Distribution

/-!
# Actual Fourier Sobolev spaces on the normalized unit torus

For `app:ch_background:prop:bg-inverse`, the public construction comprises:

* `periodicSobolevLevel`: nested subspaces of real L² defined by summability;
* `periodicSobolevScale`: a `GradedScale` with level zero equal to L² and norms
  equal to `periodicSobolevNorm` on smooth representatives;
* `PeriodicSobolevSpace`: complete real inner product spaces with those norms,
  compatible inclusions, and an isometric identification of level zero with L²;
* smooth density in every Sobolev norm, proved by finite Fourier approximation;
* weak and iterated distributional derivative characterizations, with bounded
  coordinate derivatives and the normalized unit-torus `2π` Fourier symbol;
* the H¹ characterization by uniformly bounded translation difference quotients,
  including an explicit converse norm estimate;
* `PeriodicSobolevNegativeOne`: the continuous dual of H¹, its injective L²
  inclusion, and compatible transpose extensions of self-adjoint L² operators;
* bounded distributional derivatives L² → H⁻¹, whose L² representatives are
  exactly the weak derivatives used in the integer Sobolev characterization.

All dimensions, including zero, and all finite-dimensional real Hilbert
codomains are allowed. The operator extension theorems take compatible bounded
H¹ restrictions as inputs; elliptic preservation for the paper's particular
normal operator belongs to the subsequent inverse construction.
-/
