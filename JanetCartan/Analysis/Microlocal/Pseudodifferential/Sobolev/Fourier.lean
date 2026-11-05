module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Basic
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Interpolation
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.FirstDerivatives
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.IntegerDerivatives

/-!
# Euclidean Fourier Sobolev estimates

Quantitative Fourier Sobolev membership and norms for the scalar L² data in
`app:ch_regular_base:eq:fio-input` and the Fourier interpolation following
`app:ch_regular_base:eq:graph-derivative-transfer`.

The weight is `(1 + ‖ξ‖²)^(s/2)`, with coordinate derivative symbol `2π i ξⱼ`.
`MemFourierSobolev` accompanies the real-valued `fourierSobolevNorm`, whose
definition uses `ENNReal.toReal`. The assembled API provides:

* exact order-zero normalization and monotonicity of membership and norms;
* equivalence with Mathlib's `TemperedDistribution.MemSobolev` on L² classes;
* interpolation between orders zero and `s`, including
  `H^(1-k/s) ‖u‖_k ≤ H ‖u‖_0 + ‖u‖_s` for `0 ≤ k ≤ s` and `H ≥ 0`;
* first-derivative characterization at order `s + 1` for `s ≥ 0`, with norm
  comparison constants `1` and `1 + 2πd`;
* characterization at every natural order `n` by a finite family of actual
  distributional coordinate derivatives, including the input at the empty word.
  If `A` is the sum of their L² norms, the bounds are
  `‖u‖_n ≤ 2^n A` and `A ≤ (1 + 2πd)^n ‖u‖_n`.

Both derivative characterizations construct representatives from membership
and establish membership from the derivative family. Order zero, dimension
zero, and the interpolation endpoints are included. These are the Sobolev
ingredients for the PDO estimates; operator estimate assembly belongs to the
consuming Sobolev modules.
-/
