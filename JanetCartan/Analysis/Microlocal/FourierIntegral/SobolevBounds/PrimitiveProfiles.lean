module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.FiniteCharts

/-!
# Normalized primitive profiles for the strong graph estimate

Step 3 of `app:ch_regular_base:thm:actual-calculus`, before
`app:ch_regular_base:eq:fio-input`:

* `exists_primitiveProfile_inputs` constructs the actual profiles on one
  buffered normalized ball.
* `exists_finitePrimitiveProfile_inputs` sums them over a fixed finite cover,
  supplying all primitive hypotheses of the forward and literal-adjoint
  `StrongAssembly` theorems on the covered physical carrier.

The complete matrix amplitude includes both positions and all masks. The scalar
primitives are the actual mixed phase entries and actual inverse entries.
Weighted ordered jets, monotonicity, individual interpolation, and the tame high
inverse bound are proved. The fixed low baseline precedes the Sobolev order `s`;
the final high bound is `C_s * (1 + |A|_(s+μ) + |S|_(s+μ))` with `μ = μ₀ + 2`.
Constants precede the phase, amplitude, and high seminorms.

The amplitude convention is the supremum over radial dilations `R ≥ 1` of the
joint `cNorm`, summed over the fixed charts. The phase convention is the sum of
joint `cNorm`s of `S(x,η)` on the same charts; `cNorm_normalizedPhase_eq` proves
its equality with the degree-one normalized phase at every dilation radius.

Geometric chart coverage, ordinary smoothness, positive phase homogeneity,
amplitude symbol-class finiteness, fixed low seminorm bounds, and the actual
zeroth-order inverse gap remain explicit inputs for the Hamilton phase and
carrier producers. This module proves the primitive construction; the parent
retains the low L² realization, Sobolev assembly, and actual geometric
instantiation. It does not claim the unconditional operator theorem.
-/
