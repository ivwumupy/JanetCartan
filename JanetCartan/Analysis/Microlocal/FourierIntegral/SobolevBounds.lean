module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PhaseTrade
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FirstDerivatives
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.TransferAmplitudes
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.IntegerBounds

/-!
# Strong Sobolev bounds of graph operators

For `app:ch_regular_base:eq:fio-input`, `PhaseTrade` proves the nonlinear
forward Euler identity and the literal-adjoint phase trade from local smooth
homogeneous phase data and the actual mixed-matrix inverse hypothesis.

`FirstDerivatives` proves the actual forward and conjugate-transpose matrix
kernel derivatives used for gain one. `TransferAmplitudes` defines the finite
nonlinear transfer coefficients and proves their branch and datum-order counts.

`WeakTransfer` proves the finite distributional derivative expansion from actual
regularized kernels and supplied low L² realizations. `BranchBounds` proves
uniform low-jet bounds with high exponent `(s-k)/s`, including explicit monomial
and factor counts independent of the high majorant.

`LocalBranchBounds` localizes the primitive expansions to the supported
nonzero covector region. `WeightedBranches` preserves the exact number of
covector derivatives across every primitive monomial and proves the weighted
low-jet bounds needed by the fixed L² reserve.

`StrongAssembly` derives output membership and the tame order-zero estimate
for the forward graph and its literal Hilbert adjoint on all vector Sobolev
data, including order zero. It applies the supplied weighted low L² reserve
to the concrete branches and proves the weak expansions before Fourier
interpolation and density extension. It assumes no high branch norm estimate.
The adjoint uses the original amplitude's Frobenius jet bounds.

`PrimitiveProfiles` constructs the primitive majorants and proves their
interpolation and tame inverse bounds from finite normalized chart data.
`NormalizedBounds` instantiates those results in both all-data order-zero
estimates, with high quantity `1 + |A|_(s+μ) + |S|_(s+μ)` and fixed `μ = μ₀+2`.
Its constants precede the phase, amplitude, high seminorms, and datum.

`GainOneProfiles` produces the original order-minus-one amplitude, order-one
phase and mixed/inverse primitive profiles from normalized seminorms.
`GainOneBounds` inserts them into `GainOneAssembly`, applies the fixed L²
reserve and actual first-output weak identities, and reconstructs all-data
Sobolev regularity with gain one, including output orders zero and one.

`exists_graph_integer_sobolev_constant` and
`exists_adjoint_integer_sobolev_constant` are the final unified deductions for
`d ∈ {0,1}`. They prove output `H^s` membership and the estimate with input
order `max(s-d,0)`, high quantity `1 + |A|_{-d,s+μ} + |S|_{s+μ}`, and fixed
`μ = μ₀+2`. No primitive interpolation, high inverse-jet estimate, high branch
norm, operator derivative identity or output membership remains a premise.

These are conditional estimates. The Hamilton phase and compatible geometry
producers owe the finite normalized cover, smoothness, homogeneity and actual
mixed inverse gap. The graph realization and finite-calculus producers owe
the fixed low amplitude/phase seminorm bounds, symbol-class finiteness,
distributional L² realizations and fixed low L² reserve. The finite-calculus,
regular-sector and response consumers must instantiate those analytic inputs
for their concrete objects before using these deductions in the paper theorem.
-/
