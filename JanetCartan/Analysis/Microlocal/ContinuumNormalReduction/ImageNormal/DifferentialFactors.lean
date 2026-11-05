module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.DifferentialFactors.Operator
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.DifferentialFactors.PrimitiveBounds

/-!
# Differential factors of the Euclidean image normal

Checked ingredients for `app:ch_background:prop:bg-frame`, Step 1:

* actual first/zeroth coefficient arrays and their geometric specialization;
* source-square product coefficient `Q = ∑ Aᵃ ∂ₐC + ZC`;
* the full matrix Hermitian adjoint identity, proved by integration by parts;
* an actual compact Schwartz realization of the masked adjoint;
* the unregularized action of both literal Bessel multipliers and convergence;
* output differentiation of the actual composite, retaining the complete `Q`;
* the explicit full amplitude and its positive `MMᵀ` leading term;
* its explicit lower-order coefficient remainder and quantitative fixed-chart
  physical derivative bounds of order minus one from primitive budgets.

`coefficientImageNormal_eq_fullAmplitude` identifies the literal composite
with `matrixFullAmplitudeOperator differentialFullAmplitude` on smooth input.
The fixed measurement mask supplies compact support, and every source-tested
matrix entry has a convergent unregularized frequency integral.
`coefficientImageNormal_eq_leading_add_remainder` supplies its exact amplitude
split. `norm_iteratedFDeriv_differentialRemainderAmplitude_le_primitive` bounds
all physical jets through order `N` by an explicit constant depending only on
`d`, `N`, and the primitive chart budgets for `A`, `Z`, `μ`, and `χ` (the last
through order `N+1`). The geometric specialization uses the actual principal
and reduced zeroth coefficients, including the induced connection.

The parent image-normal construction retains the separate source commutator,
Euclidean/torus comparison, diagonal reduction, and endpoint estimates. This
module proves the Euclidean differential-factor deduction, not those further
steps or the unconditional continuum existence theorem.
-/
