module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Native
public import JanetCartan.Iteration.PhysicalInitialization.CurrentInverse
public meta import JanetCartan.Iteration.PhysicalInverseContinuity.OriginalApplication

/-!
# Original current inverse at the literal density-admission grade

`StrongDatum.original_current_admission_raw_half` has an explicit threshold
and works for every admissible physical prefix above it. It returns the
original zero-density carrier with its complete native specification and
`X_(κ+3+(n−1)+2) (rawCurrent − rawSeed) ≤ δ/2`, for the actual measured
residuals on the unchanged row. The chart/phase, coefficient, native
coercivity, both quadratures, residual regularity, and high cap are all
constructed. `StrongDatum.Original.Vzero` is selected from the complete native
zero-density branch *before* the comparison. `Original.raw_half` is the bound
on its named `rawCurrent` and the prehistory `rawSeed`; `Original.current_zero_estimate`
and `Original.rawSeed_preScale_estimate` retain the native all-order estimates.
`StrongDatum.Original.all_densities` retains the full inverse on
the same current for the corrected step. There is no leading-chart,
operator, inverse-continuity or measured-error input.

The positive-background parent chooses σ using the pre-σ reference estimate
and the actual mask/seed field; this theorem works at every such fixed σ.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 16000000

apply_original_leading_measured_raw_admission
