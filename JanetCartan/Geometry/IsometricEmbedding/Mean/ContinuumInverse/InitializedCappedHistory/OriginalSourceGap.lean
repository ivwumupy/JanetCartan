module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.SourceInverseBoundary
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.PrescribedHistoryGap
public meta import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.OriginalSourceGap.Extraction

/-!
# The original source gap on the same selected row and scale

`OriginalSourceGap.source_input` supplies the source premise of
`exists_prescribed_source_history_coercivity` from the **actual original**
`SourceInverseBoundary.continuation`. It takes all 21 original parameters, then
one scale `σ` and its original `Ioc 0 sourceCap` proof. Its conclusion is universal
in the density and its four original smoothness/positivity/low-norm hypotheses.

The source continuation is not four parallel fields: for each density it first
returns `Vzero`, its frozen certificates, and then a continuation for every
source scale. We keep that `Vzero`, specialize this same continuation at `σ`,
keep its `Vop`, and project the literal uniqueness, test/adjoint action, physical
row norm, local gap, and two augmented-gap fields. Only the order of universal
inputs is rearranged. No source-gap or source-inverse success premise is added.

All original row/reference/current/cutoff and `g/Mlimit/rInner` data are unchanged.
`Vzero`, `frozen_spec`, and `scale_continuation` expose the same frozen witness;
`Vop` and `operator_spec` retain the same source witness with its **complete**
original inverse tail. `gap_spec` is the six-field projection, while
`source_input` packages it as the fixed-scale universal source premise.

Consumer: `PrescribedHistoryGap`, source premise at lines 225–254
(`app:ch_background:eq:bg-local-bound`, `app:ch_background:eq:bg-global-bound`,
`main:eq:displacement-budget`, `new:sec:order-of-choices`). This projection does
not itself establish the remaining history or final embedding construction.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

project_original_fixed_scale_source_gap
