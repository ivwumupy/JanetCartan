module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalQuadraticSourceProfilesTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticStatic
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfiles

/-!
# The original prehistory high quadratic source cost

Use89's single static dictionary, shared literally with the full actual
primitive callback, together with100's unchanged global inverse budget. No
history, current scale, numerical moment guard, sample, shift, or prefix enters
this cost. Only the supplied source profile is a later argument. Publication
of the data and of its nonnegativity uses separate default-limit commands;
the dynamic source theorem imports these named results instead of rebuilding
them (new:eq:source-bound, app:ch_mean_pairs:eq:block-bilinear).
-/

public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open JanetCartan.PhysicalMean

run_meta do
  OriginalMeanQuadraticRealization.withActualQuadraticStaticPrimitives fun params fields => do
    unless params.size == 44 do
      throwError "actual quadratic budget: only the unchanged prehistory44 is permitted"
    OriginalCanonicalQuadraticSourceProfilesTemplate.publishBudget params fields

run_meta do
  OriginalMeanQuadraticRealization.withActualQuadraticStaticPrimitives fun params fields => do
    unless params.size == 44 do
      throwError "actual quadratic budget: only the unchanged prehistory44 is permitted"
    OriginalCanonicalQuadraticSourceProfilesTemplate.publishBudgetNonneg params fields
