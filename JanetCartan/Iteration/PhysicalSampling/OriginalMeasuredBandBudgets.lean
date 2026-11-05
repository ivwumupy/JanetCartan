module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredBandBudgetsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredBandBudgetsApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication

/-!
# Before-history corrected sharp-band coefficient on the original tuple

The correction/measurement/uncut-response budgets are exactly the measured
mean's. Its extra free jets come from the identical retained packet, and the
fixed cutoff has its actual compact-seminorm bound. The finite current
application is still separate (`app:ch_waves:eq:sampling-operator-bounds`).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16000
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

cache_original_measured_band_cutoff_field 0
cache_original_measured_band_cutoff_field 1
cache_original_measured_band_cutoff_field 2
cache_original_measured_band_factory
cache_original_measured_band_budget_field 0
cache_original_measured_band_budget_field 1
cache_original_measured_band_budget_field 2
cache_original_measured_band_budget_field 3
