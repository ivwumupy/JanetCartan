module

public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalCarriersApplication

/-!
# Actual common-measurement carriers with the complete native inverse

`OriginalCarriers.exists_common_measured_carriers` applies the actual original44
current inverse and preserves its ENTIRE predicate on the SAME carrier witness.
It additionally derives the common-chart kernel, test and adjoint formulas,
measurement support and norm bound, retaining the individual carrier's original
angular cutoff, label support, transport, covector, normal field and stress frame.

`common_measurement_of_native` applies to an already retained native carrier
witness. Thus a downstream parent need not choose another carrier or identify
independently chosen normal inverses. No corrected response or comparison bound
is assumed or asserted here.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 2400000

apply_actual_carriers_common_measurement
apply_actual_carriers_common_coordinates
