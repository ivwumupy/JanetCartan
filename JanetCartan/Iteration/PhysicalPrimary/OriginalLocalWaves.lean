module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveRaw
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate

/-!
# The actual original corrected and full-angular local waves

The public raw-only predecessor retains the actual source53 leading data and
both χ₂ source quadratures. This application uses the SAME task26 graph adapter
of the native weak38 uncut `OriginalFullResponse.B`, never a different ambient
extension, cutoff or current. Only local smoothness is claimed
(`app:ch_response:cor:current-atoms`, `app:ch_lag:eq:lag-recurrence`).

Every whole-input displacement uses the original finite-band rate margin,
original selected sampling radius and SAME spatial cell. Restoring the actual
inner angular factor does not scale the separate positive baseline. The outer
zero-weight branch belongs to the final weighted synthesis, not a division by
the weight or a replacement of the raw fields.

The final `cutSchwartz` primary still requires the actual shared final family,
Picard input and sharp jets. These are not replaced by a success hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000

name_original_local_source_callback
abbreviate_original_local_graph_inputs_through 26
abbreviate_original_local_graph_inputs_through 28
abbreviate_original_local_graph_inputs_through 37
name_original_local_sample_row
construct_original_local_corrected_atoms
construct_original_local_corrected_sample
construct_original_local_whole_waves 0
construct_original_local_whole_waves 1
construct_original_local_whole_waves 5
construct_original_local_whole_waves 2
construct_original_local_whole_waves 3
construct_original_local_whole_waves 4
