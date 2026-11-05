module

public import JanetCartan.Iteration.PhysicalSampling.OriginalGraphResponseApplication

/-!
# One literal tensor source cutoff and full uncut map on the sampling graph

The same regular weak current supplies the existing global ambient response,
not a recut output or another response operator. Its physical map is the
actual source-dilated finite history (`app:ch_response:eq:response-full-map`).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

retain_original_measured_graph_response 0
retain_original_measured_graph_response 1
retain_original_measured_graph_response 2
retain_original_measured_graph_response 3
retain_original_measured_graph_response 4
