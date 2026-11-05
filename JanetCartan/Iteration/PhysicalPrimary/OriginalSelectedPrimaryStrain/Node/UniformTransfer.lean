module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Proof

/-! The original full-complex node strain bound follows from a nonnegative
uniform discrepancy price on the complete observed-label family. This
conditional deduction keeps the identical uncut response, source labels,
carrier and core. The actual producer is supplied in `Node`
(`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.node_of_uniform_discrepancy
