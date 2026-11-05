module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.SelectedNativeGlue.Paired
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.SelectedNativeGlue.Node

/-!
# Exact selected/native representation of the original node deduction

`NodeSelectedNativeGlue.paired_eq` and `NodeSelectedNativeGlue.node_eq` identify
the selected source hypothesis and node conclusion with their native versions
on the SAME source data. Both use only selected52,N,sample,accuracy,C. These
identities transport the existing node deduction (`main:eq:primary-strain`).
-/
