module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.PrimitiveInputs
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Realization

/-!
# Whole-image geometry for the exact graph normal

For `app:ch_regular_base:thm:actual-calculus`, Step 1, the actual inverse is
constructed on the whole `LowBounds.bufferedNormalDomain`, with both physical
positions retained. Its inverse equations, smoothness, the open image and the
exact change-of-variables chart follow from local phase smoothness, injectivity
and the averaged-Jacobian determinant gap. Covector normalization preserves
smoothness on every whole-image dyadic shell.

Original degree-one homogeneity, a mixed second-jet bound and the determinant gap
give two-sided frequency comparison. The positive source collar includes the two
low shells in a fixed source band. Original normalized phase jets through
`wholeImagePhaseReserve n = primitiveNormalReserve n + 2` give uniform Jacobian
jets and positive-order joint inverse jets on every whole-image shell.

`exists_wholeImage_primitive_inputs` assembles the exact chart, transported closed
support, buffered geometry and all primitive shell inputs. It uses only original
amplitude smoothness, support and normalized jets through `primitiveNormalReserve n`.
`exists_graphL2_of_wholeImage_phase` applies the local-phase consumer with all these
geometric premises discharged and reuses PhaseExtension for the auxiliary global
phase. Its remaining original amplitude assumptions are explicit. Instantiation
by the paper's Hamilton family and the full calculus remain the parent's work.
-/
