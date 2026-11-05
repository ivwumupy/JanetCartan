module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Regularizations.Chart
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Regularizations.Identification

/-!
# Regularizations and retarded identification on the retained selected chart

`exists_selected_supported_graph_regularizations` constructs the forward
regularizations and literal Hilbert adjoints, uniform low bounds, and both
strong limits on the original `chartOutputMask` and `chartInputMask`. The
common sequence is exactly `complexPhysicalCutoff`. The SAME supported `G`,
collared solver sum and full physical `PW₁`, including `B`, are retained.

The canonical retarded operators have the actual elapsed integrals and uncut
test kernels. `retained_common_localization_eq_canonical` identifies their
common-mask localizations with the SAME retained solver and residual, by
literal kernel equality and density. The source multiplier acts before the
Fourier multiplier throughout. All geometric and symbol inputs are proved
from the retained chart outputs; no uncut residual equation is assumed.

The parent retains the four PDO terms, the tested differential equation, and
its final instantiation. Source: `paper-v2.tex`,
`app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:energy-complete-residual`; `paper.tex`,
`app:ch_regular_base:prop:complete-residual`.
-/
