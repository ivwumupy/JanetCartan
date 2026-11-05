module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Localizers.Diagonal

/-!
# Buffered localizers and actual graph gradient gaps

For `app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:joint-stationary`,
`exists_uniform_bufferedLocalizers_joint_gap` constructs smooth compact input
and output symbols valued in `[0,1]`, protects the entire input closed support,
and proves a positive lower bound for the actual packed joint derivative on
the complementary amplitude support. It handles forward and literal reverse
phases, and `diagonal_forwardChartControl` / `diagonal_reverseChartControl`
discharge the geometry for diagonal factors.

The parent supplies the inverse-chart identities and quantitative low bounds
in `ForwardChartControl` or `ReverseChartControl`, plus a common compact image
envelope inside its open output chart. `isCompact_graphChartEnvelope` supplies
compactness from physical compact support and covector bounds. These geometric
premises remain explicit, as does membership in the actual conic phase domain.
They contain neither a gradient-gap assumption nor a kernel estimate. The gap
is uniform for arbitrary phase families sharing these bounds and buffers.

`fderiv_jointPhase_forward` and `fderiv_jointPhase_reverse` identify the five
residuals with the actual packed derivative. `FrequencyGaps` supplies the actual
partial-derivative bounds outside comparable annuli, with explicit covector
comparability. Kernel integration by parts, summation, and regularization limits
are the consuming parent tasks' responsibility.
-/
