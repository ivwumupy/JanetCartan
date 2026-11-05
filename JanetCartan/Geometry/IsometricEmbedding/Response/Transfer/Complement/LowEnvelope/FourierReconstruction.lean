module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FourierReconstruction.CompactGraph

/-!
# Fourier reconstruction of the low-envelope graph

Checked prerequisites for `app:ch_response:thm:response-literal-transfer`:

* Fourier L¹ control with the exact square-root ball-volume loss `Λ^(n/2)`;
* the paper-normalized Plancherel factor `(2π)^(-n/2)` for arbitrary L² data;
* agreement with `Localization.paperFourierTransform` on L¹ ∩ L²;
* physical inverse Fourier reconstruction of low-support L² data almost everywhere;
* literal forward and reverse reconstruction through `sourceKernel`, with the
  graph's single outer `(2π)⁻ⁿ`, both physical positions, and all amplitude cutoffs;
* joint frequency integrability from compact full amplitudes and Fourier L¹
  control, and preservation of compactness by the complete complementary selector.

The graph theorems use actual complex Euclidean Hilbert-valued data and Lebesgue
measure. The general L² results impose no physical L¹ assumption. The ordinary
`paperFourierTransform` variants explicitly concern L¹ ∩ L² data. Continuity of
compact amplitudes suffices for these reconstruction results; smooth compact
amplitudes therefore satisfy the stated hypotheses. Source integration by parts,
Sobolev estimates, and the unregularized limit belong to the consuming construction.
-/
