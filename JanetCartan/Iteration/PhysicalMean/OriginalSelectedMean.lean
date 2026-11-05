module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanFractionalProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedPhysicalMeanDefect
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardMass
set_option warningAsError true
set_option Elab.async false

/-!
# Actual original-data physical mean on the common final core

This is the connected consumer entry for the v2 mean construction
(`main:prop:mean`, `main:eq:mean-equation`, `main:eq:mean-size`). It does not
redefine the original selection, history, initializer, inverse, forcing, sample,
physical cutoff, or final core.

* `OriginalSelectedMeanData.physicalMean` is the real Schwartz cut of the SAME
  completed field. The cutoff is the original one, not the residual core.
* `OriginalSelectedMeanProfiles.completedMean_cNorm_profile` and
  `OriginalSelectedMeanProfiles.physicalMean_sobolev_profile` apply ALL actual
  normal-buffer, full initialized-field/full-strain, normalized-target and full
  sampled-self producers. The norm is the physical Fourier norm at `2 * π * ξ`,
  and the exponent is the true integer order `R ^ s`.
* `OriginalSelectedMeanProfiles.physicalMean_real_sobolev_profile` applies the
  existing Fourier split at the actual scale `R` to these genuine integer
  bounds. It gives EVERY real `r ≥ 0` with exactly `R ^ r` and the early cost
  `CphysicalMean_N(0) + CphysicalMean_N(⌈r⌉₊)`, with no rounding loss or new gate.
* The exact `Cmean` and `CphysicalMean` coefficients are fixed before the history
  and target, after only the finite Picard count. They are the explicit
  complementary-order convolution and original cutoff multiplier; no new
  count-dependent initial threshold is selected.
* `OriginalSelectedMeanData.physicalMean_error_on_common_core` supplies BOTH
  native cancellation and physical-cutoff core memberships using the existing
  `OriginalSelectedMeanResidualCore.core`, not a new domain or cutoff.
* The pointwise and `cNorm` precision theorems consume the genuine full-source
  Picard residual estimate. The retained-frame variant uses `N(accuracy)`;
  the requested-precision variant uses `N(accuracy + 1)` and pays the frame
  coefficient at the CURRENT scale, giving exactly `R ^ (-accuracy)`.
* `OriginalFullSourcePicard.input_fourierMass_le` uses the SAME unweighted
  original input and sample, with `M_N = Cmass * D_N(n + 1)` and the COMMON
  prefix budget `D_N = ∑ j ≤ N, P_j`, not merely the final individual profile.

Only the original selected-data hypotheses and numerical initial/stage reaches
remain in these interfaces; no quantitative analytic success field is assumed.
The physical field and every estimate retain ONE `J = cutoffCount K` and the
SAME complete forcing and Picard count. Choosing the requested count before the
history keeps all resulting order coefficients before the history as well.

This module is the actual mean component, not by itself an implementation of
`RevisedGlobal.UniformHistoryCorrection`: the exact Main theorem still also
requires the primary, cross-pair and whole-step assembly on these same objects.
-/
