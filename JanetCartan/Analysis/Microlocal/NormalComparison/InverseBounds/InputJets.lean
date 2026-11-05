module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.ParameterBounds

/-!
# Quantitative original-input estimates for normal comparison

Quantitative estimates for `app:ch_osc:setup:osc-normal` and
`app:ch_osc:prop:osc-normal`, derived from the original finite input jets:

* The actual averaged gradient and its actual parameter derivative have
  spatial jets bounded by `averagedGradientJetBound C k`, for `k + 1 ≤ M`.
* The full normal amplitude and its actual parameter derivative have
  Frobenius spatial jets bounded by `normalAmplitudeJetBound r C k` and
  `normalAmplitudeParameterJetBound r C k`, respectively, for `k ≤ M`.

Here `M = 20 * (n + 1)`. The constants are independent of the family.
Parameter/spatial interchange is proved on the open extensions, including
both parameter endpoints; both physical positions remain independent.
-/
