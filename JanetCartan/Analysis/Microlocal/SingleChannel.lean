module

public import JanetCartan.Analysis.Microlocal.SingleChannel.Components

/-!
# Full-space single-channel L² estimates

The actual phase–amplitude integral of `app:ch_osc:prop:osc-channel` extends to
all complex L² input data. `SingleChannel.exists_oscillatorySingleChannelOperator`
proves its squared `C K` bound from the existing buffered normal data, including
finite Euclidean/Frobenius components and the factor four for both real quadratures.
The extra normalization is exactly `sqrt (K / (2π))`, and the output uses full
Lebesgue measure on `ℝ × ℝᵈ`.

The imported normal estimate applies in every positive slice dimension `d`,
including `d = 1`. Its constant is chosen before the slice family, carrier,
parameter and frequency, from the fixed buffered geometry, finite input jet
bounds and time interval. Actual WKB chart verification and differentiated
dyadic assembly belong to the raw-primary construction.
-/
