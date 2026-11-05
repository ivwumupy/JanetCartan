module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.SchwartzPreimages.Realization
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.SchwartzPreimages.UnitPeriod

/-!
# Schwartz raw preimages of compact physical tests

The preimage input to `denseRange_rawTestSobolev_of_schwartz`, for
`app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, requires two steps: constructing
a jointly Schwartz representative of the unit-period partial Fourier
integral, and identifying its normalized literal L² class.

`SchwartzPreimages.UnitPeriod` constructs the representative from the compact
physical test. `SchwartzPreimages.Realization` identifies its literal L² class
after the exact unitary radian rescaling. Combining them below supplies the
preimage input without any additional analytic premise, in every transverse
dimension, including zero.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev

/-- Every compact physical test has a Schwartz raw preimage under the actual
partial unitary inverse, with the literal product Lebesgue measures and unitary
radian normalization. The witness is the rescaled jointly Schwartz partial
Fourier transform constructed from the test. This discharges `hpreimage` in
`denseRange_rawTestSobolev_of_schwartz` for
`app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`. -/
theorem exists_rawSchwartz_preimage_compactSmooth (n : ℕ)
    (φ : carrierInitialTestSpace n) :
    ∃ f : SchwartzMap (DensityEuclidean n) ℂ,
      partialUnitaryInverse n (rawSchwartzToL2 n f) = carrierInitialTestToLp φ := by
  obtain ⟨f, hf⟩ := exists_unitPeriodSchwartz_compactSmooth n φ
  exact ⟨rawRadianRescaleSchwartz f,
    rawSchwartz_preimage_compactSmooth_of_unitPeriod φ f hf⟩

end JanetCartan.ContinuumAdjoint.DensityMultiplier
