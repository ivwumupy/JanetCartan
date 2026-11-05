module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.FrequencyTransfer.CompactFrequency.Weak
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.FrequencyTransfer.CompactFrequency.Fubini

/-!
# Compact-frequency weak derivative transfer

For `app:ch_regular_base:eq:graph-derivative-transfer` and
`app:ch_regular_base:eq:fio-input`, the phase `x · ξ` with the `2π` convention
admits both weak derivative identities at every compact frequency cutoff.
The output derivative identity is exported from `CompactFrequency.Weak`;
the transfer identity below also integrates by parts in the source variable.
Both hold for every real radius, hence in particular for nonnegative radii.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: the weak output coordinate
derivative of the literal compact-frequency operator is the sum of the
transferred full amplitude acting on the datum and the original amplitude
acting on its coordinate derivative. Every integral is justified from smoothness
and compact physical/frequency supports in the imported leaves. -/
theorem compactFrequencyAmplitudeKernel_weak_transfer
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) {R : ℝ}
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ))
    (ρ : ℝ) (i : Fin d) {u : E → ℂ} (hu : ContDiff ℝ ∞ u)
    (hus : HasCompactSupport u) (φ : 𝓢(E, ℂ)) :
    (∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1) *
      (∫ y, compactFrequencyAmplitudeKernel b ρ x y * u y)) =
      -(∫ x, φ x *
        ((∫ y, compactFrequencyAmplitudeKernel (transferAmplitude b i) ρ x y * u y) +
         (∫ y, compactFrequencyAmplitudeKernel b ρ x y *
           fderiv ℝ u y (EuclideanSpace.single i 1)))) := by
  rw [compactFrequencyAmplitudeKernel_weak_outputDerivative hb hs ρ i hu.continuous φ]
  simp_rw [compactFrequencyAmplitudeKernel_outputDerivative_eq_transfer hb ρ i hu hus]

end JanetCartan.Pseudodifferential
