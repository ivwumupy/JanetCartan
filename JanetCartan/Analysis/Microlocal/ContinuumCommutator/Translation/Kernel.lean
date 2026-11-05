module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.Amplitude
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Adjoint

/-!
# Literal translation conjugation of Euclidean two-position PDOs

The sign in `app:ch_background:prop:bg-inverse` follows from changing the
source variable in the actual Lebesgue integral. Both positions move by `+h`.
Strong frequency exhaustion passes the identity to the full L² operator.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology RealInnerProductSpace
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential

namespace JanetCartan.ContinuumCommutator

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp (α := E) ℂ 2

/-- Translation on the literal Euclidean Lebesgue L² space, with the same
positive-shift convention as `periodicL2Translation`
(`app:ch_background:prop:bg-inverse`). -/
def euclideanL2Translation (a : E) : L² →ₗᵢ[ℂ] L² :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x ↦ x + a) (measurePreserving_add_right volume a)

/-- Representative formula for Euclidean translation
(`app:ch_background:prop:bg-inverse`). -/
theorem euclideanL2Translation_coe (a : E) (u : L²) :
    euclideanL2Translation a u =ᵐ[volume] fun x ↦ u (x + a) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume a)

/-- Exact conjugation of the compact-frequency literal physical kernel;
both positions are shifted (`app:ch_background:prop:bg-inverse`). -/
theorem compactFrequencyAmplitudeKernel_translatedAmplitude
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (i : Fin d) (h ρ : ℝ) (x y : E) :
    compactFrequencyAmplitudeKernel (translatedAmplitude b i h) ρ x y =
      compactFrequencyAmplitudeKernel b ρ
        (x + h • EuclideanSpace.single i 1) (y + h • EuclideanSpace.single i 1) := by
  unfold compactFrequencyAmplitudeKernel
  simp only [add_sub_add_right_eq_sub, pairedPosition_add_jointPhysicalDirection,
    translatedAmplitude]

/-- Changing the source variable in the actual Lebesgue integral determines
the joint translation sign (`app:ch_background:prop:bg-inverse`). -/
theorem integral_compactFrequencyAmplitudeKernel_conjugate
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (i : Fin d) (h ρ : ℝ) (u : L²) (x : E) :
    (∫ y, compactFrequencyAmplitudeKernel b ρ (x + h • EuclideanSpace.single i 1) y *
      euclideanL2Translation (-(h • EuclideanSpace.single i 1)) u y) =
      ∫ y, compactFrequencyAmplitudeKernel (translatedAmplitude b i h) ρ x y * u y := by
  calc
    _ = ∫ y, compactFrequencyAmplitudeKernel b ρ (x + h • EuclideanSpace.single i 1) y *
        u (y - h • EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      filter_upwards [euclideanL2Translation_coe (-(h • EuclideanSpace.single i 1)) u] with y hy
      rw [hy, sub_eq_add_neg]
    _ = _ := by
      rw [← integral_add_right_eq_self (μ := volume) (fun y ↦
        compactFrequencyAmplitudeKernel b ρ (x + h • EuclideanSpace.single i 1) y *
          u (y - h • EuclideanSpace.single i 1)) (h • EuclideanSpace.single i 1)]
      simp only [add_sub_cancel_right, compactFrequencyAmplitudeKernel_translatedAmplitude]

/-- Compact-frequency L² conjugation, derived from the literal kernel,
without a conjugation assumption (`app:ch_background:prop:bg-inverse`). -/
theorem twoPositionCompactFrequencyL2Operator_conjugate
    (hd : 0 < d) (R h₀ : ℝ)
  (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
  (hA : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)
  (i : Fin d) (h : ℝ) (hsmall : |h| ≤ h₀) (ρ : ℝ) (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    euclideanL2Translation (h • EuclideanSpace.single i 1)
      (twoPositionCompactFrequencyL2Operator hd R b hb hs A hA ρ
        (euclideanL2Translation (-(h • EuclideanSpace.single i 1)) u)) =
      twoPositionCompactFrequencyL2Operator hd (R + h₀) (translatedAmplitude b i h)
        (contDiff_uncurry_translatedAmplitude b hb i h)
        (supportedInCenteredBox_translatedAmplitude b R h₀ hs i h hsmall) A
        (hasAmplitudeDerivativeBound_translatedAmplitude b i _ A hA h) ρ u := by
  apply Lp.ext
  filter_upwards [euclideanL2Translation_coe (h • EuclideanSpace.single i 1)
    (twoPositionCompactFrequencyL2Operator hd R b hb hs A hA ρ
      (euclideanL2Translation (-(h • EuclideanSpace.single i 1)) u)),
    (measurePreserving_add_right volume (h • EuclideanSpace.single i 1)).quasiMeasurePreserving.ae
      (twoPositionCompactFrequencyL2Operator_ae_kernel hd R b hb hs A hA ρ
        (euclideanL2Translation (-(h • EuclideanSpace.single i 1)) u)),
    twoPositionCompactFrequencyL2Operator_ae_kernel hd (R + h₀) (translatedAmplitude b i h)
      (contDiff_uncurry_translatedAmplitude b hb i h)
      (supportedInCenteredBox_translatedAmplitude b R h₀ hs i h hsmall) A
      (hasAmplitudeDerivativeBound_translatedAmplitude b i _ A hA h) ρ u] with x ht ho hn
  rw [ht, ho, hn]
  exact integral_compactFrequencyAmplitudeKernel_conjugate b i h ρ u x

/-- Exact conjugation of the full Euclidean PDO. Strong frequency exhaustion
justifies the identity on every L² datum (`app:ch_background:prop:bg-inverse`). -/
theorem twoPositionL2Operator_conjugate
    (hd : 0 < d) (R h₀ : ℝ)
  (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
  (hA : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)
  (i : Fin d) (h : ℝ) (hsmall : |h| ≤ h₀) (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    euclideanL2Translation (h • EuclideanSpace.single i 1)
      (twoPositionL2Operator hd R b hb hs A hA
        (euclideanL2Translation (-(h • EuclideanSpace.single i 1)) u)) =
      twoPositionL2Operator hd (R + h₀) (translatedAmplitude b i h)
        (contDiff_uncurry_translatedAmplitude b hb i h)
        (supportedInCenteredBox_translatedAmplitude b R h₀ hs i h hsmall) A
        (hasAmplitudeDerivativeBound_translatedAmplitude b i _ A hA h) u :=
  tendsto_nhds_unique
    ((euclideanL2Translation (h • EuclideanSpace.single i 1)).continuous.tendsto _ |>.comp
      (tendsto_twoPositionCompactFrequencyL2Operator hd R b hb hs A hA
        (euclideanL2Translation (-(h • EuclideanSpace.single i 1)) u)))
    ((tendsto_twoPositionCompactFrequencyL2Operator hd (R + h₀)
      (translatedAmplitude b i h) (contDiff_uncurry_translatedAmplitude b hb i h)
      (supportedInCenteredBox_translatedAmplitude b R h₀ hs i h hsmall) A
      (hasAmplitudeDerivativeBound_translatedAmplitude b i _ A hA h) u).congr
        (fun ρ ↦ (twoPositionCompactFrequencyL2Operator_conjugate
          hd R h₀ b hb hs A hA i h hsmall ρ u).symm))

end JanetCartan.ContinuumCommutator
