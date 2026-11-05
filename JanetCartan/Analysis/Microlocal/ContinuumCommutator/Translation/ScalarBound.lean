module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.Amplitude

/-!
# Uniform L² bound for the divided full amplitude

This applies the checked Euclidean PDO estimate to the amplitude produced by
FTC in `app:ch_background:prop:bg-inverse`. Identification with conjugation of
the original operator, and transfer to periodic chart realizations, are separate.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential

namespace JanetCartan.ContinuumCommutator

variable {d : ℕ} (hd : 0 < d) (R h₀ : ℝ)
  (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
  (hA : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) A)
  (i : Fin d) (h : ℝ) (hh : h ≠ 0) (hsmall : |h| ≤ h₀)

/-- The checked PDO realization of the FTC amplitude on Euclidean Lebesgue
L² (`app:ch_background:prop:bg-inverse`). -/
def translationDifferenceL2Operator :
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 →L[ℂ]
      Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  twoPositionL2Operator hd (R + h₀) (translationDifferenceAmplitude b i h)
    (contDiff_uncurry_translationDifferenceAmplitude b hb i h)
    (supportedInCenteredBox_translationDifferenceAmplitude b R h₀ hs i h hsmall) (2 * A)
    (hasAmplitudeDerivativeBound_translationDifferenceAmplitude b
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i _ A hA h hh)

/-- Uniform operator norm bound from primitive full-amplitude derivatives,
with a single fixed enlarged support box (`app:ch_background:prop:bg-inverse`). -/
theorem norm_translationDifferenceL2Operator_le :
    ‖translationDifferenceL2Operator hd R h₀ b hb hs A hA i h hh hsmall‖ ≤
      fixedBoxAmplitudeConstant d (R + h₀) * (2 * A) :=
  norm_twoPositionL2Operator_le ..

/-- The uniform divided-amplitude estimate on every Euclidean L² datum,
without differentiating that datum (`app:ch_background:prop:bg-inverse`). -/
theorem norm_translationDifferenceL2Operator_apply_le
    (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    ‖translationDifferenceL2Operator hd R h₀ b hb hs A hA i h hh hsmall u‖ ≤
      (fixedBoxAmplitudeConstant d (R + h₀) * (2 * A)) * ‖u‖ :=
  norm_twoPositionL2Operator_apply_le ..

end JanetCartan.ContinuumCommutator
