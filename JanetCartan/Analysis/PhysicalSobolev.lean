module

public import JanetCartan.Analysis.PhysicalSobolev.Embedding
public import JanetCartan.Geometry.IsometricEmbedding.Scales.Revised.StageLosses

/-!
# The derivative tail of the actual physical cutoff

In Step 6 of `main:thm:step`, take the *original* uncut field `u = P + W`.
The actual high physical Sobolev norm of `u` supplies the displayed `C¹` tail
for `truncate (R ^ bandExponent) u - u`. Nothing is assumed about the output
of the cutoff or its derivatives. Obtaining the input Sobolev profile from the
primary and secondary fields is a separate finite-stage obligation.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace JanetCartan.PhysicalSobolev

open PhysicalCutoff Pseudodifferential RevisedScales

variable {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- §15, Step 6: with `λ = R^a`, the input estimate at `m₀+k` yields exactly
`C δ R^{B₀} λ^{m₀-ζk}` for the derivative of the SAME real physical output
minus its input. At `u = P + W` this is the tail used in the metric comparison.
There is no restriction on `k` here: `aζk > Q+B₃` is used by that consumer. -/
theorem norm_fderiv_truncate_sub_le_of_profile {R C δ : ℝ} (hR : 0 < R)
    (k : ℕ) (u : 𝓢(E, V))
    (hprofile : (eLpNorm (fun ξ ↦
      euclideanSobolevWeight ((baselineOrder n : ℝ) + k) ((2 * Real.pi) • ξ) •
        𝓕 (complexify u) ξ) 2 volume).toReal ≤
      C * δ * R ^ RevisedScales.displacementLoss n *
        (R ^ carrierExponent) ^ ((baselineOrder n : ℝ) + k)) (x : E) :
    ‖fderiv ℝ (⇑(truncate (R ^ bandExponent) u) - ⇑u) x‖ ≤
      (embeddingConstant n * C) * δ * R ^ RevisedScales.displacementLoss n *
        (R ^ carrierExponent) ^ ((baselineOrder n : ℝ) - cutoffSlack * (k : ℝ)) := by
  have hΛ : 0 < R ^ bandExponent := Real.rpow_pos_of_pos hR _
  have htail := (physicalWeightedNorm_truncate_sub_le hΛ (baselineOrder n : ℝ) k u).trans
    (mul_le_mul_of_nonneg_left hprofile (inv_nonneg.mpr (pow_nonneg hΛ.le k)))
  have hder := (norm_fderiv_le (truncate (R ^ bandExponent) u - u) x).trans
    (mul_le_mul_of_nonneg_left htail (embeddingConstant_nonneg n))
  have hscale : ((R ^ bandExponent) ^ k)⁻¹ * (R ^ carrierExponent) ^ ((baselineOrder n : ℝ) + k) =
      (R ^ carrierExponent) ^ ((baselineOrder n : ℝ) - cutoffSlack * (k : ℝ)) := by
    rw [← Real.rpow_mul_natCast hR.le, ← Real.rpow_neg hR.le, ← Real.rpow_mul hR.le,
      ← Real.rpow_add hR, ← Real.rpow_mul hR.le]
    congr 1
    rw [scale_windows.2.1]
    ring
  calc
    _ ≤ embeddingConstant n * (((R ^ bandExponent) ^ k)⁻¹ *
        (C * δ * R ^ RevisedScales.displacementLoss n *
          (R ^ carrierExponent) ^ ((baselineOrder n : ℝ) + k))) := hder
    _ = (embeddingConstant n * C) * δ * R ^ RevisedScales.displacementLoss n *
        (((R ^ bandExponent) ^ k)⁻¹ * (R ^ carrierExponent) ^ ((baselineOrder n : ℝ) + k)) := by ring
    _ = _ := by rw [hscale]

end JanetCartan.PhysicalSobolev
