module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.Basic

/-!
# The literal Schwartz action of the Euclidean normal

The Euclidean channel construction must prove its forward and literal-adjoint
Schwartz actions. Once supplied, their composition is exactly
`coefficientSourceSquaredImageSchwartz`, with the source square between the two
inverse multipliers, as required by `app:ch_background:prop:bg-frame`, Step 1.
This deduction supplies no bounded channel by itself.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "R²" => EuclideanL2 d E
local notation "S" => 𝓢(E, ℂ)

/-- Composing the proved real channel and adjoint test actions identifies
the Euclidean normal with the literal source-square expression. The displayed
test-action inputs are to be supplied by the actual Euclidean channel
construction (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem normal_schwartz_action_of_channel_actions
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (B : R² →L[ℝ] R²)
    (hB : ∀ (v : Fin d → S) (f : R²),
      l2ComplexInclusion volume f =ᵐ[volume] (fun x ↦ WithLp.toLp 2 (fun i ↦ v i x)) →
      l2ComplexInclusion volume (B f) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (fun i ↦ channelSchwartz A Z χ μ v i x))
    (hBadj : ∀ (v : Fin d → S) (f : R²),
      l2ComplexInclusion volume f =ᵐ[volume] (fun x ↦ WithLp.toLp 2 (fun i ↦ v i x)) →
      l2ComplexInclusion volume (B.adjoint f) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (fun i ↦ channelAdjointSchwartz A Z χ μ v i x))
    (v : Fin d → S) (f : R²)
    (hf : l2ComplexInclusion volume f =ᵐ[volume] (fun x ↦ WithLp.toLp 2 (fun i ↦ v i x))) :
    l2ComplexInclusion volume (B.comp B.adjoint f) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ coefficientSourceSquaredImageSchwartz A Z χ μ v i x) := by
  have h := hB (channelAdjointSchwartz A Z χ μ v) (B.adjoint f) (hBadj v f hf)
  have he := DFunLike.congr_fun (channelSchwartz_comp_adjoint A Z χ μ hχ hχc) v
  change channelSchwartz A Z χ μ (channelAdjointSchwartz A Z χ μ v) =
    coefficientSourceSquaredImageSchwartz A Z χ μ v at he
  simpa only [ContinuousLinearMap.comp_apply, he] using h

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
