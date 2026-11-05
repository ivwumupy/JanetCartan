module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.EuclideanChannel.Actions.Reality

/-!
# The two literal real Euclidean channel actions

The concrete `euclideanChannel` and its literal Hilbert adjoint supply both
Schwartz-action hypotheses of `normal_schwartz_action_of_channel_actions`
in `app:ch_background:prop:bg-frame`, Step 1. Reality is proved for the same
bounded matrix construction; no additional action or reality input is used.
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

/-- The actual bounded real channel realizes `μ P J χ` on every Schwartz
representative, supplying the forward hypothesis of
`normal_schwartz_action_of_channel_actions`
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem euclideanChannel_schwartz_action
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (v : Fin d → S) (f : R²)
    (hf : l2ComplexInclusion volume f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ v i x)) :
    l2ComplexInclusion volume (euclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc f) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ channelSchwartz A Z χ μ v i x) := by
  have he : l2ComplexInclusion volume f = imageSchwartzFamilyToLp v :=
    Lp.ext (hf.trans (imageSchwartzFamilyToLp_ae v).symm)
  rw [euclideanChannel_complexInclusion, he, complexEuclideanChannel_toLp]
  exact imageSchwartzFamilyToLp_ae _

/-- The literal real Hilbert adjoint realizes the full divergence-form
factor `χ J P* μ`, supplying the adjoint hypothesis of
`normal_schwartz_action_of_channel_actions`
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem euclideanChannel_adjoint_schwartz_action
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (v : Fin d → S) (f : R²)
    (hf : l2ComplexInclusion volume f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ v i x)) :
    l2ComplexInclusion volume
        ((euclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc).adjoint f) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ channelAdjointSchwartz A Z χ μ v i x) := by
  have he : l2ComplexInclusion volume f = imageSchwartzFamilyToLp v :=
    Lp.ext (hf.trans (imageSchwartzFamilyToLp_ae v).symm)
  rw [euclideanChannel_adjoint_complexInclusion, he, complexEuclideanChannel_adjoint_toLp]
  exact imageSchwartzFamilyToLp_ae _

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
