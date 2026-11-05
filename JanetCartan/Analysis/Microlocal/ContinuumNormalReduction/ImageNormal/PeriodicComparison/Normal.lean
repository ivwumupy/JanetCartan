module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.EuclideanChannel
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.TestAction

/-!
# The bounded Euclidean image normal

The normal of the actual bounded Euclidean channel has the literal
source-square Schwartz action in `app:ch_background:prop:bg-frame`, Step 1.
This supplies the Euclidean term of `exists_periodicImageNormal_comparison`;
the parent image-normal reduction can then apply the source commutator and
full-amplitude identities to this same operator.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "R²" => EuclideanL2 d E

/-- The bounded real Lebesgue L² realization of `μ P J χ² J P* μ`, formed
from the constructed channel and its literal Hilbert adjoint
(`app:ch_background:prop:bg-frame`, Step 1). -/
def euclideanNormal
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) : R² →L[ℝ] R² :=
  (euclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc).comp
    (euclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc).adjoint

/-- The constructed Euclidean normal is literally self-adjoint
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem euclideanNormal_adjoint
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) :
    (euclideanNormal A Z χ μ hA hZ hχ hχc hμ hμc).adjoint =
      euclideanNormal A Z χ μ hA hZ hχ hχc hμ hμc := by
  simp only [euclideanNormal, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- The complex inclusion of the actual real normal agrees with the literal
source-square Schwartz expression. Both channel actions are instantiated for
the same bounded operator; the source square remains between the two inverse
multipliers (`app:ch_background:prop:bg-frame`, Step 1). This holds for all
real Schwartz representatives, in particular the compact tests used by the
parent image-normal reduction. -/
theorem euclideanNormal_schwartz_action
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (v : Fin d → 𝓢(E, ℂ)) (f : R²)
    (hf : l2ComplexInclusion volume f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ v i x)) :
    l2ComplexInclusion volume (euclideanNormal A Z χ μ hA hZ hχ hχc hμ hμc f) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ coefficientSourceSquaredImageSchwartz A Z χ μ v i x) :=
  normal_schwartz_action_of_channel_actions A Z χ μ hχ hχc
    (euclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc)
    (euclideanChannel_schwartz_action A Z χ μ hA hZ hχ hχc hμ hμc)
    (euclideanChannel_adjoint_schwartz_action A Z χ μ hA hZ hχ hχc hμ hμc) v f hf

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
