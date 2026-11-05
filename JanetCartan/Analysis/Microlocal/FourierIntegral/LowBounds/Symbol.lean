module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CompactNormal
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Channels

/-!
# The exact normal symbol in the existing paired-position coordinates

This shared definition is consumed by the primitive-jet and bounded-PDO steps
of `app:ch_regular_base:eq:actual-normal-amplitude`. It only rearranges the
already defined full amplitude; it assumes no derivative or operator bound.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.LowBounds

open NormalComparison AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- The cycle-frequency full normal amplitude in the existing `pairedPosition`
coordinates used by `GraphNormalAmplitudeBounds`. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
def cycleCrossNormalSymbol (D : Set E) (S : E → E → ℝ)
    (A B : E → E → Matrix (Fin r) (Fin r) ℂ)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
    (ξ : E) (z : Euclidean (2 * n)) : Matrix (Fin r) (Fin r) ℂ :=
  cycleCrossNormalAmplitude D S A B η J
    (splitPhysicalPositions z).1 (splitPhysicalPositions z).2 ξ

/-- Pairing the two positions recovers the exact compact-normal amplitude,
including both cutoffs and the Jacobian
(`app:ch_regular_base:eq:actual-normal-amplitude`). -/
@[simp] theorem cycleCrossNormalSymbol_pairedPosition
    (D : Set E) (S : E → E → ℝ)
    (A B : E → E → Matrix (Fin r) (Fin r) ℂ)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E) (ξ x y : E) :
    cycleCrossNormalSymbol D S A B η J ξ (pairedPosition x y) =
      cycleCrossNormalAmplitude D S A B η J x y ξ := by
  simp only [cycleCrossNormalSymbol, splitPhysicalPositions_pairedPosition]

end JanetCartan.FourierIntegral.LowBounds
