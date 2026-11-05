module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.SymbolDerivatives

/-!
# The real normalized symbol in the complex transport identity

This is the coefficient inclusion needed to instantiate the complex transport
algebra with the actual real normalized adjugate of
`app:ch_regular_base:eq:normalization-exact`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral

variable {n r : ℕ}

/-- Include the actual real principal pencil into complex matrices, as used
by `app:ch_regular_base:eq:direct-graph-identity`. -/
def complexifiedPencil (H : Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℝ) :
    Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℂ :=
  (Complex.ofRealCLM.toLinearMap.mapMatrix.toContinuousLinearMap).comp H

/-- The complex pencil has exactly the original real entries included in `ℂ`;
there is no change of frequency normalization
(`app:ch_regular_base:eq:direct-graph-identity`). -/
theorem complexifiedPencil_apply
    (H : Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℝ) (ξ : Euclidean n) :
    complexifiedPencil H ξ = (H ξ).map Complex.ofReal := rfl

/-- The actual normalized adjugate supplies the undifferentiated symbol
identity for the complex two-term cancellation. Singular pencils are allowed.
Source: `app:ch_regular_base:eq:normalization-exact` and
`app:ch_regular_base:eq:direct-graph-identity`. -/
theorem complexifiedPencil_mul_normalizedAdjugateSymbol
    (H : Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℝ) (ξ : Euclidean n) :
    complexifiedPencil H ξ * (normalizedAdjugateSymbol H ξ).map Complex.ofReal =
      (normalizedDeterminantSymbol H ξ : ℂ) • 1 := by
  calc
    _ = (H ξ * normalizedAdjugateSymbol H ξ).map Complex.ofReal :=
      (Complex.ofRealHom.mapMatrix.map_mul _ _).symm
    _ = _ := by
      rw [mul_normalizedAdjugateSymbol]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.smul_apply, hij]

end JanetCartan.FourierIntegral
