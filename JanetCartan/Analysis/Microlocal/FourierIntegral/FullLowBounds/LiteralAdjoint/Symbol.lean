module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.JointJets
public import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# The full source-symbol budget under literal adjunction

Conjugate transpose keeps the original physical variable order in
`app:ch_regular_base:eq:actual-adjoint-trade`. All ordered derivatives and their
covector weights therefore retain exactly the same bound.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullLowBounds
open SourceExpansion AmplitudeBound
variable {n r : ℕ}

private theorem scalarCoefficientJet_star (is : List (Fin n ⊕ Fin n))
    (f : Euclidean n × Euclidean n → ℂ) :
    scalarCoefficientJet is (fun p ↦ star (f p)) =
      fun p ↦ star (scalarCoefficientJet is f p) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [scalarCoefficientJet, ih, fderiv_star,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply]

private theorem sourceCoordinateDerivList_star (js : List (Fin n)) (f : Euclidean n → ℂ) :
    euclideanCoordinateDerivList js (fun y ↦ star (f y)) =
      fun y ↦ star (euclideanCoordinateDerivList js f y) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [euclideanCoordinateDerivList, ih, fderiv_star,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply]

/-- The exact original mixed source-symbol budget is preserved by conjugate
transpose, including budget zero. Consumer: the reverse modified amplitudes in
`FullLowBounds.Uniform`, for `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem hasFullSourceSymbolBound_conjTranspose {A : FullAmplitude n r} {N : ℕ} {B : ℝ}
    (hb : HasFullSourceSymbolBound A N B) :
    HasFullSourceSymbolBound (fun x y η ↦ (A x y η).conjTranspose) N B := by
  intro is js hij x y η
  have he : matrixAmplitudeCoordinateDerivList js
      (fun z ↦ fullAmplitudeParameterJet is (fun x y η ↦ (A x y η).conjTranspose) x z η) y =
      (matrixAmplitudeCoordinateDerivList js (fun z ↦ fullAmplitudeParameterJet is A x z η) y).conjTranspose := by
    ext i j
    simp only [matrixAmplitudeCoordinateDerivList, fullAmplitudeParameterJet,
      matrixCoefficientJet, Matrix.conjTranspose_apply, scalarCoefficientJet_star,
      sourceCoordinateDerivList_star]
  rw [he, Matrix.frobenius_norm_conjTranspose]
  exact hb is js hij x y η

end JanetCartan.FourierIntegral.FullLowBounds
