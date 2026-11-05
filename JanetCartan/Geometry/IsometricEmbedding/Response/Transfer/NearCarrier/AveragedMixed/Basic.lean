module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The literal averaged mixed phase matrix

The matrix immediately before `app:ch_response:eq:direct-envelope-profile`.
Covectors are physical covectors; unit-torus indices enter as `2π k`.
Matrices retain the Frobenius norm. The separate continuous-linear realization
is used for operator-norm inverse gaps.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer

-- Match the topology in integrability to the chosen Frobenius norm.
local instance (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

/-- Euclidean operator realization of a matrix, for the inverse gap in
`app:ch_response:thm:response-literal-transfer`. This changes neither the
matrix norm instance nor the physical covector convention. -/
def mixedMatrixOperatorEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ ≃L[ℝ] (Euclidean n →L[ℝ] Euclidean n) :=
  (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

/-- The physical mixed Hessian as a bounded Euclidean operator
(`app:ch_response:thm:response-literal-transfer`). -/
def mixedPhaseOperator {n : ℕ} (S : Euclidean n → Euclidean n → ℝ)
    (x η : Euclidean n) : Euclidean n →L[ℝ] Euclidean n :=
  mixedMatrixOperatorEquiv n (FourierIntegral.mixedPhaseMatrix S x η)

/-- The actual segment average `Bρ(x,δ)` of
`app:ch_response:thm:response-literal-transfer`. -/
def averagedMixedMatrix {n : ℕ} (S : Euclidean n → Euclidean n → ℝ)
    (ζ : Euclidean n) (ρ : ℝ) (x δ : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  ∫ t in (0 : ℝ)..1, FourierIntegral.mixedPhaseMatrix S x (ρ • ζ + t • δ)

/-- The Euclidean operator corresponding to the literal averaged matrix
(`app:ch_response:thm:response-literal-transfer`). -/
def averagedMixedOperator {n : ℕ} (S : Euclidean n → Euclidean n → ℝ)
    (ζ : Euclidean n) (ρ : ℝ) (x δ : Euclidean n) : Euclidean n →L[ℝ] Euclidean n :=
  mixedMatrixOperatorEquiv n (averagedMixedMatrix S ζ ρ x δ)

/-- Matrix integration agrees with operator integration for the actual
segment average (`app:ch_response:thm:response-literal-transfer`). -/
theorem averagedMixedOperator_eq_integral {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (x δ : Euclidean n)
    (hi : IntervalIntegrable
      (fun t : ℝ ↦ FourierIntegral.mixedPhaseMatrix S x (ρ • ζ + t • δ)) volume 0 1) :
    averagedMixedOperator S ζ ρ x δ =
      ∫ t in (0 : ℝ)..1, mixedPhaseOperator S x (ρ • ζ + t • δ) := by
  exact ((mixedMatrixOperatorEquiv n).toContinuousLinearMap.intervalIntegral_comp_comm hi).symm

/-- Coordinates of the operator realization agree with matrix multiplication
(`app:ch_response:thm:response-literal-transfer`). -/
theorem mixedMatrixOperatorEquiv_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Euclidean n) (i : Fin n) :
    mixedMatrixOperatorEquiv n A v i = ∑ j, A i j * v j := rfl

end JanetCartan.ResponseTransfer
