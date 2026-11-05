module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.VectorInteger
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Bridges

/-!
# Literal vector kernels and the existing graph normal

The estimates in `app:ch_regular_base:eq:fio-input` act on the existing literal
matrix integral and graph normal, rather than an unrelated bounded extension.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
open JanetCartan.AmplitudeBound
namespace JanetCartan.Pseudodifferential
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin (2 * d))

/-- Vector L² agrees with the literal matrix kernel/composition API, for
`app:ch_regular_base:thm:actual-calculus`. -/
theorem vectorTwoPositionL2Operator_ae_matrixFullAmplitudeOperator
    (hd : 0 < d) (R : ℝ) (b : E → P → Matrix I J ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (M : ℝ)
    (hM : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (d + 1)) M)
    (u : E → EuclideanSpace ℂ J) (hu : MemLp u 2)
    (hc : ∀ j, ContDiff ℝ (d + 1) (fun y ↦ u y j))
    (hcs : ∀ j, HasCompactSupport (fun y ↦ u y j)) :
    vectorTwoPositionL2Operator hd R b hb hs M hM (hu.toLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2
        (matrixFullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) (fun y j ↦ u y j) x) := by
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro i
  simp only [vectorTwoPositionL2Operator, finiteL2CoordinateIsometry_vectorMatrixL2Operator,
    finiteL2CoordinateIsometry_toLp]
  exact matrixTwoPositionL2Operator_ae_matrixFullAmplitudeOperator hd R b hb hs M hM
    (fun y j ↦ u y j) (fun j ↦ hu.eval_piLp j) hc hcs i

/-- The vector Hilbert adjoint retains the reversed source cutoffs and
conjugate transpose (`app:ch_regular_base:thm:actual-calculus`). -/
theorem vectorTwoPositionL2Operator_adjoint_ae_matrixFullAmplitudeOperator
    (hd : 0 < d) (R : ℝ) (b : E → P → Matrix I J ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (M : ℝ)
    (hM : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (d + 1)) M)
    (u : E → EuclideanSpace ℂ I) (hu : MemLp u 2)
    (hc : ∀ i, ContDiff ℝ (d + 1) (fun y ↦ u y i))
    (hcs : ∀ i, HasCompactSupport (fun y ↦ u y i)) :
    (vectorTwoPositionL2Operator hd R b hb hs M hM).adjoint (hu.toLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2
        (matrixFullAmplitudeOperator (fun x y ξ ↦ (b ξ (pairedPosition y x)).conjTranspose)
          (fun y i ↦ u y i) x) := by
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro j
  simp only [vectorTwoPositionL2Operator, vectorMatrixL2Operator_adjoint,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, finiteL2CoordinateIsometry_toLp]
  simpa only [matrixTwoPositionL2Operator, matrixOperator_adjoint] using
    matrixTwoPositionL2Operator_adjoint_ae_matrixFullAmplitudeOperator hd R b hb hs M hM
      (fun y i ↦ u y i) (fun i ↦ hu.eval_piLp i) hc hcs j

/-- The graph normal producer uses exactly the vector operator estimated here
(`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem vectorTwoPositionL2Operator_eq_graphNormalL2Operator {r : ℕ}
    (hd : 0 < d) (R : ℝ) (b : E → P → Matrix (Fin r) (Fin r) ℂ)
    (M : ℝ) (hb : FourierIntegral.GraphNormalAmplitudeBounds b R M) :
    vectorTwoPositionL2Operator hd R b hb.smooth hb.support M hb.entry_bound =
      FourierIntegral.graphNormalL2Operator hd R b M hb := by
  unfold vectorTwoPositionL2Operator FourierIntegral.graphNormalL2Operator
  exact vectorMatrixL2Operator_eq_graphMatrixL2Operator _

end JanetCartan.Pseudodifferential
