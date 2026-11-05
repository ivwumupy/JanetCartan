module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.PrimitiveBudget.Coordinates
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.Matrix
public import JanetCartan.Analysis.Operator.RealQuadratures

/-!
# Operator consequences of the full carrier entry budget

The primitive producers in `CarrierNormalRealization.PrimitiveBudget` supply
all analytic inputs to these bounds for `app:ch_background:prop:bg-frame`,
Step 1. The reflected amplitude already includes the real-quadrature factor.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol TransportKernel
open Pseudodifferential AmplitudeBound PeriodicLocalL2
variable {n N : ℕ}

/-- Scalar entry bounds give the literal full vector PDO, its periodic transfer,
and its real compression the same bound with explicit finite matrix factor.
This is the operator deduction used by both primitive producers, and does not
assume an identification with the normal (`app:ch_background:prop:bg-frame`,
Step 1; `app:ch_background:eq:bg-real-symbol`). -/
theorem fullReflectedMatrixAmplitude_operator_bounds
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S)))
    (s : ℕ) (A : ℝ)
    (hA : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j) s A)
    (hn : 0 < n) (Rbox : ℝ)
    (hsupport : ∀ x, a.measurement x ≠ 0 → ∀ j, |x j| ≤ Rbox)
    (hreserve : 2 * (n + 1) ≤ s) :
    let T := vectorTwoPositionL2Operator hn Rbox (fullReflectedMatrixAmplitude a J u Ω S)
      hb (fullReflectedMatrixAmplitude_supportedInCenteredBox a J u Ω S Rbox hsupport)
      A (fun i j ξ is his ↦ hA i j ξ is (his.trans hreserve))
    ‖T‖ ≤ (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * A) ∧
      ‖transferOperator T‖ ≤ (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * A) ∧
      ‖realOutputCompression (transferOperator T)‖ ≤
        (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * A) := by
  dsimp only
  have hbound : ‖vectorTwoPositionL2Operator hn Rbox (fullReflectedMatrixAmplitude a J u Ω S)
      hb (fullReflectedMatrixAmplitude_supportedInCenteredBox a J u Ω S Rbox hsupport)
      A (fun i j ξ is his ↦ hA i j ξ is (his.trans hreserve))‖ ≤
        (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * A) := by
    unfold vectorTwoPositionL2Operator
    calc
      _ ≤ (Fintype.card (Fin n) : ℝ) * (Fintype.card (Fin n) : ℝ) *
          (fixedBoxAmplitudeConstant n Rbox * A) :=
        ContinuumCommutator.norm_vectorMatrixL2Operator_le_of_entry_bound _ _
          (fun _ _ ↦ norm_twoPositionL2Operator_le ..)
      _ = _ := by simp only [Fintype.card_fin, pow_two]
  exact ⟨hbound, (norm_transferOperator_le _).trans hbound,
    (realOutputCompression_norm_le _).trans ((norm_transferOperator_le _).trans hbound)⟩

end JanetCartan.ContinuumRow.CarrierNormalRealization
