module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.FiniteSums
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.SourceBounds
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Adjoint
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.Basic
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.MatrixKernels

/-!
# Literal finite matrix two-position operators

The operator for `app:ch_regular_base:thm:actual-calculus` is the existing
Hilbert matrix assembly applied to the actual scalar `twoPositionL2Operator`.
On compact smooth data it equals `matrixFullAmplitudeOperator`, retaining both
physical variables, matrix order, and the source cutoff.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
open JanetCartan.AmplitudeBound
namespace JanetCartan.Pseudodifferential
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin (2 * d))
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- Frobenius derivative budgets imply the exact scalar budgets, without a
change of order, for `app:ch_regular_base:eq:fio-input`. -/
theorem matrixAmplitude_entry_bound {b : E → P → Matrix I J ℂ} {N : ℕ} {M : ℝ}
    (hM : ∀ ξ is, is.length ≤ N → ∀ z,
      ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ M) (i : I) (j : J) :
    HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) N M := by
  intro ξ is hi z
  exact (norm_matrixEntry_le_frobenius _ i j).trans (hM ξ is hi z)

/-- The gain-one Frobenius budget implies each weighted scalar budget in
`app:ch_regular_base:eq:fio-input`, keeping its exact frequency power. -/
theorem matrixAmplitude_weighted_entry_bound {b : E → P → Matrix I J ℂ} {N : ℕ} {M : ℝ}
    (hM : ∀ ξ is, is.length ≤ N → ∀ z,
      (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ M) (i : I) (j : J) :
    ∀ ξ is, is.length ≤ N → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (fun z ↦ b ξ z i j) z‖ ≤ M := by
  intro ξ is hi z
  exact (mul_le_mul_of_nonneg_left (norm_matrixEntry_le_frobenius _ i j)
    (by positivity)).trans (hM ξ is hi z)

/-- The literal matrix operator of `app:ch_regular_base:thm:actual-calculus`,
assembled from actual two-position scalar L² operators. -/
def matrixTwoPositionL2Operator (hd : 0 < d) (R : ℝ) (b : E → P → Matrix I J ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (M : ℝ)
    (hM : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (d + 1)) M) :
    PiLp 2 (fun _ : J ↦ L²) →L[ℂ] PiLp 2 (fun _ : I ↦ L²) :=
  matrixOperator (fun i j ↦ twoPositionL2Operator hd R (fun ξ z ↦ b ξ z i j)
    ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) M (hM i j))

/-- The explicit low L² dimension factor in `app:ch_regular_base:eq:fio-input`. -/
theorem norm_matrixTwoPositionL2Operator_le (hd : 0 < d) (R : ℝ)
    (b : E → P → Matrix I J ℂ) (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (M : ℝ)
    (hM : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (d + 1)) M) :
    ‖matrixTwoPositionL2Operator hd R b hb hs M hM‖ ≤
      (Fintype.card I : ℝ) * (Fintype.card J : ℝ) * (fixedBoxAmplitudeConstant d R * M) :=
  norm_matrixOperator_le_of_entry_bound _ _ (fun _ _ ↦ norm_twoPositionL2Operator_le ..)

/-- The finite Hilbert construction agrees with the existing literal matrix
kernel/composition API on compact smooth data
(`app:ch_regular_base:thm:actual-calculus`). -/
theorem matrixTwoPositionL2Operator_ae_matrixFullAmplitudeOperator
    (hd : 0 < d) (R : ℝ) (b : E → P → Matrix I J ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (M : ℝ)
    (hM : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (d + 1)) M)
    (u : E → J → ℂ) (hu : ∀ j, MemLp (fun y ↦ u y j) 2)
    (hc : ∀ j, ContDiff ℝ (d + 1) (fun y ↦ u y j))
    (hcs : ∀ j, HasCompactSupport (fun y ↦ u y j)) (i : I) :
    (matrixTwoPositionL2Operator hd R b hb hs M hM
      (WithLp.toLp 2 (fun j ↦ (hu j).toLp (fun y ↦ u y j)))) i =ᵐ[volume]
      fun x ↦ matrixFullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u x i := by
  let B := fun i j ↦ twoPositionL2Operator hd R (fun ξ z ↦ b ξ z i j)
    ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) M (hM i j)
  change matrixOperator B _ i =ᵐ[volume] _
  rw [matrixOperator_apply]
  have he : ∀ᵐ x ∂volume, ∀ j, B i j ((hu j).toLp _) x =
      fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y) i j) (fun y ↦ u y j) x :=
    ae_all_iff.mpr (fun j ↦ twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_physicalBudget
      hd R _ _ _ M (hM i j) _ (hu j) (hc j) (hcs j))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j ↦ B i j ((hu j).toLp _)), he]
    with x hx he
  exact hx.trans (Finset.sum_congr rfl (fun j _ ↦ he j))

/-- The literal Hilbert adjoint is the reversed conjugate transpose matrix
kernel, including all physical masks (`app:ch_regular_base:thm:actual-calculus`). -/
theorem matrixTwoPositionL2Operator_adjoint_ae_matrixFullAmplitudeOperator
    (hd : 0 < d) (R : ℝ) (b : E → P → Matrix I J ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (M : ℝ)
    (hM : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (d + 1)) M)
    (u : E → I → ℂ) (hu : ∀ i, MemLp (fun y ↦ u y i) 2)
    (hc : ∀ i, ContDiff ℝ (d + 1) (fun y ↦ u y i))
    (hcs : ∀ i, HasCompactSupport (fun y ↦ u y i)) (j : J) :
    ((matrixTwoPositionL2Operator hd R b hb hs M hM).adjoint
      (WithLp.toLp 2 (fun i ↦ (hu i).toLp (fun y ↦ u y i)))) j =ᵐ[volume]
      fun x ↦ matrixFullAmplitudeOperator
        (fun x y ξ ↦ (b ξ (pairedPosition y x)).conjTranspose) u x j := by
  let B := fun i j ↦ twoPositionL2Operator hd R (fun ξ z ↦ b ξ z i j)
    ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) M (hM i j)
  change (matrixOperator B).adjoint _ j =ᵐ[volume] _
  rw [matrixOperator_adjoint, matrixOperator_apply]
  have he : ∀ᵐ x ∂volume, ∀ i, (B i j).adjoint ((hu i).toLp _) x =
      fullAmplitudeOperator (fun x y ξ ↦ star (b ξ (pairedPosition y x) i j))
        (fun y ↦ u y i) x := by
    apply ae_all_iff.mpr
    intro i
    dsimp only [B]
    rw [twoPositionL2Operator_adjoint hd R (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) M (hM i j)]
    have h := twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_physicalBudget hd R
      (adjointAmplitude (fun ξ z ↦ b ξ z i j))
      (contDiff_adjointAmplitude ((matrixEntryEvaluation i j).contDiff.comp hb))
      (supportedInCenteredBox_adjointAmplitude (fun ξ ↦ hs ξ i j)) M
      (hasAmplitudeDerivativeBound_adjointAmplitude
        (fun _ ↦ ((matrixEntryEvaluation i j).contDiff.comp hb).comp
          (contDiff_const.prodMk contDiff_id)) (hM i j))
      (fun y ↦ u y i) (hu i) (hc i) (hcs i)
    filter_upwards [h] with x hx
    simpa only [adjointAmplitude_pairedPosition] using hx
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ (B i j).adjoint ((hu i).toLp _)), he]
    with x hx he
  exact hx.trans (Finset.sum_congr rfl (fun i _ ↦ he i))

end JanetCartan.Pseudodifferential
