module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.TransportExtension.CoordinateDerivatives
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.LiteralLimit.SourceBounds

/-!
# Convert the retained PDO coordinate certificate into physical jets

The endpoint and algebraic constructors retain ordered matrix coordinate
derivatives in the paired physical positions. This finite coordinate
expansion supplies the Fréchet derivative norm needed after fixing the
source position. Consumer: the global symbol hypotheses of
`FullEllipticResidualEnvelopes.completeDiagonalAnnularComplement_sobolev`
(`app:ch_response:eq:direct-envelope-profile`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication.TailSymbols
open AmplitudeBound NormalComparison

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

private theorem matrix_iteratedFDeriv_on_coordinate_vectors
    {f : E → Mat} (hf : ContDiff ℝ ∞ f) (k : ℕ)
    (a : Fin k → Fin n) (x : E) :
    iteratedFDeriv ℝ k f x (fun i ↦ EuclideanSpace.single (a i) 1) =
      normalMatrixDerivList (List.ofFn a) f x := by
  induction k generalizing x with
  | zero => simp [normalMatrixDerivList, iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ, normalMatrixDerivList, iteratedFDeriv_succ_apply_left]
    have he : normalMatrixDerivList (List.ofFn (fun i ↦ a i.succ)) f =
        fun y ↦ iteratedFDeriv ℝ k f y (fun i ↦ EuclideanSpace.single (a i.succ) 1) :=
      funext fun y ↦ (ih _ y).symm
    rw [he]
    exact (fderiv_continuousMultilinear_apply_const_apply
      (ContDiff.differentiable_iteratedFDeriv
        (show (k : ℕ∞ω) < ∞ from WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top k)) hf).differentiableAt
      _ _).symm

private theorem norm_matrix_multilinear_le_coordinate_bound {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) Mat)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ a : Fin k → Fin n, ‖T (fun i ↦ EuclideanSpace.single (a i) 1)‖ ≤ B) :
    ‖T‖ ≤ (n : ℝ)^k * B := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have he (i : Fin k) : v i = ∑ j : Fin n, (v i j) • EuclideanSpace.single j 1 := by
    simpa using ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (v i)).symm
  calc
    _ = ‖T (fun i ↦ ∑ j : Fin n, (v i j) • EuclideanSpace.single j 1)‖ := by
      congr 2
      funext i
      exact he i
    _ ≤ ∑ a : Fin k → Fin n, ‖T (fun i ↦ (v i (a i)) • EuclideanSpace.single (a i) 1)‖ := by
      rw [T.map_sum]
      exact norm_sum_le _ _
    _ ≤ ∑ _a : Fin k → Fin n, (∏ i, ‖v i‖) * B := by
      apply Finset.sum_le_sum
      intro a _
      rw [T.map_smul_univ, norm_smul, norm_prod]
      exact mul_le_mul (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
        (fun i _ ↦ PiLp.norm_apply_le (v i) (a i))) (hb a) (norm_nonneg _) (by positivity)
    _ = _ := by simp; ring

/-- The retained Frobenius coordinate certificate controls the full Fréchet
jet with a fixed dimensional cost. It introduces no scalar-entry norm or
new symbol hypothesis (`app:ch_regular_base:eq:actual-normal-amplitude`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_iteratedFDeriv_le_coordinate_certificate
    {f : E → Mat} (hf : ContDiff ℝ ∞ f) (k : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ is : List (Fin n), is.length = k → ∀ y,
      ‖matrixAmplitudeCoordinateDerivList is f y‖ ≤ B) (y : E) :
    ‖iteratedFDeriv ℝ k f y‖ ≤ (n : ℝ)^k * B := by
  apply norm_matrix_multilinear_le_coordinate_bound _ hB
  intro a
  rw [matrix_iteratedFDeriv_on_coordinate_vectors hf,
    normalMatrixDerivList_eq_matrixAmplitudeCoordinateDerivList hf]
  exact hb _ (List.length_ofFn) y

end JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication.TailSymbols
