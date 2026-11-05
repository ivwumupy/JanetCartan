module

public import JanetCartan.Iteration.PhysicalMean.CanonicalSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.ComponentOperator

/-!
# Keep the high quadratic factor in the original aggregate row

Step 5 of `app:ch_mean_pairs:prop:canonical-estimates` uses the amplitude
`Dν v` on the SAME aggregate raw row. The other factor remains in the SAME
weighted adjoint column. The exact identity and operator-norm consequence
below contain no sum of individual operator bounds, inverse sample weights,
cutoff factor or logarithmic loss.

The scalar amplitude theorem and individual moment estimates must still
bound the modified aggregate row for the original sampled kernels. The
crude individual raw L² bounds below construct its continuous linear map;
they are NOT used in the final aggregate norm estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open CurrentMean SmoothPeriodicFamily ContinuumRow CanonicalChange

variable {n : ℕ} {ι m : Type*} [Fintype ι] [Fintype m]
    {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]

/-- The actual source-dependent aggregate row, with `Dν v` replacing only the
zero-wave amplitude. All raw maps, sample weights, measurement and inverse
are unchanged (`app:ch_mean_pairs:eq:mean-quadratic-low`). -/
def modifiedCanonicalRow (μ : ι → ℝ)
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (CG : ι → ℝ) (hG : ∀ i v, periodicL2Norm (fun x ↦ (G i v).val x ()) ≤ CG i * ‖v‖)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (v : SmoothResidual n) :
    PiLp 2 Raw →L[ℝ] OutputL2 n :=
  CanonicalRow.weightedRow μ
    (smoothRawCrossOperator (fixedSourceDerivative A G Q₀ v) C hC G CG hG)

/-- The modified aggregate row applied to the original aggregate adjoint
is exactly twice the FULL measured Hermitian quadratic source. This proves
the factorization used in Step 5, including both real quadratures and the
literal weights (`app:ch_mean_pairs:eq:mean-quadratic-low`). -/
theorem modifiedCanonicalRow_apply_adjoint (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (CG : ι → ℝ) (hG : ∀ i v, periodicL2Norm (fun x ↦ (G i v).val x ()) ≤ CG i * ‖v‖)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (u v : SmoothResidual n) :
    modifiedCanonicalRow μ C hC A G CG hG Q₀ v
      ((CanonicalRow.weightedRow μ A).adjoint (Q₀ (smoothResidualToL2 n u))) =
        (2 : ℝ) • smoothResidualToL2 n (fixedSourceQuadratic μ C hC A G Q₀ v u) := by
  have hcross := smoothCanonicalResponse_eq_measured_cross μ
    (fixedSourceDerivative A G Q₀ v) C hC A G Q₀ (smoothResidualToL2 n u)
  have htwo : smoothCanonicalResponse μ A
      (smoothRawCrossResponse (fixedSourceDerivative A G Q₀ v) C hC G) Q₀
      (smoothResidualToL2 n u) = (2 : ℝ) • fixedSourceQuadratic μ C hC A G Q₀ v u := by
    simpa only [fixedSourceQuadratic, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
      map_smul, fixedSourceDerivative, LinearMap.comp_apply] using hcross
  rw [← map_smul, ← htwo]
  simp only [modifiedCanonicalRow, CanonicalRow.weightedRow_apply,
    CanonicalRow.weightedRow_adjoint_apply_component, map_smul,
    smoothRawCrossOperator_apply, smoothCanonicalResponse, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    map_sum, smul_smul, Real.mul_self_sqrt (hμ _)]

/-- The low quadratic norm is controlled ONLY by the two aggregate rows and
the actual current inverse. In particular the individual `CG` constants
used to construct the map do not appear in this bound
(`app:ch_mean_pairs:eq:mean-quadratic-low`). -/
theorem two_mul_norm_fixedSourceQuadratic_le_aggregate
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (CG : ι → ℝ) (hG : ∀ i v, periodicL2Norm (fun x ↦ (G i v).val x ()) ≤ CG i * ‖v‖)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (u v : SmoothResidual n) :
    2 * ‖smoothResidualToL2 n (fixedSourceQuadratic μ C hC A G Q₀ v u)‖ ≤
      ‖modifiedCanonicalRow μ C hC A G CG hG Q₀ v‖ *
        ‖CanonicalRow.weightedRow μ A‖ * ‖Q₀‖ * ‖smoothResidualToL2 n u‖ := by
  have he := modifiedCanonicalRow_apply_adjoint μ hμ C hC A G CG hG Q₀ u v
  have hn := (modifiedCanonicalRow μ C hC A G CG hG Q₀ v).le_opNorm
    ((CanonicalRow.weightedRow μ A).adjoint (Q₀ (smoothResidualToL2 n u)))
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hn
  apply hn.trans
  have ha := (CanonicalRow.weightedRow μ A).adjoint.le_opNorm (Q₀ (smoothResidualToL2 n u))
  rw [ContinuousLinearMap.adjoint.norm_map] at ha
  have hq := Q₀.le_opNorm (smoothResidualToL2 n u)
  exact (mul_le_mul_of_nonneg_left
    (ha.trans (mul_le_mul_of_nonneg_left hq (norm_nonneg _))) (norm_nonneg _)).trans_eq (by ring)

end JanetCartan.PhysicalMean
