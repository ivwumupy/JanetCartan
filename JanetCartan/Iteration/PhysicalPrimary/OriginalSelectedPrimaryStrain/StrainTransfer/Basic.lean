module

public import JanetCartan.Iteration.PhysicalPairs.OriginalTensorLag
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.QuadratureResidual

/-!
# The original uncut tensor equation and both strain quadratures

The consumer is the actual source-to-strain comparison in `main:eq:primary-strain`.
The full original frame agrees with the projected frame on the original
coefficient ball. This cancels the source part of the classical equation,
leaving the original smooth discrepancy. The two real residuals are then
combined for the same complex corrected atom, without an output cutoff.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer

open AmbientResponse ProjectedStressFrame ProtectedFlow CorrectedAtoms ResponseSourceExtension

/-- The source of the extended frame is the original projected source on the
entire coefficient ball, including its boundary (used in `main:eq:primary-strain`). -/
theorem extended_stress_eq_on_coefficient_ball {n N : ℕ}
    (ext : BallExtension.Parameters (Euclidean n))
    (F : Euclidean n → Euclidean N) (H : MetricField n)
    {x : Euclidean n} (hx : x ∈ closedBall ext.center ext.radius) :
    (WithLp.toLp 2 (stressSource (extendedProjectedStress ext F) H x) : Euclidean n) =
      WithLp.toLp 2 (stressSource (projectedStress F) H x) := by
  have hQ := affineFrameExtension_eqOn ext (projectedStress F) hx
  change extendedProjectedStress ext F x = projectedStress F x at hQ
  apply congrArg (WithLp.toLp 2)
  funext i
  change (1 / 2 : ℝ) * tensorPairing (extendedProjectedStress ext F x i) (H x) =
    (1 / 2 : ℝ) * tensorPairing (projectedStress F x i) (H x)
  rw [hQ]

/-- Cancel only the original tensor forcing in the full classical equation.
Its remaining error is the original source-minus-identity discrepancy
(`main:eq:lag-strain`). -/
theorem bound_after_tensor_forcing_cancellation {n N : ℕ}
    (ext : BallExtension.Parameters (Euclidean n))
    (F : Euclidean n → Euclidean N) (H : MetricField n)
    (forcing discrepancy : Euclidean n → Euclidean n)
    (hforcing : forcing = fun x ↦
      (WithLp.toLp 2 (stressSource (extendedProjectedStress ext F) H x) : Euclidean n))
    {x : Euclidean n} (hx : x ∈ closedBall ext.center ext.radius)
    (T : MetricTensor n) (C : ℝ)
    (h : ‖T‖ ≤ C * ‖forcing x + discrepancy x -
      (WithLp.toLp 2 (stressSource (projectedStress F) H x) : Euclidean n)‖) :
    ‖T‖ ≤ C * ‖discrepancy x‖ := by
  have hf : forcing x = WithLp.toLp 2 (stressSource (projectedStress F) H x) :=
    (congrFun hforcing x).trans (extended_stress_eq_on_coefficient_ball ext F H hx)
  simpa only [hf, add_sub_cancel_left] using h

/-- Both original real quadrature errors control the literal complex
corrected atom. No global response smoothness or second cutoff is used
(`main:eq:primary-strain`, `main:eq:lag-strain`). -/
theorem corrected_atom_strain_le_quadrature_errors {n N : ℕ}
    (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (Z : Euclidean n → EuclideanSpace ℂ (Fin N)) {x : Euclidean n}
    (hχ : χ x = 1) (hZ : DifferentiableAt ℝ Z x)
    (hR : DifferentiableAt ℝ (B (tensorFieldRealPart (complexAtomicSource F χ Z))) x)
    (hI : DifferentiableAt ℝ (B (tensorFieldImagPart (complexAtomicSource F χ Z))) x)
    (C εR εI : ℝ)
    (heR : ‖linearizedMetric F (B (tensorFieldRealPart (complexAtomicSource F χ Z))) x -
      tensorFieldRealPart (complexAtomicSource F χ Z) x‖ ≤ C * εR)
    (heI : ‖linearizedMetric F (B (tensorFieldImagPart (complexAtomicSource F χ Z))) x -
      tensorFieldImagPart (complexAtomicSource F χ Z) x‖ ≤ C * εI) :
    ‖WKB.complexLinearizedMetric F (complexCorrectedAtom F χ B Z) x‖ ≤
      C * (εR + εI) := by
  let H := complexAtomicSource F χ Z
  have hB : DifferentiableAt ℝ (complexifyResponse B H) x :=
    (euclideanComplexInclusion.differentiableAt.comp x hR).add
      ((euclideanComplexInclusion.differentiableAt.comp x hI).const_smul Complex.I)
  rw [complexCorrectedAtom_strain F χ B Z hχ hZ hB, norm_neg,
    complexAtomicResidual_eq_quadratures F B H hR hI]
  calc
    _ ≤ ‖(linearizedMetric F (B (tensorFieldRealPart H)) x - tensorFieldRealPart H x).map
        Complex.ofReal‖ +
      ‖Complex.I • (linearizedMetric F (B (tensorFieldImagPart H)) x -
        tensorFieldImagPart H x).map Complex.ofReal‖ := norm_add_le _ _
    _ = ‖linearizedMetric F (B (tensorFieldRealPart H)) x - tensorFieldRealPart H x‖ +
      ‖linearizedMetric F (B (tensorFieldImagPart H)) x - tensorFieldImagPart H x‖ := by
        rw [norm_smul, Complex.norm_I, one_mul,
          Matrix.frobenius_norm_map_eq _ Complex.ofReal Complex.norm_real,
          Matrix.frobenius_norm_map_eq _ Complex.ofReal Complex.norm_real]
    _ ≤ C * εR + C * εI := add_le_add heR heI
    _ = _ := by ring

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer
end
