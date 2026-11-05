module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.ComplexColumns
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhysicalOperator
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ScalarReduction

/-!
# Identification of the complex correction residual

The complex residual matrix is the original physical operator applied to
`W₁`, column by column, on the fixed-source slice. The factor `i`, the full
zeroth-order matrix and all physical directions are retained. This connects
the primitive amplitude estimate to the literal residual in
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds
open ActualCarriers

variable {d : ℕ}

/-- On the constructed coordinate split, the estimated matrix residual is
exactly `P W₁`, with source time and initial covector fixed. The differentiability
input is supplied by `exists_pencilPrimitiveAmplitudes_cNorm_bounds`; no
operator estimate is assumed (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem pencilCorrectionResidualComplexMatrix_column_eq_physicalApply
    (i : Fin (d + 1))
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (B : Euclidean (d + 1) → MetricTensor (d + 1))
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ) (j : Fin (d + 1))
    (q : TwoTimePoint (Euclidean d))
    (hu : DifferentiableAt ℝ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j) q) :
    (fun a ↦ pencilCorrectionResidualComplexMatrix (coordinateSplit i) Q B h Φ C r c σ q a j) =
      WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
        (fun y a ↦ pencilCorrectionComplexMatrix (coordinateSplit i) Q B h Φ C r c σ
          (physicalSlice (coordinateSplit i) q.2.1 q.2.2.2 y) a j)
        ((coordinateSplit i).symm (q.1, q.2.2.1)) := by
  let e := coordinateSplit i
  let u := pencilCorrectionColumn e Q B h Φ C r c σ j
  let sl := physicalSlice e q.2.1 q.2.2.2
  let y := e.symm (q.1, q.2.2.1)
  have heq : sl y = q := physicalSlice_at e q
  have hd : DifferentiableAt ℝ (u ∘ sl) y := by
    apply DifferentiableAt.comp y _ ((contDiff_physicalSlice e _ _).differentiable (by simp) y)
    change DifferentiableAt ℝ u (sl y)
    rw [heq]
    exact hu
  let L : (Fin (d + 1) → ℝ) →L[ℝ] (Fin (d + 1) → ℂ) :=
    ContinuousLinearMap.pi fun a ↦ Complex.ofRealCLM.comp (ContinuousLinearMap.proj a)
  have hdc := L.differentiableAt.comp y hd
  change DifferentiableAt ℝ (fun z a ↦ ((u ∘ sl) z a : ℂ)) y at hdc
  symm
  change WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
    (fun z ↦ Complex.I • (fun a ↦ ((u ∘ sl) z a : ℂ))) y =
      Complex.I • (fun a ↦ (adaptedPencilApply e Q B u q a : ℂ))
  rw [firstOrderApply_smul _ _ (differentiableAt_const Complex.I) hdc]
  simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply, zero_smul,
    Finset.sum_const_zero, zero_add]
  rw [firstOrderApply_complexPencil_real Q B hd]
  rw [physicalPencilApply_slice i Q B hu]

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds
