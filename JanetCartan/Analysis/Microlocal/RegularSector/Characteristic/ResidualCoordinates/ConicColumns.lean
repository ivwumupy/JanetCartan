module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.Columns
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.Kernel
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.EvolutionCoordinates

/-!
# The actual conic columns in complete-residual coordinates

This is the coordinate connection for the published `ConicAmplitude` producer.
No conic null equation or cancellation is assumed. The input differential,
null and correction identities are the local outputs of
`exists_pencil_leading_amplitude`, at the same normalized point. All physical
coefficients, including `B`, and the factor `i` in `W₁` are retained.
Consumer: `CompleteResidual.completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:two-term-null-identity` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification AmplitudeBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d + 1)

variable (ℓ : Euclidean d →L[ℝ] ℝ) (i : Fin (d + 1))
  (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
  (B : Euclidean (d + 1) → MetricTensor (d + 1))
  (h : RootState (Euclidean d) → ℝ)
  (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
  (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))) (r c : Fin (d + 1))
  (σ : RootState (Euclidean d) → ℝ)

local notation "M₀" => pencilLeadingComplexMatrix (coordinateSplit i) Q B h Φ C r c σ
local notation "M₁" => pencilCorrectionComplexMatrix (coordinateSplit i) Q B h Φ C r c σ
local notation "M₂" => pencilCorrectionResidualComplexMatrix (coordinateSplit i) Q B h Φ C r c σ
local notation "W₀" => curryCharacteristicMatrix (ConicAmplitude.extend ℓ 0 M₀)
local notation "W₁" => curryCharacteristicMatrix (ConicAmplitude.extend ℓ 1 M₁)

/-- The conic correction is the original correction at the normalized
covector, with exactly one inverse radial factor. Source:
`app:ch_regular_base:eq:two-term-null-identity`. -/
theorem conicCorrection_eq (t s : ℝ) (y η : Euclidean d) :
    W₁ t s y η = (ℓ η)⁻¹ • correction i Q B h Φ C r c σ t s y ((ℓ η)⁻¹ • η) := by
  simp only [curryCharacteristicMatrix, ConicAmplitude.extend, pow_one]
  rfl

/-- The continued upper endpoint is exactly the original transported source
symbol and oblique projector at the same normalized covector. The diagonal
input is the initial-value conclusion of `exists_pencil_leading_amplitude`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem conic_leading_endpoint (x : E) (η : Euclidean d)
    (hinit : ∀ j, pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j
      (x 0, rootState x ((ℓ η)⁻¹ • η)) =
      (σ (rootState x ((ℓ η)⁻¹ • η)) * minorLeftNullvector
        (rootPencil (coordinateSplit i) Q h (rootState x ((ℓ η)⁻¹ • η)))
        (rootTimeCoefficient (coordinateSplit i) Q (rootState x ((ℓ η)⁻¹ • η))) r c j) •
          minorRightNullvector (rootPencil (coordinateSplit i) Q h
            (rootState x ((ℓ η)⁻¹ • η))) r c) :
    (coefficient i Q x 0).map Complex.ofReal * W₀ (x 0) (x 0) (spatialPart x) η =
      sourceSymbol σ x ((ℓ η)⁻¹ • η) • projector i Q h r c x ((ℓ η)⁻¹ • η) := by
  have he : W₀ (x 0) (x 0) (spatialPart x) η =
      leading i Q B h Φ C r c σ (x 0) (x 0) (spatialPart x) ((ℓ η)⁻¹ • η) := by
    ext k j
    simp [curryCharacteristicMatrix, ConicAmplitude.extend, ConicPhase.normalize,
      pencilLeadingComplexMatrix, complexColumnMatrix, leading]
  rw [he]
  exact leading_endpoint i Q B h Φ C r c σ x ((ℓ η)⁻¹ • η) hinit

/-- Matrix differentiability needed by `twoTimePhysicalApply_column`, derived
from the same actual local correction columns. Source:
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem differentiableAt_conicCorrection_slice (s : ℝ) (η : Euclidean d) (x : E)
    (hv : ∀ j, DifferentiableAt ℝ
      (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (ConicPhase.normalize ℓ (x 0, (s, (spatialPart x, η))))) :
    DifferentiableAt ℝ (fun y ↦ W₁ (y 0) s (spatialPart y) η) x := by
  simp only [conicCorrection_eq]
  exact (differentiableAt_correction_slice i Q B h Φ C r c σ s ((ℓ η)⁻¹ • η) x hv).const_smul
      ((ℓ η)⁻¹ : ℝ)

/-- The residual consumer's matrix `P W₁` is exactly the published physical
conic residual matrix, without a change of norm or Fourier convention.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem conicCorrection_apply (s : ℝ) (η : Euclidean d) (x : E)
    (hv : ∀ j, DifferentiableAt ℝ
      (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (ConicPhase.normalize ℓ (x 0, (s, (spatialPart x, η))))) :
    twoTimePhysicalApply (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
      (fun y ↦ (zeroth i B y).map Complex.ofReal) W₁ (x 0) s (spatialPart x) η =
      ConicAmplitude.extend ℓ 1 M₂ (x 0, (s, (spatialPart x, η))) := by
  simp only [ConicPhase.normalize] at hv
  have hw := differentiableAt_conicCorrection_slice ℓ i Q B h Φ C r c σ s η x hv
  ext k j
  have hc := twoTimePhysicalApply_column
    (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
    (fun y ↦ (zeroth i B y).map Complex.ofReal) W₁ s η x hw j
  rw [← congrFun hc k]
  let f : E → Fin (d + 1) → ℂ := fun y a ↦
    ConicAmplitude.extend ℓ 1 M₁ (physicalSlice (coordinateSplit i) s η y) a j
  have hf : DifferentiableAt ℝ f (physicalCoordinates i x) := by
    have hv' := ((physicalSlice_physicalCoordinates i s ((ℓ η)⁻¹ • η) x).symm ▸ hv j).comp _
      ((contDiff_physicalSlice (coordinateSplit i) s ((ℓ η)⁻¹ • η)).differentiable (by simp) _)
    have hc' : DifferentiableAt ℝ (fun y a ↦
        (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j
          (physicalSlice (coordinateSplit i) s ((ℓ η)⁻¹ • η) y) a : ℂ))
        (physicalCoordinates i x) := differentiableAt_pi.mpr fun a ↦
      Complex.ofRealCLM.differentiableAt.comp _ (differentiableAt_pi.mp hv' a)
    convert (hc'.const_smul Complex.I).const_smul ((ℓ η)⁻¹ : ℝ) using 1
    ext y a
    simp [f, ConicAmplitude.extend, ConicPhase.normalize, physicalSlice,
      pencilCorrectionComplexMatrix, complexColumnMatrix]
  have he : (fun y a ↦ W₁ (y 0) s (spatialPart y) η a j) = f ∘ physicalCoordinates i := by
    funext y a
    simp only [f, Function.comp_apply, physicalSlice_physicalCoordinates]
    rfl
  rw [he, firstOrderApply_physicalCoordinates i Q B hf]
  exact congrFun (ConicAmplitude.pencilCorrectionResidual_extend_column_eq_physicalApply
    ℓ i Q B h Φ C r c σ j (x 0, (s, (spatialPart x, η))) (hv j)).symm k

/-- Transfer the actual conic physical cancellation into the residual's
canonical time-zero coordinates. All local hypotheses are outputs of the
same `exists_pencil_leading_amplitude`, not assumptions on extended kernels.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem conic_column_cancellation (s : ℝ) (η : Euclidean d) (x : E)
    (hℓ : 0 < ℓ η)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (ConicPhase.normalize ℓ (x 0, (s, (spatialPart x, η)))))
      (ConicPhase.normalize ℓ (x 0, (s, (spatialPart x, η)))))
    (hclock : (twoTimeState Φ (C.symm (ConicPhase.normalize ℓ
      (x 0, (s, (spatialPart x, η)))))).1 = x 0)
    (hy : (twoTimeState Φ (C.symm (ConicPhase.normalize ℓ
      (x 0, (s, (spatialPart x, η)))))).2.1 = spatialPart x)
    (hu : ∀ j, DifferentiableAt ℝ (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (ConicPhase.normalize ℓ (x 0, (s, (spatialPart x, η)))))
    (hv : ∀ j, DifferentiableAt ℝ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (ConicPhase.normalize ℓ (x 0, (s, (spatialPart x, η)))))
    (hnull : ∀ j, rootPencil (coordinateSplit i) Q h
      (twoTimeState Φ (C.symm (ConicPhase.normalize ℓ (x 0, (s, (spatialPart x, η)))))) *ᵥ
        pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j
          (ConicPhase.normalize ℓ (x 0, (s, (spatialPart x, η)))) = 0)
    (hcorr : ∀ j, rootPencil (coordinateSplit i) Q h
      (twoTimeState Φ (C.symm (ConicPhase.normalize ℓ (x 0, (s, (spatialPart x, η)))))) *ᵥ
        pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j
          (ConicPhase.normalize ℓ (x 0, (s, (spatialPart x, η)))) =
      adaptedPencilApply (coordinateSplit i) Q B
        (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j)
          (ConicPhase.normalize ℓ (x 0, (s, (spatialPart x, η))))) (j : Fin (d + 1)) :
    WKB.firstOrderApply (fun y a ↦ ((coefficient i Q y a).map Complex.ofReal).mulVecLin)
      (fun y ↦ ((zeroth i B y).map Complex.ofReal).mulVecLin)
      (fun y ↦ Complex.exp (Complex.I * (ConicPhase.phase ℓ C
        (y 0, (s, (spatialPart y, η))) : ℂ)) •
          (fun k ↦ (W₀ + W₁) (y 0) s (spatialPart y) η k j)) x =
      Complex.exp (Complex.I * (ConicPhase.phase ℓ C
        (x 0, (s, (spatialPart x, η))) : ℂ)) •
        (fun k ↦ twoTimePhysicalApply (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
          (fun y ↦ (zeroth i B y).map Complex.ofReal) W₁ (x 0) s (spatialPart x) η k j) := by
  simp only [ConicPhase.normalize] at hu hv hphase
  let sl := physicalSlice (coordinateSplit i) s ((ℓ η)⁻¹ • η)
  have hs : DifferentiableAt ℝ sl (physicalCoordinates i x) :=
    (contDiff_physicalSlice (coordinateSplit i) s ((ℓ η)⁻¹ • η)).differentiable (by simp) _
  have heq := physicalSlice_physicalCoordinates i s ((ℓ η)⁻¹ • η) x
  have hu' := (heq.symm ▸ hu j).comp _ hs
  have hv' := (heq.symm ▸ hv j).comp _ hs
  have hp := (heq.symm ▸ hphase.differentiableAt).comp _ hs
  have huc : DifferentiableAt ℝ (fun y k ↦
      (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j (sl y) k : ℂ))
      (physicalCoordinates i x) := differentiableAt_pi.mpr fun k ↦
    Complex.ofRealCLM.differentiableAt.comp _ (differentiableAt_pi.mp hu' k)
  have hvc : DifferentiableAt ℝ (fun y k ↦
      (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j (sl y) k : ℂ))
      (physicalCoordinates i x) := differentiableAt_pi.mpr fun k ↦
    Complex.ofRealCLM.differentiableAt.comp _ (differentiableAt_pi.mp hv' k)
  have hk : DifferentiableAt ℝ
      (ConicAmplitude.pencilKernelColumn ℓ (coordinateSplit i) Q B h Φ C r c σ j s η)
      (physicalCoordinates i x) := by
    have hsum := huc.add ((hvc.const_smul Complex.I).const_smul ((ℓ η)⁻¹ : ℝ))
    have h := (((differentiableAt_const Complex.I).mul
      (Complex.ofRealCLM.differentiableAt.comp _ (hp.const_mul (ℓ η)))).cexp).smul hsum
    convert h using 1
    ext y k
    simp only [ConicAmplitude.pencilKernelColumn, ConicAmplitude.extend,
      ConicPhase.phase, ConicPhase.extend, ConicPhase.normalize, physicalSlice,
      pencilLeadingComplexMatrix, pencilCorrectionComplexMatrix, complexColumnMatrix,
      pow_zero, one_smul, pow_one, Matrix.smul_apply, Pi.smul_apply,
      Function.comp_apply, Pi.mul_apply, Complex.ofRealCLM_apply, sl]
    rfl
  have he : (fun y ↦ Complex.exp (Complex.I * (ConicPhase.phase ℓ C
      (y 0, (s, (spatialPart y, η))) : ℂ)) •
        (fun k ↦ (W₀ + W₁) (y 0) s (spatialPart y) η k j)) =
      ConicAmplitude.pencilKernelColumn ℓ (coordinateSplit i) Q B h Φ C r c σ j s η ∘
        physicalCoordinates i := by
    funext y k
    simp only [Function.comp_apply, ConicAmplitude.pencilKernelColumn,
      physicalSlice_physicalCoordinates]
    rfl
  rw [he, firstOrderApply_physicalCoordinates i Q B hk,
    conicCorrection_apply ℓ i Q B h Φ C r c σ s η x hv]
  exact ConicAmplitude.firstOrder_pencilKernelColumn ℓ i Q B h Φ C r c σ j
    (x 0, (s, (spatialPart x, η))) hℓ hphase hclock hy (hu j) (hv j) (hnull j) (hcorr j)

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
