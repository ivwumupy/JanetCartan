module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.Symbols

/-!
# Physical column cancellation in canonical residual coordinates

This transfers the actual column producer through the coordinate permutation
and uses `CompleteResidual.twoTimePhysicalApply_column` to identify its RHS
with the matrix `P W₁`. It does not postulate the residual's `hcancel` premise.
The local phase differential and the null/transport outputs below are exactly
those of `exists_pencil_leading_amplitude`, on the same witnesses.
Source: `app:ch_regular_base:eq:two-term-null-identity` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)

/-- Slicing the same physical point gives exactly the consumer's two-time
arguments, with source time and covector fixed.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
@[simp] theorem physicalSlice_physicalCoordinates (i : Fin (d + 1))
    (s : ℝ) (η : Euclidean d) (x : E) :
    physicalSlice (coordinateSplit i) s η (physicalCoordinates i x) =
      (x 0, (s, (spatialPart x, η))) := by
  simp [physicalSlice, physicalCoordinates]
  rfl

private theorem differentiableAt_complex_column
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : F → Fin (d + 1) → ℝ} {x : F} (hu : DifferentiableAt ℝ u x) :
    DifferentiableAt ℝ (fun y j ↦ (u y j : ℂ)) x :=
  differentiableAt_pi.mpr fun j ↦ Complex.ofRealCLM.differentiableAt.comp x
    (differentiableAt_pi.mp hu j)

/-- Local regularity of the actual correction matrix follows from the
column producer, without extending a chart identity to other points.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem differentiableAt_correction_slice
    (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ)
    (s : ℝ) (η : Euclidean d) (x : E)
    (hv : ∀ j, DifferentiableAt ℝ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (x 0, (s, (spatialPart x, η)))) :
    DifferentiableAt ℝ (fun y ↦ correction i Q B h Φ C r c σ (y 0) s (spatialPart y) η) x := by
  have hs := (contDiff_physicalSlice (coordinateSplit (0 : Fin (d + 1))) s η).differentiable
    (by simp) x
  apply differentiableAt_pi.mpr
  intro k
  apply differentiableAt_pi.mpr
  intro j
  have hd := (differentiableAt_pi.mp (hv j) k).comp x
    (show DifferentiableAt ℝ (fun y : E ↦ (y 0, (s, (spatialPart y, η)))) x from hs)
  exact (differentiableAt_const Complex.I).mul
    (Complex.ofRealCLM.differentiableAt.comp x hd)

/-- The matrix residual `P W₁` has exactly the original physical correction
derivatives. Both the factor `i` and `B` are retained.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem correction_apply_column
    (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ)
    (s : ℝ) (η : Euclidean d) (x : E)
    (hv : ∀ j, DifferentiableAt ℝ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (x 0, (s, (spatialPart x, η)))) (j : Fin (d + 1)) :
    (fun k ↦ twoTimePhysicalApply (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
      (fun y ↦ (zeroth i B y).map Complex.ofReal) (correction i Q B h Φ C r c σ)
      (x 0) s (spatialPart x) η k j) =
    WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
      (fun y ↦ Complex.I • (fun k ↦ (pencilCorrectionColumn (coordinateSplit i)
        Q B h Φ C r c σ j (physicalSlice (coordinateSplit i) s η y) k : ℂ)))
      (physicalCoordinates i x) := by
  rw [← twoTimePhysicalApply_column _ _ _ s η x
    (differentiableAt_correction_slice i Q B h Φ C r c σ s η x hv) j]
  have hv' : DifferentiableAt ℝ (fun y ↦ pencilCorrectionColumn (coordinateSplit i)
      Q B h Φ C r c σ j (physicalSlice (coordinateSplit i) s η y)) (physicalCoordinates i x) :=
    ((physicalSlice_physicalCoordinates i s η x).symm ▸ hv j).comp _
      ((contDiff_physicalSlice (coordinateSplit i) s η).differentiable (by simp) _)
  have he : (fun y k ↦ correction i Q B h Φ C r c σ (y 0) s (spatialPart y) η k j) =
      (fun y ↦ Complex.I • (fun k ↦ (pencilCorrectionColumn (coordinateSplit i)
        Q B h Φ C r c σ j (physicalSlice (coordinateSplit i) s η y) k : ℂ))) ∘
        physicalCoordinates i := by
    funext y k
    simp [correction]
  rw [he]
  exact firstOrderApply_physicalCoordinates i Q B
    ((differentiableAt_complex_column hv').const_smul Complex.I)

/-- The actual null and transport columns give the precise cancellation
premise of the complete residual, on their existing chart. These inputs are
the phase differential and the first/third conclusions of
`exists_pencil_leading_amplitude`; no cancellation is assumed.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem column_cancellation
    (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ)
    (s : ℝ) (η : Euclidean d) (x : E)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (x 0, (s, (spatialPart x, η))))
      (x 0, (s, (spatialPart x, η))))
    (hclock : (twoTimeState Φ (C.symm (x 0, (s, (spatialPart x, η))))).1 = x 0)
    (hy : (twoTimeState Φ (C.symm (x 0, (s, (spatialPart x, η))))).2.1 = spatialPart x)
    (hu : ∀ j, DifferentiableAt ℝ (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (x 0, (s, (spatialPart x, η))))
    (hv : ∀ j, DifferentiableAt ℝ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (x 0, (s, (spatialPart x, η))))
    (hnull : ∀ j, rootPencil (coordinateSplit i) Q h
      (twoTimeState Φ (C.symm (x 0, (s, (spatialPart x, η))))) *ᵥ
        pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j
          (x 0, (s, (spatialPart x, η))) = 0)
    (hcorr : ∀ j, rootPencil (coordinateSplit i) Q h
      (twoTimeState Φ (C.symm (x 0, (s, (spatialPart x, η))))) *ᵥ
        pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j
          (x 0, (s, (spatialPart x, η))) =
      adaptedPencilApply (coordinateSplit i) Q B
        (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j)
          (x 0, (s, (spatialPart x, η)))) (j : Fin (d + 1)) :
    WKB.firstOrderApply (fun y a ↦ ((coefficient i Q y a).map Complex.ofReal).mulVecLin)
      (fun y ↦ ((zeroth i B y).map Complex.ofReal).mulVecLin)
      (fun y ↦ Complex.exp (Complex.I * (phase C (y 0) s (spatialPart y) η : ℂ)) •
        (fun k ↦ (leading i Q B h Φ C r c σ + correction i Q B h Φ C r c σ)
          (y 0) s (spatialPart y) η k j)) x =
      Complex.exp (Complex.I * (phase C (x 0) s (spatialPart x) η : ℂ)) •
        (fun k ↦ twoTimePhysicalApply (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
          (fun y ↦ (zeroth i B y).map Complex.ofReal) (correction i Q B h Φ C r c σ)
          (x 0) s (spatialPart x) η k j) := by
  let sl := physicalSlice (coordinateSplit i) s η
  have hs : DifferentiableAt ℝ sl (physicalCoordinates i x) :=
    (contDiff_physicalSlice (coordinateSplit i) s η).differentiable (by simp) _
  have hu' := ((physicalSlice_physicalCoordinates i s η x).symm ▸ hu j).comp _ hs
  have hv' := ((physicalSlice_physicalCoordinates i s η x).symm ▸ hv j).comp _ hs
  have hp := ((physicalSlice_physicalCoordinates i s η x).symm ▸ hphase.differentiableAt).comp _ hs
  have hk : DifferentiableAt ℝ
      (pencilTwoTermKernelColumn (coordinateSplit i) Q B h Φ C r c σ j s η)
      (physicalCoordinates i x) :=
    (((differentiableAt_const Complex.I).mul (Complex.ofRealCLM.differentiableAt.comp _ hp)).cexp).smul
      ((differentiableAt_complex_column hu').add
        ((differentiableAt_complex_column hv').const_smul Complex.I))
  have he : (fun y ↦ Complex.exp (Complex.I * (phase C (y 0) s (spatialPart y) η : ℂ)) •
      (fun k ↦ (leading i Q B h Φ C r c σ + correction i Q B h Φ C r c σ)
        (y 0) s (spatialPart y) η k j)) =
      pencilTwoTermKernelColumn (coordinateSplit i) Q B h Φ C r c σ j s η ∘
        physicalCoordinates i := by
    funext y k
    simp [phase, leading, correction, pencilTwoTermKernelColumn, mul_add]
  rw [he]
  refine (firstOrderApply_physicalCoordinates i Q B hk).trans ?_
  have hid := firstOrder_pencilTwoTermKernelColumn i Q B h Φ C r c σ j
    hphase hclock hy (hu j) (hv j) (hnull j) (hcorr j)
  refine hid.trans ?_
  exact congrArg (Complex.exp (Complex.I * (phase C (x 0) s (spatialPart x) η : ℂ)) • ·)
    (correction_apply_column i Q B h Φ C r c σ s η x hv j).symm

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
