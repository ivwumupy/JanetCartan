module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.Basic
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.ComplexPhysical

/-!
# The physical residual of the conic correction

Both source time and initial covector are fixed during physical differentiation.
The radial weight is therefore constant. This proves that the continued local
residual is literally `P W₁`, with the same zeroth-order matrix `B`.
Consumer: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ConicAmplitude
open AmplitudeBounds

variable {n d : ℕ}

/-- Radial normalization commutes with the literal fixed-source physical
slice (`app:ch_regular_base:eq:two-term-null-identity`). -/
theorem normalize_physicalSlice (ℓ : Euclidean d →L[ℝ] ℝ)
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (s : ℝ) (η : Euclidean d) (x : Euclidean n) :
    ConicPhase.normalize ℓ (physicalSlice e s η x) =
      physicalSlice e s ((ℓ η)⁻¹ • η) x := rfl

/-- Physical differentiation commutes with the actual order `-o`
continuation on a fixed source slice. The full operator, including `B`, is
retained (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem firstOrderApply_extend_slice (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (f : TwoTimePoint (Euclidean d) → Fin n → ℂ)
    (s : ℝ) (η : Euclidean d) (x : Euclidean n)
    (hf : DifferentiableAt ℝ (f ∘ physicalSlice e s ((ℓ η)⁻¹ • η)) x) :
    WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
      (extend ℓ o f ∘ physicalSlice e s η) x =
      (ℓ η)⁻¹ ^ o • WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
        (f ∘ physicalSlice e s ((ℓ η)⁻¹ • η)) x := by
  have he : extend ℓ o f ∘ physicalSlice e s η =
      fun y ↦ (((ℓ η)⁻¹ ^ o : ℝ) : ℂ) • (f ∘ physicalSlice e s ((ℓ η)⁻¹ • η)) y := by
    funext y a
    simp only [Function.comp_apply, extend, physicalSlice, ConicPhase.normalize,
      Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [he, firstOrderApply_smul _ _ (differentiableAt_const _) hf]
  simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply, zero_smul,
    Finset.sum_const_zero, zero_add]
  ext a
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]

/-- The conically continued correction residual is exactly the physical
operator applied to the conically continued correction matrix, columnwise.
The local identity is instantiated from `ComplexPhysical`, for the SAME
coefficients, chart, minor and source mask
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem pencilCorrectionResidual_extend_column_eq_physicalApply
    (ℓ : Euclidean d →L[ℝ] ℝ) (i : Fin (d + 1))
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (B : Euclidean (d + 1) → MetricTensor (d + 1))
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ) (j : Fin (d + 1))
    (q : TwoTimePoint (Euclidean d))
    (hu : DifferentiableAt ℝ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (ConicPhase.normalize ℓ q)) :
    (fun a ↦ extend ℓ 1 (pencilCorrectionResidualComplexMatrix (coordinateSplit i)
      Q B h Φ C r c σ) q a j) =
      WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
        (fun y a ↦ extend ℓ 1 (pencilCorrectionComplexMatrix (coordinateSplit i)
          Q B h Φ C r c σ) (physicalSlice (coordinateSplit i) q.2.1 q.2.2.2 y) a j)
        ((coordinateSplit i).symm (q.1, q.2.2.1)) := by
  let e := coordinateSplit i
  let p := ConicPhase.normalize ℓ q
  let x := e.symm (q.1, q.2.2.1)
  let sl := physicalSlice e q.2.1 ((ℓ q.2.2.2)⁻¹ • q.2.2.2)
  let u := pencilCorrectionColumn e Q B h Φ C r c σ j
  let f := fun z a ↦ pencilCorrectionComplexMatrix e Q B h Φ C r c σ z a j
  have hsl : sl x = p := physicalSlice_at e p
  have hd : DifferentiableAt ℝ (u ∘ sl) x := by
    apply DifferentiableAt.comp x _ ((contDiff_physicalSlice e _ _).differentiable (by simp) x)
    change DifferentiableAt ℝ u (sl x)
    rw [hsl]
    exact hu
  have hc : DifferentiableAt ℝ (f ∘ sl) x := by
    change DifferentiableAt ℝ (fun z ↦ Complex.I • (fun a ↦ ((u ∘ sl) z a : ℂ))) x
    have hdc : DifferentiableAt ℝ (fun z a ↦ ((u ∘ sl) z a : ℂ)) x :=
      differentiableAt_pi.mpr fun a ↦ Complex.ofRealCLM.differentiableAt.comp x
        (differentiableAt_pi.mp hd a)
    exact hdc.const_smul Complex.I
  have hp := pencilCorrectionResidualComplexMatrix_column_eq_physicalApply
    i Q B h Φ C r c σ j p hu
  have he := firstOrderApply_extend_slice ℓ 1 e Q B f q.2.1 q.2.2.2 x hc
  change (ℓ q.2.2.2)⁻¹ ^ 1 •
      (fun a ↦ pencilCorrectionResidualComplexMatrix e Q B h Φ C r c σ p a j) = _
  rw [hp]
  exact he.symm

end JanetCartan.RegularSector.Characteristic.ConicAmplitude
