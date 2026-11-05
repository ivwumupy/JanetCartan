module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.PhysicalAction
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhysicalKernel

/-!
# The same two-term cancellation at every positive radial scale

The conic phase and both amplitudes use one fixed radial representative.
The pencil scales by the radial factor and the correction scales by its
inverse, so the original local cancellation remains exact. This is the
pointwise input for the supported residual connection, not an assertion of
an uncut operator identity. Source: `app:ch_regular_base:eq:two-term-null-identity`
and `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ConicAmplitude
open ActualCarriers AmplitudeBounds

variable {n d : ℕ}

/-- The actual two-term physical kernel from the fixed conic phase and the
literal continued local matrices. The factor `i` remains inside the correction
matrix (`app:ch_regular_base:eq:two-term-null-identity`). -/
def pencilKernelColumn (ℓ : Euclidean d →L[ℝ] ℝ)
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin n) (σ : RootState (Euclidean d) → ℝ) (j : Fin n)
    (s : ℝ) (η : Euclidean d) (x : Euclidean n) : Fin n → ℂ :=
  let q := physicalSlice e s η x
  Complex.exp (Complex.I * (ConicPhase.phase ℓ C q : ℂ)) •
    (fun a ↦ extend ℓ 0 (pencilLeadingComplexMatrix e Q B h Φ C r c σ) q a j +
      extend ℓ 1 (pencilCorrectionComplexMatrix e Q B h Φ C r c σ) q a j)

/-- The local null and correction identities from the SAME constructed
Hamilton chart imply the exact physical conic cancellation. Every radial
factor is computed; no extended null identity or extended residual equation
is assumed (`app:ch_regular_base:eq:two-term-null-identity`). -/
theorem firstOrder_pencilKernelColumn
    (ℓ : Euclidean d →L[ℝ] ℝ) (i : Fin (d + 1))
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (B : Euclidean (d + 1) → MetricTensor (d + 1))
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ) (j : Fin (d + 1))
    (q : TwoTimePoint (Euclidean d)) (hℓ : 0 < ℓ q.2.2.2)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (ConicPhase.normalize ℓ q)) (ConicPhase.normalize ℓ q))
    (hclock : (twoTimeState Φ (C.symm (ConicPhase.normalize ℓ q))).1 = q.1)
    (hy : (twoTimeState Φ (C.symm (ConicPhase.normalize ℓ q))).2.1 = q.2.2.1)
    (hu : DifferentiableAt ℝ (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (ConicPhase.normalize ℓ q))
    (hv : DifferentiableAt ℝ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (ConicPhase.normalize ℓ q))
    (hnull : rootPencil (coordinateSplit i) Q h (twoTimeState Φ (C.symm (ConicPhase.normalize ℓ q))) *ᵥ
      pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j (ConicPhase.normalize ℓ q) = 0)
    (hcorr : rootPencil (coordinateSplit i) Q h (twoTimeState Φ (C.symm (ConicPhase.normalize ℓ q))) *ᵥ
      pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j (ConicPhase.normalize ℓ q) =
      adaptedPencilApply (coordinateSplit i) Q B
        (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j) (ConicPhase.normalize ℓ q)) :
    WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
      (pencilKernelColumn ℓ (coordinateSplit i) Q B h Φ C r c σ j q.2.1 q.2.2.2)
      ((coordinateSplit i).symm (q.1, q.2.2.1)) =
      Complex.exp (Complex.I * (ConicPhase.phase ℓ C q : ℂ)) •
        (fun a ↦ extend ℓ 1 (pencilCorrectionResidualComplexMatrix (coordinateSplit i)
          Q B h Φ C r c σ) q a j) := by
  let e := coordinateSplit i
  let p := ConicPhase.normalize ℓ q
  let lam := ℓ q.2.2.2
  let x := e.symm (q.1, q.2.2.1)
  let sl := physicalSlice e p.2.1 p.2.2.2
  let u := pencilLeadingColumn e Q B h Φ C r c σ j
  let v := pencilCorrectionColumn e Q B h Φ C r c σ j
  let φ := twoTimePhase C ∘ sl
  let ξ := e.symm (h (twoTimeState Φ (C.symm p)), (twoTimeState Φ (C.symm p)).2.2)
  change DifferentiableAt ℝ u p at hu
  change DifferentiableAt ℝ v p at hv
  change HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C p) p at hphase
  change (twoTimeState Φ (C.symm p)).1 = q.1 at hclock
  change (twoTimeState Φ (C.symm p)).2.1 = q.2.2.1 at hy
  have hsl : sl x = p := physicalSlice_at e p
  have hsd : DifferentiableAt ℝ sl x := (contDiff_physicalSlice e _ _).differentiable (by simp) x
  have hud : DifferentiableAt ℝ (u ∘ sl) x := (hsl.symm ▸ hu).comp x hsd
  have hvd : DifferentiableAt ℝ (v ∘ sl) x := (hsl.symm ▸ hv).comp x hsd
  have hpd : DifferentiableAt ℝ φ x := (hsl.symm ▸ hphase.differentiableAt).comp x hsd
  have hξ (a : Fin (d + 1)) : partialDeriv φ x a = ξ a :=
    partialDeriv_twoTimePhase_physicalSlice i h Φ C hphase hclock hy a
  have hgrad (a : Fin (d + 1)) : partialDeriv (fun y ↦ lam * φ y) x a = (lam • ξ) a := by
    change fderiv ℝ (fun y ↦ lam * φ y) x _ = _
    rw [(hpd.hasFDerivAt.const_mul lam).fderiv]
    change lam * partialDeriv φ x a = lam * ξ a
    rw [hξ]
  have hs : pencil (Q x) ξ = rootPencil e Q h (twoTimeState Φ (C.symm p)) := by
    simp only [rootPencil, x, ξ, hclock, hy]
  have hscale : pencil (Q x) (lam • ξ) = lam • pencil (Q x) ξ :=
    (pencilContinuousLinearMap (Q x)).map_smul lam ξ
  have hn : pencil (Q x) (lam • ξ) *ᵥ (u ∘ sl) x = 0 := by
    rw [hscale, smul_mulVec]
    simp only [Function.comp_apply, hsl, hs, u, e, p, hnull, smul_zero]
  have hc : pencil (Q x) (lam • ξ) *ᵥ (lam⁻¹ • (v ∘ sl) x) =
      physicalPencilApply Q B (u ∘ sl) x := by
    rw [hscale, smul_mulVec, mulVec_smul, smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]
    have happly : physicalPencilApply Q B (u ∘ sl) x = adaptedPencilApply e Q B u p :=
      physicalPencilApply_slice i Q B hu
    rw [happly]
    simpa only [Function.comp_apply, hsl, hs, u, v, e, p] using hcorr
  have hid := firstOrder_twoTerm_real_columns Q B
    (v := fun y ↦ lam⁻¹ • (v ∘ sl) y) (hpd.const_mul lam) hud
    (hvd.const_smul lam⁻¹) (lam • ξ) hgrad hn hc
  have he : pencilKernelColumn ℓ e Q B h Φ C r c σ j q.2.1 q.2.2.2 =
      fun y ↦ Complex.exp (Complex.I * ((lam * φ y : ℝ) : ℂ)) •
        ((fun a ↦ ((u ∘ sl) y a : ℂ)) +
          Complex.I • (fun a ↦ ((lam⁻¹ • (v ∘ sl) y) a : ℂ))) := by
    funext y a
    simp only [pencilKernelColumn, ConicPhase.phase, ConicPhase.extend, extend,
      physicalSlice, ConicPhase.normalize, pow_zero, one_smul, pow_one,
      pencilLeadingComplexMatrix, pencilCorrectionComplexMatrix, complexColumnMatrix,
      Pi.smul_apply, Matrix.smul_apply, Pi.add_apply, Complex.real_smul, smul_eq_mul,
      Complex.ofReal_mul, Function.comp_apply, φ, u, v, sl, p, lam]
    ring
  have hvext : (fun y ↦ Complex.I • (fun a ↦ ((lam⁻¹ • (v ∘ sl) y) a : ℂ))) =
      fun y a ↦ extend ℓ 1 (pencilCorrectionComplexMatrix e Q B h Φ C r c σ)
        (physicalSlice e q.2.1 q.2.2.2 y) a j := by
    funext y a
    simp only [extend, physicalSlice, ConicPhase.normalize, pow_one,
      pencilCorrectionComplexMatrix, complexColumnMatrix, Pi.smul_apply, Matrix.smul_apply,
      Complex.real_smul, smul_eq_mul, Complex.ofReal_mul, Function.comp_apply, v, sl, p, lam]
    ring
  rw [← he, hvext] at hid
  rw [← pencilCorrectionResidual_extend_column_eq_physicalApply ℓ i Q B h Φ C r c σ j q hv] at hid
  simpa only [φ, Function.comp_apply, hsl, ConicPhase.phase, ConicPhase.extend, lam, p] using hid

end JanetCartan.RegularSector.Characteristic.ConicAmplitude
