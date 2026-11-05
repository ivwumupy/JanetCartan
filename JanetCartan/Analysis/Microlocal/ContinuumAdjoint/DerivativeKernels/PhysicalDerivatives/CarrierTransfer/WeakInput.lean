module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PhysicalDerivatives.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Hilbert.Density.Coordinates
/-!
# The weak carrier derivatives of the smooth Fourier-side input

For `app:ch_background:prop:bg-adjoint`, joint smoothness and the two primitive
L² bounds give the distributional derivative in each of the three carrier
coordinates. Hölder's inequality supplies every integrability condition for
integration by parts against arbitrary Schwartz tests; no compact support or
extra decay of the input is required.

The consumer is `hasCarrierL2CoordinateDerivative_partialInverse_carrier`.
This leaf supplies its input weak derivative. Preservation of that identity by
`partialUnitaryInverse` is a separate obligation of the carrier transfer.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap ContDiff LineDeriv
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow CarrierSobolev
variable {n : ℕ}

private def carrierTransferCoordinates (n : ℕ) :
    CarrierVariable n ≃L[ℝ] EuclideanSpace ℝ (Fin (3 + (n - 1))) :=
  (initialCoordinatesLinear n).trans (flatInitialEquiv n).toContinuousLinearEquiv

private theorem fderiv_carrier_applyInitialCarrierDerivative {f : CarrierVariable n → ℂ}
    (hf : ContDiff ℝ ∞ f) (h : CarrierParameter) (p : CarrierVariable n) :
    fderiv ℝ f p (h, 0) = applyInitialCarrierDerivative (.carrier h) f p := by
  have hp : HasFDerivAt (fun z : CarrierParameter ↦ (z, p.2))
      ((ContinuousLinearMap.id ℝ CarrierParameter).prod 0) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have hd := ((hf.differentiable (by simp) p).hasFDerivAt.comp p.1 hp).fderiv
  change _ = fderiv ℝ (fun z ↦ f (z, p.2)) p.1 h
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply] using (congrArg (fun L ↦ L h) hd).symm

private theorem fderiv_flat_carrier_applyInitialCarrierDerivative {f : CarrierVariable n → ℂ}
    (hf : ContDiff ℝ ∞ f) (i : Fin 3)
    (x : EuclideanSpace ℝ (Fin (3 + (n - 1)))) :
    fderiv ℝ (f ∘ (carrierTransferCoordinates n).symm) x
      (EuclideanSpace.basisFun (Fin (3 + (n - 1))) ℝ (Fin.castAdd (n - 1) i)) =
      applyInitialCarrierDerivative (.carrier (physicalCarrierDirection i)) f
        ((flatInitialCoordinates n).symm x) := by
  rw [(carrierTransferCoordinates n).symm.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  have he : (carrierTransferCoordinates n).symm
      (EuclideanSpace.basisFun (Fin (3 + (n - 1))) ℝ (Fin.castAdd (n - 1) i)) =
      (physicalCarrierDirection i, 0) := by
    apply (carrierTransferCoordinates n).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (flatInitialCoordinates_physicalCarrierDirection i).symm
  rw [he]
  exact fderiv_carrier_applyInitialCarrierDerivative hf _ _

/-- Jointly smooth carrier data with the indicated L² derivative has that
actual distributional derivative in the full ordered initial coordinates.
This supplies the primitive input to
`hasCarrierL2CoordinateDerivative_partialInverse_carrier`, for the scalar and
both vector carrier coordinates in `app:ch_background:prop:bg-adjoint`.
The measure remains the literal `(ds dv) dη`. -/
theorem hasCarrierL2CoordinateDerivative_toLp_carrier
    (i : Fin 3) {f : CarrierVariable n → ℂ} (hreg : ContDiff ℝ ∞ f)
    (h0 : MemLp f 2 (carrierMeasure n))
    (h1 : MemLp (applyInitialCarrierDerivative (.carrier (physicalCarrierDirection i)) f)
      2 (carrierMeasure n)) :
    HasCarrierL2CoordinateDerivative (Fin.castAdd (n - 1) i) (h0.toLp f)
      (h1.toLp (applyInitialCarrierDerivative (.carrier (physicalCarrierDirection i)) f)) := by
  let e := carrierTransferCoordinates n
  let F := f ∘ e.symm
  let G := applyInitialCarrierDerivative (.carrier (physicalCarrierDirection i)) f ∘ e.symm
  let v := EuclideanSpace.basisFun (Fin (3 + (n - 1))) ℝ (Fin.castAdd (n - 1) i)
  have hF : ContDiff ℝ ∞ F := hreg.comp e.symm.contDiff
  have hF2 : MemLp F 2 volume :=
    h0.comp_measurePreserving (flatInitialCoordinates_symm_measurePreserving n)
  have hG2 : MemLp G 2 volume :=
    h1.comp_measurePreserving (flatInitialCoordinates_symm_measurePreserving n)
  have hd (x) : fderiv ℝ F x v = G x := fderiv_flat_carrier_applyInitialCarrierDerivative hreg i x
  have he0 : flatInitialL2Equiv n (h0.toLp f) =ᵐ[volume] F :=
    (flatInitialL2Equiv_coeFn n _).trans
      ((flatInitialCoordinates_symm_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
        h0.coeFn_toLp)
  have he1 : flatInitialL2Equiv n (h1.toLp _) =ᵐ[volume] G :=
    (flatInitialL2Equiv_coeFn n _).trans
      ((flatInitialCoordinates_symm_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
        h1.coeFn_toLp)
  apply (hasCarrierL2CoordinateDerivative_iff_test _ _ _).mpr
  intro φ
  have hφ2 := φ.memLp 2
  have hdφ2 := (∂_{v} φ).memLp 2
  have hD2 : MemLp (fun x ↦ fderiv ℝ F x v) 2 volume := by
    simpa only [hd] using hG2
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := φ) (g := F) (v := v)
    (hdφ2.integrable_mul hF2) (hφ2.integrable_mul hD2)
    (hφ2.integrable_mul hF2)
    (fun x _ ↦ φ.differentiableAt) (fun x _ ↦ hF.differentiable (by simp) x)
  simp only [hd] at hibp
  calc
    _ = ∫ x, φ x * G x := by
      apply integral_congr_ae
      filter_upwards [he1] with x hx
      simp only [smul_eq_mul, hx]
    _ = -(∫ x, (∂_{v} φ) x * F x) := hibp
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [he0] with x hx
      simp only [smul_eq_mul, hx, v]

end JanetCartan.ContinuumAdjoint.DerivativeKernels
