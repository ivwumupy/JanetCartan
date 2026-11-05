module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PhysicalDerivatives.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.FullCompatibility

/-!
# Carrier weak derivatives commute with partial radian synthesis

For `app:ch_background:prop:bg-adjoint`, the actual partial inverse Fourier
map preserves weak differentiation in all three outer carrier coordinates.
Full Fourier factorization changes a carrier derivative into multiplication
by an outer frequency. Fubini and complex linearity transport that multiplier
through inverse transverse Fourier and the exact radian dilation. All L²
classes use the literal carrier measure, including when `n - 1 = 0`.

The consumer is `hasCarrierL2CoordinateDerivative_partialInverse_carrier`;
its smooth input weak derivative is supplied separately by `WeakInput`.
-/

set_option maxHeartbeats 1000000

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow CarrierSobolev Pseudodifferential
variable {n : ℕ}

/-- Recover the distributional derivative from its Fourier representative. Used by
`carrier_derivative_of_fourier_ae` for `app:ch_background:prop:bg-adjoint`. -/
private theorem derivative_of_fourier_ae {d : ℕ} (i : Fin d)
    (f g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (h : 𝓕 g =ᵐ[volume] fun ξ => euclideanCoordinateDerivativeSymbol i ξ * 𝓕 f ξ) :
    HasEuclideanL2CoordinateDerivative i f g := by
  have he : 𝓕 (euclideanCoordinateDerivative i f) =
      𝓕 (g : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
    rw [fourier_euclideanCoordinateDerivative, Lp.fourier_toTemperedDistribution_eq]
    ext φ
    simp only [TemperedDistribution.smulLeftCLM_apply_apply,
      Lp.toTemperedDistribution_apply,
      SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_euclideanCoordinateDerivativeSymbol i)]
    apply integral_congr_ae
    filter_upwards [h] with ξ hξ
    simp only [hξ, smul_eq_mul]
    ring
  have := congrArg (fun T : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ) => 𝓕⁻ T) he
  change euclideanCoordinateDerivative i f = _
  simpa only [fourierInv_fourier_eq] using this

/-- Pull the Fourier representative back through the exact ordered coordinates,
for the final commutation theorem in `app:ch_background:prop:bg-adjoint`. -/
private theorem carrier_derivative_of_fourier_ae (i : Fin (3 + (n - 1)))
    (f g : CarrierL2 n)
    (h : initialFourier n g =ᵐ[carrierMeasure n] fun ξ =>
      (2 * Real.pi * Complex.I) * (flatInitialCoordinates n ξ i : ℂ) *
        initialFourier n f ξ) : HasCarrierL2CoordinateDerivative i f g := by
  apply derivative_of_fourier_ae
  have he := (flatInitialCoordinates_symm_measurePreserving n).quasiMeasurePreserving.ae h
  have hf := flatInitialL2Equiv_coeFn n (initialFourier n f)
  have hg := flatInitialL2Equiv_coeFn n (initialFourier n g)
  rw [flatInitialL2Equiv_initialFourier] at hf hg
  filter_upwards [he, hf, hg] with ξ hξ hfξ hgξ
  rw [hgξ, hfξ]
  simpa only [Function.comp_apply, MeasurableEquiv.apply_symm_apply,
    euclideanCoordinateDerivativeSymbol] using hξ

/-- The outer frequency symbol in `app:ch_background:prop:bg-adjoint`. -/
private def outerSymbol (i : Fin 3) (z : CarrierParameter) : ℂ :=
  (2 * Real.pi * Complex.I) * (Fin.cases z.1 (fun j => z.2 j) i : ℝ)

/-- Measurability needed by `outer_smul_of_fubini` when reassembling the product
a.e. identity for `app:ch_background:prop:bg-adjoint`. -/
private theorem measurable_outerSymbol (i : Fin 3) : Measurable (outerSymbol i) := by
  refine Fin.cases ?_ (fun j => ?_) i <;>
    unfold outerSymbol <;> simp only [Fin.cases_zero, Fin.cases_succ] <;> fun_prop

/-- The carrier derivative symbol is independent of transverse frequency, as
used in the commutation proof for `app:ch_background:prop:bg-adjoint`. -/
private theorem outerSymbol_eq (i : Fin 3) (p : CarrierVariable n) :
    (2 * Real.pi * Complex.I) * (flatInitialCoordinates n p (Fin.castAdd (n - 1) i) : ℂ) =
      outerSymbol i p.1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change (2 * Real.pi * Complex.I) *
      (flatInitialEquiv n (initialCoordinates n p) (Fin.castAdd (n - 1) (Fin.castAdd 2 0)) : ℂ) = _
    rw [flatInitialEquiv_scalar]
    rfl
  · have hj : j.succ = Fin.natAdd 1 j := by ext; simp; omega
    rw [hj]
    change (2 * Real.pi * Complex.I) *
      (flatInitialEquiv n (initialCoordinates n p) (Fin.castAdd (n - 1) (Fin.natAdd 1 j)) : ℂ) = _
    rw [flatInitialEquiv_vector, ← hj]
    rfl

/-- Convert an existing product L² multiplier identity into a fiber identity.
No boundedness of the outer multiplier is needed: both L² representatives
are already given (`app:ch_background:prop:bg-adjoint`). -/
private theorem fubini_outer_smul (m : CarrierParameter → ℂ) (f g : CarrierL2 n)
    (h : g =ᵐ[carrierMeasure n] fun p => m p.1 * f p) :
    carrierFubiniEquiv n g =ᵐ[volume.prod volume]
      fun z => m z • carrierFubiniEquiv n f z := by
  filter_upwards [Measure.ae_ae_of_ae_prod h, carrierFubiniEquiv_coeFn n f,
    carrierFubiniEquiv_coeFn n g] with z hz hf hg
  apply Lp.ext
  filter_upwards [hz, hf, hg, Lp.coeFn_smul (m z) (carrierFubiniEquiv n f z)]
    with η hη hfη hgη hsη
  simpa only [hsη, Pi.smul_apply, smul_eq_mul, hfη, hgη] using hη

/-- Reassemble the fiber multiplier identity on the literal carrier measure;
used by the final commutation proof for `app:ch_background:prop:bg-adjoint`. -/
private theorem outer_smul_of_fubini (m : CarrierParameter → ℂ) (hm : Measurable m)
    (f g : CarrierL2 n)
    (h : carrierFubiniEquiv n g =ᵐ[volume.prod volume]
      fun z => m z • carrierFubiniEquiv n f z) :
    g =ᵐ[carrierMeasure n] fun p => m p.1 * f p := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (Lp.stronglyMeasurable g).measurable
    ((hm.comp measurable_fst).mul (Lp.stronglyMeasurable f).measurable))).mpr
  filter_upwards [h, carrierFubiniEquiv_coeFn n f, carrierFubiniEquiv_coeFn n g]
    with z hz hf hg
  have hs := Lp.coeFn_smul (m z) (carrierFubiniEquiv n f z)
  rw [← hz] at hs
  filter_upwards [hs, hf, hg] with η hsη hfη hgη
  change g (z, η) = m z * f (z, η)
  simpa only [Pi.smul_apply, smul_eq_mul, hfη, hgη] using hsη

/-- Complex linearity commutes an outer multiplier with each inverse transverse
operator. The final commutation proof uses this for transverse Fourier and
radian dilation (`app:ch_background:prop:bg-adjoint`). -/
private theorem transverseEquiv_symm_outer_smul
    (U : TransverseL2 n ≃ₗᵢ[ℂ] TransverseL2 n) (m : CarrierParameter → ℂ)
    (f g : IteratedCarrierL2 n)
    (h : g =ᵐ[volume.prod volume] fun z => m z • f z) :
    (iteratedTransverseEquiv U).symm g =ᵐ[volume.prod volume]
      fun z => m z • (iteratedTransverseEquiv U).symm f z := by
  filter_upwards [h, iteratedTransverseEquiv_symm_coeFn U f,
    iteratedTransverseEquiv_symm_coeFn U g] with z hz hf hg
  simp only [hg, hf, hz, map_smul]

/-- Partial radian inverse Fourier transformation preserves each of the three
carrier weak derivatives before physical cutoffs, as required by
`app:ch_background:prop:bg-adjoint`. The consumer is
`hasCarrierL2CoordinateDerivative_partialInverse_carrier`. -/
theorem hasCarrierL2CoordinateDerivative_partialUnitaryInverse_of_carrierDerivative
    (i : Fin 3) (f g : CarrierL2 n)
    (h : HasCarrierL2CoordinateDerivative (Fin.castAdd (n - 1) i) f g) :
    HasCarrierL2CoordinateDerivative (Fin.castAdd (n - 1) i)
      (partialUnitaryInverse n f) (partialUnitaryInverse n g) := by
  have hF : initialFourier n g =ᵐ[carrierMeasure n]
      fun p => outerSymbol i p.1 * initialFourier n f p := by
    filter_upwards [h.initialFourier_ae_eq] with p hp
    simpa only [outerSymbol_eq] using hp
  have hI := fubini_outer_smul (outerSymbol i) (initialFourier n f) (initialFourier n g) hF
  simp only [carrierFubiniEquiv_initialFourier] at hI
  have hcomm (v : CarrierL2 n) :
      iteratedParameterFourier n (iteratedTransverseFourier n (carrierFubiniEquiv n v)) =
        iteratedTransverseFourier n (iteratedParameterFourier n (carrierFubiniEquiv n v)) :=
    iteratedParameterFourier_transverseEquiv
      (Lp.fourierTransformₗᵢ (Euclidean (n - 1)) ℂ) (carrierFubiniEquiv n v)
  simp only [hcomm] at hI
  have hP := transverseEquiv_symm_outer_smul
    (Lp.fourierTransformₗᵢ (Euclidean (n - 1)) ℂ) (outerSymbol i) _ _ hI
  change (iteratedTransverseFourier n).symm
    (iteratedTransverseFourier n (iteratedParameterFourier n (carrierFubiniEquiv n g)))
      =ᵐ[volume.prod volume] fun z => outerSymbol i z •
        (iteratedTransverseFourier n).symm
          (iteratedTransverseFourier n (iteratedParameterFourier n (carrierFubiniEquiv n f))) z at hP
  simp only [LinearIsometryEquiv.symm_apply_apply] at hP
  have hD := transverseEquiv_symm_outer_smul (transverseDilation n ℂ) (outerSymbol i) _ _ hP
  change (iteratedTransverseDilation n).symm
    (iteratedParameterFourier n (carrierFubiniEquiv n g)) =ᵐ[volume.prod volume]
      fun z => outerSymbol i z • (iteratedTransverseDilation n).symm
        (iteratedParameterFourier n (carrierFubiniEquiv n f)) z at hD
  have hout (v : CarrierL2 n) :
      carrierFubiniEquiv n (initialFourier n (partialUnitaryInverse n v)) =
        (iteratedTransverseDilation n).symm
          (iteratedParameterFourier n (carrierFubiniEquiv n v)) :=
    (carrierFubiniEquiv_initialFourier_partialUnitaryInverse v).trans
      (iteratedParameterFourier_dilation_symm _)
  simp only [← hout g, ← hout f] at hD
  have hfinal := outer_smul_of_fubini (outerSymbol i) (measurable_outerSymbol i)
    (initialFourier n (partialUnitaryInverse n f))
    (initialFourier n (partialUnitaryInverse n g)) hD
  apply carrier_derivative_of_fourier_ae
  filter_upwards [hfinal] with p hp
  simpa only [outerSymbol_eq] using hp

end JanetCartan.ContinuumAdjoint.DerivativeKernels
