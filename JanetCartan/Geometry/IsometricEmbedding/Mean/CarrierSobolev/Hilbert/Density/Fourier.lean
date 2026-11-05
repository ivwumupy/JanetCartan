module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Hilbert.Density.Coordinates

/-!
# Fourier transport for compact smooth physical density

The full L² Fourier transform commutes with orthonormal finite coordinates.
This supplies the actual transport needed for compact smooth approximation in
`app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace JanetCartan.CarrierSobolev
open ContinuumRow

private theorem densityEuclideanL2Equiv_schwartz (n : ℕ)
    (f : 𝓢(InitialSpace n, ℂ)) :
    densityEuclideanL2Equiv n (f.toLp 2 volume) =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (densityEuclideanEquiv n).symm.toContinuousLinearEquiv f).toLp 2 volume := by
  apply Lp.ext
  refine (Lp.coeFn_compMeasurePreserving _ _).trans ?_
  exact ((densityEuclideanEquiv n).symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (f.coeFn_toLp 2 volume)).trans
      (SchwartzMap.coeFn_toLp
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (densityEuclideanEquiv n).symm.toContinuousLinearEquiv f) 2 volume).symm

set_option maxHeartbeats 800000 in
/-- Orthogonal change of variables commutes with the full L² Fourier transform;
the extension from Schwartz functions uses density, as required for arbitrary
physical classes in `app:ch_background:prop:bg-adjoint`. -/
theorem densityEuclideanL2Equiv_fourier (n : ℕ)
    (f : Lp ℂ 2 (volume : Measure (InitialSpace n))) :
    densityEuclideanL2Equiv n (𝓕 f) = 𝓕 (densityEuclideanL2Equiv n f) := by
  let p := fun f : Lp ℂ 2 (volume : Measure (InitialSpace n)) ↦
    densityEuclideanL2Equiv n (𝓕 f) = 𝓕 (densityEuclideanL2Equiv n f)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (E := InitialSpace n) (F := ℂ)
      (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      ((densityEuclideanL2Equiv n).continuous.comp (continuous_fourier))
      (continuous_fourier.comp (densityEuclideanL2Equiv n).continuous)
  intro g
  change densityEuclideanL2Equiv n (𝓕 (g.toLp 2 volume)) =
    𝓕 (densityEuclideanL2Equiv n (g.toLp 2 volume))
  rw [SchwartzMap.toLp_fourier_eq, densityEuclideanL2Equiv_schwartz,
    densityEuclideanL2Equiv_schwartz, SchwartzMap.toLp_fourier_eq]
  congr 1
  ext x
  exact (Real.fourier_comp_linearIsometry (densityEuclideanEquiv n).symm g x).symm

/-- The physical full Fourier transform becomes the usual Euclidean L² Fourier
transform in finite coordinates (`app:ch_background:prop:bg-adjoint`). -/
theorem densityL2Equiv_initialFourier (n : ℕ) (f : CarrierL2 n) :
    densityL2Equiv n (initialFourier n f) = 𝓕 (densityL2Equiv n f) := by
  change densityEuclideanL2Equiv n
    (initialL2Equiv n ((initialL2Equiv n).symm
      (𝓕 (initialL2Equiv n f)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact densityEuclideanL2Equiv_fourier n _

/-- Representative form of Fourier transport on the physical domain, used to
compare weighted norms in `app:ch_background:prop:bg-adjoint`. -/
theorem initialFourier_coeFn_densityCoordinates (n : ℕ) (f : CarrierL2 n) :
    initialFourier n f =ᵐ[carrierMeasure n]
      (𝓕 (densityL2Equiv n f) : Lp ℂ 2 (volume : Measure (DensityEuclidean n))) ∘
        densityCoordinates n := by
  rw [← densityL2Equiv_initialFourier]
  simpa only [LinearIsometryEquiv.symm_apply_apply] using
    densityL2Equiv_symm_coeFn n (densityL2Equiv n (initialFourier n f))

end JanetCartan.CarrierSobolev
