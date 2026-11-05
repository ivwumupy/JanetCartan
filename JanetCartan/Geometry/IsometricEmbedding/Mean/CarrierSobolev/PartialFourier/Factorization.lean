module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Factorization.Density
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Factorization.FullTransform
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Factorization.TensorOperators

/-!
# Full Fourier factorization on carrier L²

The actual full initial Fourier transform equals transverse Fourier followed
by parameter Fourier under the actual Fubini equivalence. This provides the
full Fourier compatibility required for transverse frequency-weight control
in `app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`.
-/

set_option maxHeartbeats 1000000

@[expose] public noncomputable section
open MeasureTheory FourierTransform
namespace JanetCartan.CarrierSobolev
open ContinuumRow

/-- Full carrier Fourier factorization into the constructed transverse and
parameter transforms. It holds for every L² datum and every transverse
dimension, including zero (`app:ch_background:prop:bg-adjoint` and
`app:ch_background:prop:bg-inverse`). -/
theorem carrierFubiniEquiv_initialFourier (n : ℕ) (f : CarrierL2 n) :
    carrierFubiniEquiv n (initialFourier n f) =
      iteratedParameterFourier n (iteratedTransverseFourier n (carrierFubiniEquiv n f)) := by
  let L : CarrierL2 n →L[ℂ] IteratedCarrierL2 n :=
    (carrierFubiniEquiv n).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (initialFourier n).toContinuousLinearEquiv.toContinuousLinearMap
  let M : CarrierL2 n →L[ℂ] IteratedCarrierL2 n :=
    (iteratedParameterFourier n).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((iteratedTransverseFourier n).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (carrierFubiniEquiv n).toContinuousLinearEquiv.toContinuousLinearMap)
  apply Factorization.ext_of_carrierTensor L M _ f
  intro c g
  change carrierFubiniEquiv n (initialFourier n (Factorization.carrierTensor n c g)) = _
  exact (congrArg (carrierFubiniEquiv n) (Factorization.initialFourier_carrierTensor c g)).trans
    (Factorization.iteratedFourier_carrierTensor c g).symm

end JanetCartan.CarrierSobolev
