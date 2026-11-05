module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Parameter

/-!
# Product tests for the carrier Fourier factorization

The product tests and their representatives below are consumed by the full
Fourier factorization for `app:ch_background:prop:bg-adjoint` and
`app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace
namespace JanetCartan.CarrierSobolev
open ContinuumRow
namespace Factorization

variable {n : ℕ}

/-- Scalar parameter data times a transverse L² class, used as dense product
tests for `app:ch_background:prop:bg-adjoint`. -/
def tensorBilin (n : ℕ) : TransverseL2 n →L[ℂ]
    Lp ℂ 2 (volume : Measure ParameterSpace) →L[ℂ]
      Lp (TransverseL2 n) 2 (volume : Measure ParameterSpace) :=
  (ContinuousLinearMap.lsmul ℂ ℂ).flip.compLpL₂ 2 volume

/-- Evaluation of the product test, for the Fourier factorization in
`app:ch_background:prop:bg-adjoint`. -/
def tensor (n : ℕ) (c : TransverseL2 n)
    (g : Lp ℂ 2 (volume : Measure ParameterSpace)) :
    Lp (TransverseL2 n) 2 (volume : Measure ParameterSpace) :=
  (ContinuousLinearMap.toSpanSingleton ℂ c).compLp g

/-- The representative of the product test (`app:ch_background:prop:bg-adjoint`). -/
theorem tensor_coeFn (c : TransverseL2 n)
    (g : Lp ℂ 2 (volume : Measure ParameterSpace)) :
    tensor n c g =ᵐ[volume] fun z => g z • c :=
  (ContinuousLinearMap.toSpanSingleton ℂ c).coeFn_compLp g

/-- Place the product test in the literal carrier space
(`app:ch_background:prop:bg-adjoint`). -/
def carrierTensorBilin (n : ℕ) : TransverseL2 n →L[ℂ]
    Lp ℂ 2 (volume : Measure ParameterSpace) →L[ℂ] CarrierL2 n :=
  (ContinuousLinearMap.compL ℂ _ _ _
    ((carrierFubiniEquiv n).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (parameterL2Equiv n).symm.toContinuousLinearEquiv.toContinuousLinearMap)).comp (tensorBilin n)

/-- Evaluation of a carrier product test (`app:ch_background:prop:bg-adjoint`). -/
def carrierTensor (n : ℕ) (c : TransverseL2 n)
    (g : Lp ℂ 2 (volume : Measure ParameterSpace)) : CarrierL2 n :=
  (carrierFubiniEquiv n).symm ((parameterL2Equiv n).symm (tensor n c g))

/-- The product test on the original product measure has its expected nested
representative (`app:ch_background:prop:bg-adjoint`). -/
theorem carrierTensor_coeFn (c : TransverseL2 n)
    (g : Lp ℂ 2 (volume : Measure ParameterSpace)) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (fun y => carrierTensor n c g (z, y)) =ᵐ[volume]
        fun y => g (WithLp.toLp 2 z) * c y := by
  have ht := parameterToLp_measurePreserving.quasiMeasurePreserving.ae (tensor_coeFn c g)
  filter_upwards [carrierFubiniEquiv_symm_coeFn n
      ((parameterL2Equiv n).symm (tensor n c g)),
    parameterL2Equiv_symm_coeFn (tensor n c g), ht] with z hz hp ht
  change (fun y => carrierTensor n c g (z, y)) =ᵐ[volume] _ at hz
  rw [hp, ht] at hz
  exact hz.trans (Lp.coeFn_smul (g (WithLp.toLp 2 z)) c)

/-- Euclidean representative of a carrier product test. This is the input to
the product Fourier integral calculation (`app:ch_background:prop:bg-adjoint`). -/
theorem initialL2Equiv_carrierTensor_coeFn (c : TransverseL2 n)
    (g : Lp ℂ 2 (volume : Measure ParameterSpace)) :
    initialL2Equiv n (carrierTensor n c g) =ᵐ[volume]
      fun x : InitialSpace n => g x.fst * c x.snd := by
  have hp : (carrierTensor n c g : CarrierVariable n → ℂ) =ᵐ[carrierMeasure n]
      fun p => g (WithLp.toLp 2 p.1) * c p.2 := by
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr (carrierTensor_coeFn c g)
    exact measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable
      (((Lp.stronglyMeasurable g).measurable.comp
        ((MeasurableEquiv.toLp 2 CarrierParameter).measurable.comp measurable_fst)).mul
          ((Lp.stronglyMeasurable c).measurable.comp measurable_snd))
  exact (initialL2Equiv_coeFn n _).trans
    ((initialCoordinates_symm_measurePreserving n).quasiMeasurePreserving.ae hp)

end Factorization
end JanetCartan.CarrierSobolev
