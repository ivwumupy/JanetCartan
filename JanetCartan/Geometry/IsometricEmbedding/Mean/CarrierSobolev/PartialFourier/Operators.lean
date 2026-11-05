module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Realization

/-!
# Partial and parameter Fourier operators on the carrier product

For `app:ch_background:prop:bg-adjoint`, this leaf supplies the actual
fiberwise Fourier and dilation operators and the Hilbert-valued Fourier
transform in all three carrier parameters. The full Fourier factorization
uses these constructions; it is a theorem to prove, not part of their inputs.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
namespace JanetCartan.CarrierSobolev
open ContinuumRow
variable {n : ℕ}

/-- Lift a transverse L² equivalence to the outer carrier L² space. This
single construction supplies the Fourier and dilation factors needed for
`app:ch_background:prop:bg-adjoint`. -/
def iteratedTransverseEquiv (U : TransverseL2 n ≃ₗᵢ[ℂ] TransverseL2 n) :
    IteratedCarrierL2 n ≃ₗᵢ[ℂ] IteratedCarrierL2 n where
  __ := U.toContinuousLinearEquiv.toContinuousLinearMap.compLpₗ 2 (volume.prod volume)
  invFun := U.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp
  left_inv f := by
    apply Lp.ext
    let A := U.toContinuousLinearEquiv.toContinuousLinearMap
    let B := U.symm.toContinuousLinearEquiv.toContinuousLinearMap
    change B.compLp (A.compLp f) =ᵐ[volume.prod volume] f
    filter_upwards [B.coeFn_compLp (A.compLp f), A.coeFn_compLp f] with z hz hz'
    rw [hz, hz']
    exact U.symm_apply_apply _
  right_inv f := by
    apply Lp.ext
    let A := U.toContinuousLinearEquiv.toContinuousLinearMap
    let B := U.symm.toContinuousLinearEquiv.toContinuousLinearMap
    change A.compLp (B.compLp f) =ᵐ[volume.prod volume] f
    filter_upwards [A.coeFn_compLp (B.compLp f), B.coeFn_compLp f] with z hz hz'
    rw [hz, hz']
    exact U.apply_symm_apply _
  norm_map' f := by
    let A := U.toContinuousLinearEquiv.toContinuousLinearMap
    change ‖A.compLp f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.memLp _).aestronglyMeasurable
      (Lp.memLp _).aestronglyMeasurable
    filter_upwards [A.coeFn_compLp f] with z hz
    rw [hz]
    exact U.norm_map _

/-- Representative formula for the lifted transverse operator
(`app:ch_background:prop:bg-adjoint`). -/
theorem iteratedTransverseEquiv_coeFn (U : TransverseL2 n ≃ₗᵢ[ℂ] TransverseL2 n)
    (f : IteratedCarrierL2 n) :
    iteratedTransverseEquiv U f =ᵐ[volume.prod volume] fun z => U (f z) :=
  U.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f

/-- Representative formula for the inverse lifted transverse operator
(`app:ch_background:prop:bg-inverse`). -/
theorem iteratedTransverseEquiv_symm_coeFn (U : TransverseL2 n ≃ₗᵢ[ℂ] TransverseL2 n)
    (f : IteratedCarrierL2 n) :
    (iteratedTransverseEquiv U).symm f =ᵐ[volume.prod volume] fun z => U.symm (f z) :=
  U.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp f

/-- Unit-period Fourier transformation in the transverse variable, leaving
all carrier parameters fixed (`app:ch_background:prop:bg-adjoint`). -/
def iteratedTransverseFourier (n : ℕ) :
    IteratedCarrierL2 n ≃ₗᵢ[ℂ] IteratedCarrierL2 n :=
  iteratedTransverseEquiv (Lp.fourierTransformₗᵢ (Euclidean (n - 1)) ℂ)

/-- The radian normalization dilation in each transverse fiber
(`app:ch_background:prop:bg-adjoint`). -/
def iteratedTransverseDilation (n : ℕ) :
    IteratedCarrierL2 n ≃ₗᵢ[ℂ] IteratedCarrierL2 n :=
  iteratedTransverseEquiv (transverseDilation n ℂ)

/-- The lifted Fourier transform acts on the actual transverse L² class
at almost every parameter (`app:ch_background:prop:bg-adjoint`). -/
theorem iteratedTransverseFourier_coeFn (f : IteratedCarrierL2 n) :
    iteratedTransverseFourier n f =ᵐ[volume.prod volume] fun z => 𝓕 (f z) :=
  iteratedTransverseEquiv_coeFn _ _

/-- Transverse Fourier compatibility on every iterated L² class, including
nonintegrable data (`app:ch_background:prop:bg-adjoint`). -/
theorem iteratedTransverseFourier_unitaryInverse (f : IteratedCarrierL2 n) :
    iteratedTransverseFourier n (iteratedUnitaryInverse n f) =
      (iteratedTransverseDilation n).symm f := by
  apply Lp.ext
  filter_upwards [iteratedTransverseFourier_coeFn (iteratedUnitaryInverse n f),
    iteratedUnitaryInverse_coeFn n f,
    iteratedTransverseEquiv_symm_coeFn (transverseDilation n ℂ) f] with z h₁ h₂ h₃
  change (iteratedTransverseDilation n).symm f z =
    (transverseDilation n ℂ).symm (f z) at h₃
  exact h₁.trans ((congrArg (fun g : TransverseL2 n => 𝓕 g) h₂).trans
    ((fourier_transverseUnitaryInverse (n := n) (f z)).trans h₃.symm))

/-- Carrier product-space partial Fourier equivalence in the physical
transverse variable (`app:ch_background:prop:bg-adjoint`). -/
def partialFourier (n : ℕ) : CarrierL2 n ≃ₗᵢ[ℂ] CarrierL2 n :=
  ((carrierFubiniEquiv n).trans (iteratedTransverseFourier n)).trans
    (carrierFubiniEquiv n).symm

/-- The exact transverse Fourier action of radian synthesis on arbitrary
carrier L² input (`app:ch_background:prop:bg-adjoint`). -/
theorem partialFourier_partialUnitaryInverse (f : CarrierL2 n) :
    partialFourier n (partialUnitaryInverse n f) =
      (carrierFubiniEquiv n).symm
        ((iteratedTransverseDilation n).symm (carrierFubiniEquiv n f)) := by
  change (carrierFubiniEquiv n).symm
    (iteratedTransverseFourier n (carrierFubiniEquiv n (partialUnitaryInverse n f))) = _
  exact congrArg (carrierFubiniEquiv n).symm
    ((congrArg (iteratedTransverseFourier n)
      (carrierFubiniEquiv_partialUnitaryInverse f)).trans
        (iteratedTransverseFourier_unitaryInverse (carrierFubiniEquiv n f)))

/-- Explicit frequency rescaling after partial radian synthesis, with the
exact amplitude and `2π` rescaling needed for transverse weight control
(`app:ch_background:prop:bg-adjoint`). -/
theorem partialFourier_partialUnitaryInverse_coeFn (f : CarrierL2 n) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (fun ξ => partialFourier n (partialUnitaryInverse n f) (z, ξ)) =ᵐ[volume]
        fun ξ => synthesisFactor n • f (z, (2 * Real.pi) • ξ) := by
  rw [partialFourier_partialUnitaryInverse (n := n) f]
  filter_upwards [carrierFubiniEquiv_symm_coeFn n
      ((iteratedTransverseDilation n).symm (carrierFubiniEquiv n f)),
    iteratedTransverseEquiv_symm_coeFn (transverseDilation n ℂ) (carrierFubiniEquiv n f),
    carrierFubiniEquiv_coeFn n f] with z hz hd hf
  change (iteratedTransverseDilation n).symm (carrierFubiniEquiv n f) z =
    (transverseDilation n ℂ).symm ((carrierFubiniEquiv n f) z) at hd
  have hz' := hz.trans (Filter.Eventually.of_forall fun ξ =>
    congrArg (fun g : TransverseL2 n => g ξ) hd)
  have he := (Measure.quasiMeasurePreserving_smul
    (volume : Measure (Euclidean (n - 1))) (by positivity : (2 * Real.pi : ℝ) ≠ 0)).ae hf
  refine hz'.trans ((transverseDilation_symm_coeFn _).trans ?_)
  filter_upwards [he] with ξ hξ
  rw [hξ]

/-- The literal parameter measure is Euclidean volume after the Hilbert
coordinate change (`app:ch_background:prop:bg-adjoint`). -/
theorem parameterToLp_measurePreserving :
    MeasurePreserving (MeasurableEquiv.toLp 2 CarrierParameter)
      (volume.prod volume) volume :=
  WithLp.volume_preserving_toLp ℝ (Euclidean 2)

/-- The inverse parameter-coordinate map preserves the literal Lebesgue
product measure (`app:ch_background:prop:bg-adjoint`). -/
theorem parameterOfLp_measurePreserving :
    MeasurePreserving (MeasurableEquiv.toLp 2 CarrierParameter).symm
      volume (volume.prod volume) :=
  parameterToLp_measurePreserving.symm

/-- L² coordinate change for all three carrier parameters with the transverse
L² space as Hilbert fiber (`app:ch_background:prop:bg-adjoint`). -/
def parameterL2Equiv (n : ℕ) :
    IteratedCarrierL2 n ≃ₗᵢ[ℂ] Lp (TransverseL2 n) 2 (volume : Measure ParameterSpace) where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (MeasurableEquiv.toLp 2 CarrierParameter).symm
    parameterOfLp_measurePreserving
  invFun := Lp.compMeasurePreserving (MeasurableEquiv.toLp 2 CarrierParameter)
    parameterToLp_measurePreserving
  left_inv f := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.symm_comp_self] using
      Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.self_comp_symm] using
      Lp.compMeasurePreserving_id_apply f

/-- Actual Hilbert-valued Fourier transform in `z = (s,v)`, for the full
initial-variable Fourier factorization in `app:ch_background:prop:bg-adjoint`.
It does not transform the transverse L² fiber. -/
def iteratedParameterFourier (n : ℕ) :
    IteratedCarrierL2 n ≃ₗᵢ[ℂ] IteratedCarrierL2 n :=
  ((parameterL2Equiv n).trans (Lp.fourierTransformₗᵢ ParameterSpace (TransverseL2 n))).trans
    (parameterL2Equiv n).symm

/-- Forward representative for the parameter-coordinate isometry used in
the full Fourier factorization (`app:ch_background:prop:bg-adjoint`). -/
theorem parameterL2Equiv_coeFn (f : IteratedCarrierL2 n) :
    parameterL2Equiv n f =ᵐ[volume]
      fun z => f ((MeasurableEquiv.toLp 2 CarrierParameter).symm z) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Inverse representative for the parameter-coordinate isometry
(`app:ch_background:prop:bg-adjoint`). -/
theorem parameterL2Equiv_symm_coeFn
    (f : Lp (TransverseL2 n) 2 (volume : Measure ParameterSpace)) :
    (parameterL2Equiv n).symm f =ᵐ[volume.prod volume]
      fun z => f (MeasurableEquiv.toLp 2 CarrierParameter z) :=
  Lp.coeFn_compMeasurePreserving _ _

end JanetCartan.CarrierSobolev
