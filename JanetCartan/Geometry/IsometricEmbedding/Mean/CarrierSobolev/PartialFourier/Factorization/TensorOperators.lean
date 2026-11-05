module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Factorization.Tensors

/-!
# The iterated Fourier operators on product tests

For `app:ch_background:prop:bg-adjoint`, the actual parameter and transverse
Fourier operators transform the respective factors of every L² product test.
The full initial Fourier operator is compared to them separately.
-/

set_option maxHeartbeats 1000000

@[expose] public noncomputable section
open MeasureTheory FourierTransform
namespace JanetCartan.CarrierSobolev
open ContinuumRow
namespace Factorization
variable {n : ℕ}

/-- Bounded transverse maps act on the transverse factor of a product test
(`app:ch_background:prop:bg-adjoint`). -/
theorem compLp_tensor (L : TransverseL2 n →L[ℂ] TransverseL2 n)
    (c : TransverseL2 n) (g : Lp ℂ 2 (volume : Measure ParameterSpace)) :
    L.compLp (tensor n c g) = tensor n (L c) g := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (tensor n c g), tensor_coeFn c g,
    tensor_coeFn (L c) g] with z hL hc hLc
  exact hL.trans ((congrArg L hc).trans ((L.map_smul (g z) c).trans hLc.symm))

private theorem fourier_tensor_of_integrable (c : TransverseL2 n)
    (g : Lp ℂ 2 (volume : Measure ParameterSpace)) (hg : Integrable (g : ParameterSpace → ℂ)) :
    𝓕 (tensor n c g) = tensor n c (𝓕 g) := by
  let L : ℂ →L[ℂ] TransverseL2 n := (ContinuousLinearMap.lsmul ℂ ℂ).flip c
  have hL : Integrable (tensor n c g : ParameterSpace → TransverseL2 n) :=
    (L.integrable_comp hg).congr (tensor_coeFn c g).symm
  apply Lp.ext
  filter_upwards [Localization.fourierTransform_coeFn_ae_integral_hilbert _ hL,
    tensor_coeFn c (𝓕 g), Localization.fourierTransform_coeFn_ae_integral_hilbert g hg]
    with ξ h₁ h₂ h₃
  rw [h₁, Real.fourier_congr_ae (tensor_coeFn c g) ξ, h₂, h₃]
  change 𝓕 (fun z => L (g z)) ξ = L (𝓕 (g : ParameterSpace → ℂ) ξ)
  simp only [Real.fourier_eq, Circle.smul_def, ← L.map_smul]
  exact L.integral_comp_comm ((Real.fourierIntegral_convergent_iff ξ).mpr hg)

/-- Parameter Fourier transformation acts on the scalar parameter factor of
an arbitrary L² product test (`app:ch_background:prop:bg-adjoint`). -/
theorem fourier_tensor (c : TransverseL2 n)
    (g : Lp ℂ 2 (volume : Measure ParameterSpace)) :
    𝓕 (tensor n c g) = tensor n c (𝓕 g) := by
  apply DenseRange.induction_on
    (p := fun g : Lp ℂ 2 (volume : Measure ParameterSpace) =>
      𝓕 (tensor n c g) = tensor n c (𝓕 g))
    (SchwartzMap.denseRange_toLpCLM (E := ParameterSpace) (F := ℂ)
      (p := 2) ENNReal.ofNat_ne_top) g
  · exact isClosed_eq (continuous_fourier.comp (tensorBilin n c).continuous)
      ((tensorBilin n c).continuous.comp continuous_fourier)
  intro s
  exact fourier_tensor_of_integrable c _ (s.integrable.congr (s.coeFn_toLp 2).symm)

/-- Both iterated Fourier factors have the expected action on product tests,
without assuming the full Fourier factorization
(`app:ch_background:prop:bg-adjoint`). -/
theorem iteratedFourier_carrierTensor (c : TransverseL2 n)
    (g : Lp ℂ 2 (volume : Measure ParameterSpace)) :
    iteratedParameterFourier n (iteratedTransverseFourier n
      (carrierFubiniEquiv n (carrierTensor n c g))) =
        carrierFubiniEquiv n (carrierTensor n (𝓕 c) (𝓕 g)) := by
  let L := (Lp.fourierTransformₗᵢ (Euclidean (n - 1)) ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  have h : parameterL2Equiv n (iteratedTransverseFourier n
      (carrierFubiniEquiv n (carrierTensor n c g))) = tensor n (𝓕 c) g := by
    change parameterL2Equiv n (L.compLp (carrierFubiniEquiv n
      ((carrierFubiniEquiv n).symm ((parameterL2Equiv n).symm (tensor n c g))))) = _
    rw [LinearIsometryEquiv.apply_symm_apply, parameterL2Equiv_compLp,
      LinearIsometryEquiv.apply_symm_apply]
    exact compLp_tensor L c g
  change (parameterL2Equiv n).symm (𝓕 (parameterL2Equiv n
    (iteratedTransverseFourier n (carrierFubiniEquiv n (carrierTensor n c g))))) = _
  rw [h, fourier_tensor]
  exact ((carrierFubiniEquiv n).apply_symm_apply
    ((parameterL2Equiv n).symm (tensor n (𝓕 c) (𝓕 g)))).symm

end Factorization
end JanetCartan.CarrierSobolev
