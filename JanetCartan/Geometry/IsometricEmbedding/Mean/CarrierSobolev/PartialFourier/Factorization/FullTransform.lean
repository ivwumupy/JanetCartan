module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Factorization.Integral

/-!
# Full Fourier transformation of carrier product tests

The integral product calculation identifies the actual initial L² Fourier
transform on integrable product tests. Density in each factor removes both
integrability assumptions, for `app:ch_background:prop:bg-adjoint`.
-/

set_option maxHeartbeats 1000000

@[expose] public noncomputable section
open MeasureTheory FourierTransform
namespace JanetCartan.CarrierSobolev
open ContinuumRow
namespace Factorization
variable {n : ℕ}

private theorem initialFourier_carrierTensor_of_integrable (c : TransverseL2 n)
    (g : Lp ℂ 2 (volume : Measure ParameterSpace))
    (hc : Integrable (c : Euclidean (n - 1) → ℂ))
    (hg : Integrable (g : ParameterSpace → ℂ)) :
    initialFourier n (carrierTensor n c g) = carrierTensor n (𝓕 c) (𝓕 g) := by
  let e : (ParameterSpace × Euclidean (n - 1)) ≃ᵐ InitialSpace n :=
    MeasurableEquiv.toLp 2 _
  have he : MeasurePreserving e (volume.prod volume) volume :=
    WithLp.volume_preserving_toLp _ _
  have hi : Integrable (fun x : InitialSpace n => g x.fst * c x.snd) := by
    apply (he.integrable_comp _).mp
    · exact hg.mul_prod hc
    · exact (((Lp.stronglyMeasurable g).measurable.comp
        (measurable_fst.comp (WithLp.measurable_ofLp 2 _))).mul
        ((Lp.stronglyMeasurable c).measurable.comp
          (measurable_snd.comp (WithLp.measurable_ofLp 2 _)))).aestronglyMeasurable
  have hrep := initialL2Equiv_carrierTensor_coeFn c g
  have hF := Localization.fourierTransform_coeFn_ae_integral_hilbert
    (initialL2Equiv n (carrierTensor n c g)) (hi.congr hrep.symm)
  have hgF := Localization.fourierTransform_coeFn_ae_integral_hilbert g hg
  have hcF := Localization.fourierTransform_coeFn_ae_integral_hilbert c hc
  have hp : (fun p : ParameterSpace × Euclidean (n - 1) =>
      (𝓕 g) p.1 * (𝓕 c) p.2) =ᵐ[volume.prod volume]
        fun p => 𝓕 (g : ParameterSpace → ℂ) p.1 * 𝓕 (c : Euclidean (n - 1) → ℂ) p.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgF,
      Measure.quasiMeasurePreserving_snd.ae hcF] with p h₁ h₂
    exact congrArg₂ (· * ·) h₁ h₂
  have hp' := he.symm.quasiMeasurePreserving.ae hp
  apply (initialL2Equiv n).injective
  change initialL2Equiv n ((initialL2Equiv n).symm
    (𝓕 (initialL2Equiv n (carrierTensor n c g)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [hF, initialL2Equiv_carrierTensor_coeFn (𝓕 c) (𝓕 g), hp']
    with ξ h₁ h₂ h₃
  exact h₁.trans ((Real.fourier_congr_ae hrep ξ).trans
    ((fourierIntegral_product (g : ParameterSpace → ℂ) (c : Euclidean (n - 1) → ℂ) ξ).trans
      (h₃.symm.trans h₂.symm)))

/-- The actual full initial Fourier equivalence transforms both factors of
every carrier product test. No representative-action assumption is used
(`app:ch_background:prop:bg-adjoint`). -/
theorem initialFourier_carrierTensor (c : TransverseL2 n)
    (g : Lp ℂ 2 (volume : Measure ParameterSpace)) :
    initialFourier n (carrierTensor n c g) = carrierTensor n (𝓕 c) (𝓕 g) := by
  have h : ∀ c : TransverseL2 n, Integrable (c : Euclidean (n - 1) → ℂ) →
      ∀ g : Lp ℂ 2 (volume : Measure ParameterSpace),
      initialFourier n (carrierTensor n c g) = carrierTensor n (𝓕 c) (𝓕 g) := by
    intro c hc g
    apply DenseRange.induction_on
      (p := fun g : Lp ℂ 2 (volume : Measure ParameterSpace) =>
        initialFourier n (carrierTensor n c g) = carrierTensor n (𝓕 c) (𝓕 g))
      (SchwartzMap.denseRange_toLpCLM (E := ParameterSpace) (F := ℂ)
        (p := 2) ENNReal.ofNat_ne_top) g
    · exact isClosed_eq ((initialFourier n).continuous.comp (carrierTensorBilin n c).continuous)
        ((carrierTensorBilin n (𝓕 c)).continuous.comp continuous_fourier)
    intro s
    exact initialFourier_carrierTensor_of_integrable c _ hc
      (s.integrable.congr (s.coeFn_toLp 2).symm)
  apply DenseRange.induction_on
    (p := fun c : TransverseL2 n =>
      initialFourier n (carrierTensor n c g) = carrierTensor n (𝓕 c) (𝓕 g))
    (SchwartzMap.denseRange_toLpCLM (E := Euclidean (n - 1)) (F := ℂ)
      (p := 2) ENNReal.ofNat_ne_top) c
  · exact isClosed_eq ((initialFourier n).continuous.comp ((carrierTensorBilin n).flip g).continuous)
      (((carrierTensorBilin n).flip (𝓕 g)).continuous.comp continuous_fourier)
  intro s
  exact h _ (s.integrable.congr (s.coeFn_toLp 2).symm) g

end Factorization
end JanetCartan.CarrierSobolev
