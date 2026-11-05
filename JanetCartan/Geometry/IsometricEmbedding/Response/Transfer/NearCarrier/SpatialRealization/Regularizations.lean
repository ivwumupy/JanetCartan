module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.SpatialRealization.Amplitudes

/-!
# Spatial regularization inputs from compact smooth data

Construct the analytic interfaces used by `ForwardDerivative` and
`ReverseDerivative`, rather than postulating them. Compactness and smoothness
supply every domination, integrability, and pairing field. The only geometric
inputs are the actual phase derivative and inverse identities from
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.SpatialRealization
open FourierIntegral
variable {n r : ℕ}

private theorem smooth_partialDeriv {u : Euclidean n → Fin r → ℂ}
    (hu : ContDiff ℝ ∞ u) (j : Fin n) : ContDiff ℝ ∞ (fun y ↦ partialDeriv u y j) :=
  (hu.fderiv_right (by simp)).clm_apply contDiff_const

/-- All analytic fields of the forward transfer follow from compact smooth
full amplitudes and the primitive identity `dₓ Φ = Bδ`.
Source: `app:ch_response:eq:direct-envelope-profile`.
The supplied `A` includes every selector, cutoff and physical weight. -/
theorem forwardTransferRegularization_of_compact
    {X Y F : Set (Euclidean n)} (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {Φ : Euclidean n → Euclidean n → ℝ}
    (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ))
    {A : FullAmplitude n r} (hA : ForwardAmplitudeAdmissible X Y F A)
    {B : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ}
    (j : Fin n)
    (hB : ∀ l, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 j l))
    {u : Euclidean n → Fin r → ℂ} (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (hgrad : ∀ x δ, partialDeriv (fun z ↦ Φ z δ) x j = ∑ l, B x δ j l * δ l) :
    ForwardTransferRegularization Φ A B u j := by
  have hΩ := smooth_graphOscillation hΦ
  have hR := admissible_forwardRemainderAmplitude hA hX.isClosed hY.isClosed j hB
  have hD (l) := admissible_forwardDatumAmplitude hA j l (hB l)
  refine {
    phase_differentiable := fun δ ↦ (hΦ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
    amplitude_smooth := fun δ ↦ hA.smooth.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
    datum_smooth := hu
    datum_compact := hus
    phase_identity := hgrad
    domination := ⟨?_, ?_, ?_⟩
    remainder_integrable := ?_
    datum_integrable := ?_
    base_pairing_integrable := ?_
    remainder_pairing_integrable := ?_
    datum_pairing_integrable := ?_ }
  · exact integrable_amplitudeKernel hΩ hA hY hF hu
  · exact integrable_amplitudeKernel_fderiv hΩ hA hY hF hu
  · exact locally_dominated_amplitudeKernel_fderiv hΩ hA hY hF hu
  · intro x
    exact (integrable_amplitudeKernel hΩ hR hY hF hu x).integral_prod_left
  · intro x l
    exact (integrable_amplitudeKernel hΩ (hD l) hY hF (smooth_partialDeriv hu l) x).integral_prod_left
  · exact integrable_amplitudeIntegral_pairing hΩ hA hX hY hF hu _
  · exact integrable_amplitudeIntegral_pairing hΩ hR hX hY hF hu _
  · intro φ l
    exact integrable_amplitudeIntegral_pairing hΩ (hD l) hX hY hF (smooth_partialDeriv hu l) _ φ

/-- All analytic fields of the reverse transfer follow from compact smooth
full amplitudes, the actual inverse identity, and `dₓ ΔS = Bδ`.
The remainder differentiates the entire inverse-weighted amplitude, retaining
both `C` and `j_S U⁻¹` derivatives. No regularization record is an assumption.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem reverseTransferRegularization_of_compact
    {X Y F : Set (Euclidean n)} (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {S : Euclidean n → Euclidean n → ℝ} {ζ : Euclidean n} {ρ : ℝ}
    (hΦ : ContDiff ℝ ∞ (Function.uncurry (phaseIncrement S ζ ρ)))
    {A : FullAmplitude n r} (hA : ForwardAmplitudeAdmissible X Y F A)
    {B C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ}
    (j : Fin n)
    (hC : ∀ l, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ C p.1 p.2 j l))
    {u : Euclidean n → Fin r → ℂ} (hu : ContDiff ℝ ∞ u)
    (hinv : ∀ y δ, ∀ x ∈ tsupport (fun z ↦ A y z δ), C x δ * B x δ = 1)
    (hgrad : ∀ y δ, ∀ x ∈ tsupport (fun z ↦ A y z δ), ∀ l,
      partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l =
        (B x δ).mulVec (fun k ↦ δ k) l) :
    ReverseDerivative.TransferRegularization S ζ ρ A B C u j := by
  have hΩ := smooth_reverseOscillation hΦ
  have hR := admissible_reverseRemainderAmplitude hA hX.isClosed hY.isClosed j hC
  have hD (l) := admissible_reverseDatumAmplitude hA j l (hC l)
  refine {
    phase_smooth := fun δ ↦ hΦ.comp (contDiff_id.prodMk contDiff_const)
    inverse_smooth := fun δ l ↦ (hC l).comp (contDiff_id.prodMk contDiff_const)
    amplitude_smooth := fun δ ↦ hA.smooth.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
    amplitude_compact := compactSupport_amplitude_source hA hY
    datum_smooth := hu
    inverse_identity := hinv
    phase_identity := hgrad
    domination := ⟨?_, ?_, ?_⟩
    output_amplitude_integrable := ?_
    remainder_integrable := ?_
    datum_integrable := ?_
    base_pairing_integrable := ?_
    remainder_pairing_integrable := ?_
    datum_pairing_integrable := ?_ }
  · exact integrable_amplitudeKernel hΩ hA hY hF hu
  · exact integrable_amplitudeKernel_fderiv hΩ hA hY hF hu
  · exact locally_dominated_amplitudeKernel_fderiv hΩ hA hY hF hu
  · intro y δ
    have hx := hA.outputPartial hX.isClosed j
    have hc : Continuous (fun x ↦ ReverseDerivative.oscillation S ζ ρ y x δ •
        (partialDeriv (fun z ↦ A z x δ) y j).mulVec (u x)) :=
      (smooth_amplitudeKernel hΩ hx hu).continuous.comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    apply hc.integrable_of_hasCompactSupport
    apply hY.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hY.isClosed
    intro x hx'
    by_contra hn
    exact hx' (by simp [hx.support y x δ (Or.inr (Or.inl hn))])
  · intro y
    exact (integrable_amplitudeKernel hΩ hR hY hF hu y).integral_prod_left
  · intro y l
    exact (integrable_amplitudeKernel hΩ (hD l) hY hF (smooth_partialDeriv hu l) y).integral_prod_left
  · exact integrable_amplitudeIntegral_pairing hΩ hA hX hY hF hu _
  · exact integrable_amplitudeIntegral_pairing hΩ hR hX hY hF hu _
  · intro φ l
    exact integrable_amplitudeIntegral_pairing hΩ (hD l) hX hY hF (smooth_partialDeriv hu l) _ φ

end JanetCartan.ResponseTransfer.SpatialRealization
