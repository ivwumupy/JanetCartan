module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative.Regularized
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Weak derivative of the actual reverse regularization

The source trade from `app:ch_regular_base:eq:actual-adjoint-trade` and primitive
integral domination give the reverse weak derivative in
`app:ch_response:eq:direct-envelope-profile`. The hypotheses below are inputs of
`jc-finite-fio-calculus` and `jc-compatible-phase-geometry`, to be instantiated by
`jc-response-near-carrier`. They do not assume an operator derivative identity.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.ReverseDerivative
variable {n r : ℕ}

/-- Analytic and geometric inputs for one regularization in
`app:ch_response:eq:direct-envelope-profile`. The matrix `C` is the supplied
inverse of `B`; its source derivatives are retained in the remainder. Compact
source support belongs to the amplitude, so the datum need not be compactly
supported. Domination concerns the literal kernel, never its integral. -/
structure TransferRegularization (S : Euclidean n → Euclidean n → ℝ)
    (ζ : Euclidean n) (ρ : ℝ) (A : FourierIntegral.FullAmplitude n r)
    (B C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (f : Euclidean n → Fin r → ℂ) (j : Fin n) : Prop where
  phase_smooth : ∀ δ, ContDiff ℝ ∞ (fun x ↦ phaseIncrement S ζ ρ x δ)
  inverse_smooth : ∀ δ l, ContDiff ℝ ∞ (fun x ↦ C x δ j l)
  amplitude_smooth : ∀ δ, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 δ)
  amplitude_compact : ∀ y δ, HasCompactSupport (fun x ↦ A y x δ)
  datum_smooth : ContDiff ℝ ∞ f
  inverse_identity : ∀ y δ, ∀ x ∈ tsupport (fun z ↦ A y z δ), C x δ * B x δ = 1
  phase_identity : ∀ y δ, ∀ x ∈ tsupport (fun z ↦ A y z δ), ∀ l,
    partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l =
      (B x δ).mulVec (fun k ↦ δ k) l
  domination : KernelDomination S ζ ρ A f
  output_amplitude_integrable : ∀ y δ, Integrable (fun x ↦ oscillation S ζ ρ y x δ •
    (partialDeriv (fun z ↦ A z x δ) y j).mulVec (f x))
  remainder_integrable : ∀ y, Integrable (fun δ ↦ ∫ x, oscillation S ζ ρ y x δ •
    (remainderAmplitude C A j y x δ).mulVec (f x))
  datum_integrable : ∀ y l, Integrable (fun δ ↦ ∫ x, oscillation S ζ ρ y x δ •
    (datumAmplitude C A j l y x δ).mulVec (partialDeriv f x l))
  base_pairing_integrable : ∀ φ : 𝓢(Euclidean n, ℂ),
    Integrable (fun y ↦ φ y • envelopeGraph S ζ ρ A f y)
  remainder_pairing_integrable : ∀ φ : 𝓢(Euclidean n, ℂ),
    Integrable (fun y ↦ φ y • envelopeGraph S ζ ρ (remainderAmplitude C A j) f y)
  datum_pairing_integrable : ∀ (φ : 𝓢(Euclidean n, ℂ)) l,
    Integrable (fun y ↦ φ y • envelopeGraph S ζ ρ (datumAmplitude C A j l)
      (fun x ↦ partialDeriv f x l) y)

/-- Actual regularized output differentiation in
`app:ch_response:eq:direct-envelope-profile`: datum amplitudes `Cⱼₗ A` and full
remainder `∂yⱼ A + Σₗ ∂xₗ(Cⱼₗ A)`. In particular, the derivative of the inverse
matrix is present. -/
theorem TransferRegularization.partialDeriv_envelopeGraph
    {S : Euclidean n → Euclidean n → ℝ} {ζ : Euclidean n} {ρ : ℝ}
    {A : FourierIntegral.FullAmplitude n r}
    {B C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ}
    {f : Euclidean n → Fin r → ℂ} {j : Fin n}
    (h : TransferRegularization S ζ ρ A B C f j) (y : Euclidean n) :
    partialDeriv (envelopeGraph S ζ ρ A f) y j =
      envelopeGraph S ζ ρ (remainderAmplitude C A j) f y +
      ∑ l, envelopeGraph S ζ ρ (datumAmplitude C A j l) (fun x ↦ partialDeriv f x l) y := by
  have hAy (x δ : Euclidean n) : Differentiable ℝ (fun z ↦ A z x δ) :=
    ((h.amplitude_smooth δ).comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
  rw [partialDeriv_envelopeGraph_of_domination S ζ ρ A f hAy h.domination y j]
  simp_rw [integral_output_derivative_transfer S ζ ρ y _ j B C A f
    (h.phase_smooth _) (h.inverse_smooth _)
    ((h.amplitude_smooth _).comp (contDiff_const.prodMk contDiff_id))
    (fun x ↦ hAy x _ y) (h.amplitude_compact y _) h.datum_smooth
    (h.inverse_identity y _) (h.phase_identity y _) (h.output_amplitude_integrable y _)]
  rw [integral_add (integrable_finsetSum _ (fun l _ ↦ h.datum_integrable y l))
    (h.remainder_integrable y), integral_finsetSum _ (fun l _ ↦ h.datum_integrable y l)]
  simp only [smul_add, Finset.smul_sum, envelopeGraph]
  exact add_comm _ _

/-- Weak derivative identity for the literal reverse regularization, derived by
output integration by parts after the source trade. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem TransferRegularization.weak_derivative
    {S : Euclidean n → Euclidean n → ℝ} {ζ : Euclidean n} {ρ : ℝ}
    {A : FourierIntegral.FullAmplitude n r}
    {B C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ}
    {f : Euclidean n → Fin r → ℂ} {j : Fin n}
    (h : TransferRegularization S ζ ρ A B C f j) (φ : 𝓢(Euclidean n, ℂ)) :
    (∫ y, partialDeriv φ y j • envelopeGraph S ζ ρ A f y) =
      -((∫ y, φ y • envelopeGraph S ζ ρ (remainderAmplitude C A j) f y) +
        ∑ l, ∫ y, φ y • envelopeGraph S ζ ρ (datumAmplitude C A j l)
          (fun x ↦ partialDeriv f x l) y) := by
  have hid : Integrable (fun y ↦ φ y • partialDeriv (envelopeGraph S ζ ρ A f) y j) := by
    simp_rw [h.partialDeriv_envelopeGraph, smul_add, Finset.smul_sum]
    exact (h.remainder_pairing_integrable φ).add
      (integrable_finsetSum _ (fun l _ ↦ h.datum_pairing_integrable φ l))
  have hit : Integrable (fun y ↦ partialDeriv φ y j • envelopeGraph S ζ ρ A f y) := by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, partialDeriv] using
      h.base_pairing_integrable (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) φ)
  have hh := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    hit hid (h.base_pairing_integrable φ) (fun y _ ↦ φ.differentiable y)
    (fun y _ ↦ (hasFDerivAt_envelopeGraph_of_domination S ζ ρ A f
      (fun x δ ↦ ((h.amplitude_smooth δ).comp (contDiff_id.prodMk contDiff_const)).differentiable
        (by simp)) h.domination y).differentiableAt)
  change (∫ y, φ y • partialDeriv (envelopeGraph S ζ ρ A f) y j) =
    -(∫ y, partialDeriv φ y j • envelopeGraph S ζ ρ A f y) at hh
  simp_rw [h.partialDeriv_envelopeGraph, smul_add, Finset.smul_sum] at hh
  rw [integral_add (h.remainder_pairing_integrable φ)
    (integrable_finsetSum _ (fun l _ ↦ h.datum_pairing_integrable φ l)),
    integral_finsetSum _ (fun l _ ↦ h.datum_pairing_integrable φ l)] at hh
  exact (neg_eq_iff_eq_neg.mpr hh).symm

end JanetCartan.ResponseTransfer.ReverseDerivative
