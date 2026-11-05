module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.SpatialRealization.Regularizations
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Realization

/-!
# Actual spatial transfer on compact source tests

The forward and reverse identities of
`app:ch_response:eq:direct-envelope-profile` for full smooth compact amplitudes.
Every analytic premise of the integration-by-parts calculation is discharged.
The outputs use the shared Euclidean finite-fiber convention, not a different
norm on coordinate arrays. These identities feed the all-data L² extension.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.SpatialRealization
open FourierIntegral
variable {n r : ℕ}

/-- Actual forward spatial transfer on the shared compact test domain. The
remaining amplitude is `∂x A + Σ B ∂y A`, with all physical weights and selectors
inside `A`. Compactness supplies every analytic input.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem forwardGraph_compactTest_weak_pairing
    {X Y F : Set (Euclidean n)} (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {Φ : Euclidean n → Euclidean n → ℝ}
    (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ))
    {A : FullAmplitude n r} (hA : ForwardAmplitudeAdmissible X Y F A)
    {B : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ}
    (i : Fin n)
    (hB : ∀ j, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ B p.1 p.2 i j))
    (hgrad : ∀ x δ, partialDeriv (fun z ↦ Φ z δ) x i = ∑ j, B x δ i j * δ j)
    (u : graphTestSpace n r) (φ : 𝓢(Euclidean n, ℂ)) :
    (∫ x, partialDeriv φ x i • WithLp.toLp 2
      (graphOperator Φ A (fun y ↦ (u.val y).ofLp) x)) =
    -((∫ x, φ x • WithLp.toLp 2
        (graphOperator Φ (forwardRemainderAmplitude B A i) (fun y ↦ (u.val y).ofLp) x)) +
      ∑ j, ∫ x, φ x • WithLp.toLp 2
        (graphOperator Φ (forwardDatumAmplitude B A i j)
          (fun y ↦ ((graphTestPartialDeriv j u).val y).ofLp) x)) := by
  let L := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
  let Lr := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)
  have hu : ContDiff ℝ ∞ (fun y ↦ (u.val y).ofLp) := Lr.contDiff.comp u.property.1
  have hus : HasCompactSupport (fun y ↦ (u.val y).ofLp) :=
    u.property.2.comp_left Lr.map_zero
  have hw := (forwardTransferRegularization_of_compact hX hY hF hΦ hA i hB hu hus hgrad).weak_derivative φ
  have he := congrArg L.symm hw
  simp only [map_neg, map_add, map_sum] at he
  simp_rw [← L.symm.integral_comp_comm] at he
  simp only [map_smul] at he
  simpa only [L, PiLp.coe_symm_continuousLinearEquiv,
    graphTestPartialDeriv_coordinates] using he

/-- Actual reverse spatial transfer on the shared compact test domain. The
remaining amplitude is `∂y A + Σ ∂x(C A)`, including derivatives of the actual
inverse and of the full `j_S U⁻¹` weight when it is supplied as `A`.
No analytic regularization interface is assumed.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem reverseGraph_compactTest_weak_pairing
    {X Y F : Set (Euclidean n)} (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {S : Euclidean n → Euclidean n → ℝ} {ζ : Euclidean n} {ρ : ℝ}
    (hΦ : ContDiff ℝ ∞ (Function.uncurry (phaseIncrement S ζ ρ)))
    {A : FullAmplitude n r} (hA : ForwardAmplitudeAdmissible X Y F A)
    {B C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ}
    (i : Fin n)
    (hC : ∀ j, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ C p.1 p.2 i j))
    (hinv : ∀ y δ, ∀ x ∈ tsupport (fun z ↦ A y z δ), C x δ * B x δ = 1)
    (hgrad : ∀ y δ, ∀ x ∈ tsupport (fun z ↦ A y z δ), ∀ l,
      partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l =
        (B x δ).mulVec (fun k ↦ δ k) l)
    (u : graphTestSpace n r) (φ : 𝓢(Euclidean n, ℂ)) :
    (∫ y, partialDeriv φ y i • WithLp.toLp 2
      (ReverseDerivative.envelopeGraph S ζ ρ A (fun x ↦ (u.val x).ofLp) y)) =
    -((∫ y, φ y • WithLp.toLp 2
        (ReverseDerivative.envelopeGraph S ζ ρ (ReverseDerivative.remainderAmplitude C A i)
          (fun x ↦ (u.val x).ofLp) y)) +
      ∑ j, ∫ y, φ y • WithLp.toLp 2
        (ReverseDerivative.envelopeGraph S ζ ρ (ReverseDerivative.datumAmplitude C A i j)
          (fun x ↦ ((graphTestPartialDeriv j u).val x).ofLp) y)) := by
  let L := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
  let Lr := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)
  have hu : ContDiff ℝ ∞ (fun y ↦ (u.val y).ofLp) := Lr.contDiff.comp u.property.1
  have hw := (reverseTransferRegularization_of_compact hX hY hF hΦ hA i hC hu hinv hgrad).weak_derivative φ
  have he := congrArg L.symm hw
  simp only [map_neg, map_add, map_sum] at he
  simp_rw [← L.symm.integral_comp_comm] at he
  simp only [map_smul] at he
  simpa only [L, PiLp.coe_symm_continuousLinearEquiv,
    graphTestPartialDeriv_coordinates] using he

end JanetCartan.ResponseTransfer.SpatialRealization
