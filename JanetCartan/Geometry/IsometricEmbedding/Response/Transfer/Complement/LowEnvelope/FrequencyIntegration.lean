module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.Radial
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FourierReconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.OutputJets
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.MatrixKernels

/-!
# Frequency integration against the low-support L² datum

This is the radial/Fourier-L¹ step of
`app:ch_response:thm:response-literal-transfer`. `norm_lowSupport_kernelIntegral_le`
is only an integration lemma; `norm_lowSupport_outputJetIntegral_le` discharges
its kernel premise using repeated source integration by parts and primitive
mixed amplitude/phase grades. The literal graph reconstruction and output
Sobolev realization are separate steps.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.LowEnvelope
open FourierIntegral NormalComparison JanetCartan.Localization
variable {n r : ℕ}

private theorem norm_mulVec_euclidean_le (M : Matrix (Fin r) (Fin r) ℂ)
    (v : EuclideanSpace ℂ (Fin r)) : ‖M.mulVec v‖ ≤ (r : ℝ) * ‖M‖ * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc
    ‖M.mulVec v i‖ ≤ ∑ j, ‖M i j * v j‖ := by
      simpa only [Matrix.mulVec, dotProduct] using
        norm_sum_le Finset.univ (fun j ↦ M i j * v j)
    _ ≤ ∑ _j : Fin r, ‖M‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (AmplitudeBound.norm_matrixEntry_le_frobenius M i j)
        (PiLp.norm_apply_le v j) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

/-- Integrate a matrix kernel profile against an actual low-support L² Fourier
datum (`app:ch_response:thm:response-literal-transfer`). This elementary helper
is consumed by `norm_lowSupport_outputJetIntegral_le`, which proves its kernel
premise from the primitive derivative hypotheses. The norms on the input are
Hilbert norms; the finite output coordinate norm is the Pi norm. -/
theorem norm_lowSupport_kernelIntegral_le
    (M : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    {Λ L ρ B : ℝ} (hΛ : 0 ≤ Λ) (hL : 0 ≤ L) (hρ : 0 < ρ)
    (hLρ : L ≤ ρ) (hB : 0 ≤ B) (s q : ℕ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0)
    (hM : ∀ η θ, ‖θ‖ ≤ Λ → ‖M η θ‖ ≤
      B * ((ρ + ‖η‖) ^ s * (L / (ρ + ‖η‖)) ^ (q + s + n + 1))) :
    ‖∫ η, ∫ θ, (M η θ).mulVec (paperL2FourierTransform f θ)‖ ≤
      ((r : ℝ) * B * lowEnvelopeRadialMass n * ρ ^ (s + n) * (L / ρ) ^ q) *
        (Real.sqrt (volume.real (Metric.ball (0 : Euclidean n) 1)) *
          Λ ^ ((n : ℝ) / 2) * ((2 * Real.pi) ^ (-(n : ℝ) / 2) * ‖f‖)) := by
  let H := paperL2FourierTransform f
  let W := fun η : Euclidean n ↦
    (ρ + ‖η‖) ^ s * (L / (ρ + ‖η‖)) ^ (q + s + n + 1)
  obtain ⟨hH, hHb⟩ := paperL2FourierTransform_lowSupport_L1 f hΛ hs
  obtain ⟨hW, hWb⟩ := integral_lowEnvelope_kernel_profile_le (n := n) hL hρ hLρ s q
  have hWi (η : Euclidean n) : 0 ≤ W η := by dsimp [W]; positivity
  have hinner (η : Euclidean n) :
      ‖∫ θ, (M η θ).mulVec (H θ)‖ ≤ ((r : ℝ) * B * W η) * ∫ θ, ‖H θ‖ := by
    apply (norm_integral_le_of_norm_le (hH.norm.const_mul ((r : ℝ) * B * W η)) ?_).trans_eq
      (integral_const_mul _ _)
    filter_upwards [hs] with θ hθ
    change ‖(M η θ).mulVec (H θ)‖ ≤ ((r : ℝ) * B * W η) * ‖H θ‖
    by_cases ht : ‖θ‖ ≤ Λ
    · exact (norm_mulVec_euclidean_le (M η θ) (H θ)).trans (by
        have hh := mul_le_mul_of_nonneg_left (hM η θ ht) (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
        simpa only [mul_assoc, W] using mul_le_mul_of_nonneg_right hh (norm_nonneg (H θ)))
    · have hz : H θ = 0 := hθ (lt_of_not_ge ht)
      simp [hz]
  calc
    _ ≤ ∫ η, ((r : ℝ) * B * W η) * ∫ θ, ‖H θ‖ :=
      norm_integral_le_of_norm_le ((hW.const_mul ((r : ℝ) * B)).mul_const _)
        (Filter.Eventually.of_forall hinner)
    _ = ((r : ℝ) * B * ∫ η, W η) * ∫ θ, ‖H θ‖ := by
      rw [integral_mul_const, integral_const_mul]
    _ ≤ ((r : ℝ) * B * (lowEnvelopeRadialMass n * ρ ^ (s + n) * (L / ρ) ^ q)) *
        (Real.sqrt (volume.real (Metric.ball (0 : Euclidean n) 1)) *
          Λ ^ ((n : ℝ) / 2) * ((2 * Real.pi) ^ (-(n : ℝ) / 2) * ‖f‖)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hWb (by positivity)) hHb
        (integral_nonneg (fun _ ↦ norm_nonneg _))
        (by have := lowEnvelopeRadialMass_nonneg n; positivity)
    _ = _ := by ring

/-- The source-IBP profile constant for the integrated output jet in
`app:ch_response:thm:response-literal-transfer`. This constant depends on the
fixed derivative profiles and integration orders, not on the physical scales. -/
def lowEnvelopeJetConstant (n : ℕ) (c G : ℝ) (Q P : ℕ → ℝ)
    (C : ℕ → ℕ → ℝ) (s q : ℕ) : ℝ :=
  transposeDerivativeConstant (EuclideanSpace.basisFun (Fin n) ℝ)
    (phaseCoefficientDerivativeBound (EuclideanSpace.basisFun (Fin n) ℝ)
      (c ^ 2) G Q) (outputJetAmplitudeGrade P C s) (q + s + n + 1) 0

/-- Nonnegativity of the explicit source-IBP constant. -/
theorem lowEnvelopeJetConstant_nonneg (c G : ℝ) (Q P : ℕ → ℝ)
    (C : ℕ → ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (hC : ∀ m k, 0 ≤ C m k)
    (n s q : ℕ) : 0 ≤ lowEnvelopeJetConstant n c G Q P C s q :=
  transposeDerivativeConstant_nonneg _ (phaseCoefficientDerivativeBound_nonneg _ _ _ _)
    (outputJetAmplitudeGrade_nonneg P C hP hC s) _ _

end JanetCartan.ResponseTransfer.LowEnvelope
