module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FrequencyIntegration

/-!
# Integrated source kernels from primitive derivative grades

The analytic bound feeding the literal low-envelope graph Sobolev estimate in
`app:ch_response:thm:response-literal-transfer`. Every source kernel estimate is
derived here. The source gap is needed only at covectors at which the original
full amplitude is nonzero; this allows complete complementary selectors and
all their transition regions. The offset `b` and polynomial loss `b+|α|+n`
are fixed independently of the accuracy order `q`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.LowEnvelope
open FourierIntegral NormalComparison JanetCartan.Localization
variable {n r : ℕ}

/-- Source integrations, radial integration, and low-support Fourier L¹ control
for `app:ch_response:thm:response-literal-transfer`, from primitive mixed jets.
The output is the integrated differentiated kernel, before its identification
with the derivative of the literal compact-frequency graph. No oscillatory
kernel estimate is assumed. All measures are Euclidean Lebesgue measures. -/
theorem norm_lowSupport_outputJetIntegral_le
    {Ω K : Set (Euclidean n)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (ψ : Euclidean n → Euclidean n → Euclidean n → ℝ)
    (τ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (x : Euclidean n) (α : List (Fin n)) (q b : ℕ)
    (C : ℕ → ℕ → ℝ) (P Q : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hP : ∀ j, 0 ≤ P j)
    {c G a L ρ Λ : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hL : 1 ≤ L)
    (hLρ : L ≤ ρ) (hΛ : 0 ≤ Λ)
    (hψ : ∀ η θ, ‖θ‖ ≤ Λ → ContDiffOn ℝ ∞ (ψ η θ) Ω)
    (hτ : ∀ η, ContDiff ℝ ∞ (fun z ↦ τ z η))
    (hA : ∀ η, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    (hs : ∀ η z y, y ∉ K → A z y η = 0)
    (hgap : ∀ η, (∃ z y, A z y η ≠ 0) → ∀ θ, ‖θ‖ ≤ Λ → ∀ y ∈ Ω,
      c * (ρ + ‖η‖) ≤ ‖fderiv ℝ (ψ η θ) y‖)
    (hupper : ∀ η θ, ‖θ‖ ≤ Λ → ∀ y ∈ Ω,
      ‖fderiv ℝ (ψ η θ) y‖ ≤ G * (ρ + ‖η‖))
    (hψj : ∀ η θ, ‖θ‖ ≤ Λ → ∀ y ∈ K, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (ψ η θ) y‖ ≤ Q j * (ρ + ‖η‖) * L ^ j)
    (hAj : ∀ η (β : List (Fin n)) k z y,
      ‖iteratedFDeriv ℝ k (fun w ↦ normalMatrixDerivList β (fun v ↦ A v w η) z) y‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (hτj : ∀ η j, 1 ≤ j → ∀ z,
      ‖iteratedFDeriv ℝ j (fun w ↦ τ w η) z‖ ≤ P j * (ρ + ‖η‖) * L ^ (j - 1))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    (hfs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    ‖∫ η, ∫ θ, (sourceKernel (ψ η θ) (outputJetAmplitude τ α A) x η).mulVec
        (paperL2FourierTransform f θ)‖ ≤
      ((r : ℝ) * lowEnvelopeJetConstant n c G Q P C α.length q *
        volume.real K * lowEnvelopeRadialMass n) * a * ρ ^ (b + α.length + n) *
        (L / ρ) ^ q *
        (Real.sqrt (volume.real (Metric.ball (0 : Euclidean n) 1)) *
          Λ ^ ((n : ℝ) / 2) * ((2 * Real.pi) ^ (-(n : ℝ) / 2) * ‖f‖)) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hρ : 0 < ρ := (lt_of_lt_of_le zero_lt_one hL).trans_le hLρ
  let D := lowEnvelopeJetConstant n c G Q P C α.length q
  have hD : 0 ≤ D := lowEnvelopeJetConstant_nonneg c G Q P C hP hC n α.length q
  have hV : 0 ≤ volume.real K := ENNReal.toReal_nonneg
  have hbound (η θ : Euclidean n) (hθ : ‖θ‖ ≤ Λ) :
      ‖sourceKernel (ψ η θ) (outputJetAmplitude τ α A) x η‖ ≤
        (D * (a * ρ ^ b) * volume.real K) *
          ((ρ + ‖η‖) ^ α.length * (L / (ρ + ‖η‖)) ^ (q + α.length + n + 1)) := by
    by_cases hactive : ∃ z y, A z y η ≠ 0
    · have hb := norm_sourceKernel_outputJetAmplitude_le hΩ hK hKΩ (ψ η θ) τ A x η α
        (q + α.length + n + 1) b C P Q hC hP hc ha hL hρ
        (hLρ.trans (le_add_of_nonneg_right (norm_nonneg η))) (hψ η θ hθ) (hτ η)
        (hA η) (hs η) (hgap η hactive θ hθ) (hupper η θ hθ) (hψj η θ hθ)
        (hAj η) (hτj η)
      change ‖sourceKernel (ψ η θ) (outputJetAmplitude τ α A) x η‖ ≤
        (D * ((a * L ^ b * (ρ + ‖η‖) ^ α.length) *
          (L / (ρ + ‖η‖)) ^ (q + α.length + n + 1))) * volume.real K at hb
      apply hb.trans
      have hh := pow_le_pow_left₀ hL0 hLρ b
      have hp := mul_le_mul_of_nonneg_left hh
        (show 0 ≤ D * a * (ρ + ‖η‖) ^ α.length *
          (L / (ρ + ‖η‖)) ^ (q + α.length + n + 1) * volume.real K by positivity)
      convert hp using 1 <;> ring
    · have hz (z y : Euclidean n) : A z y η = 0 := by
        by_contra hn
        exact hactive ⟨z, y, hn⟩
      have hj (y : Euclidean n) : outputJetAmplitude τ α A x y η = 0 := by
        have he : (fun z ↦ phaseOscillation (fun w ↦ τ w η) z • A z y η) = 0 := by
          funext z
          simp [hz z y]
        simp [outputJetAmplitude, he, normalMatrixDerivList_zero]
      simp only [sourceKernel, hj, smul_zero, integral_zero, norm_zero]
      positivity
  have hb := norm_lowSupport_kernelIntegral_le
    (fun η θ ↦ sourceKernel (ψ η θ) (outputJetAmplitude τ α A) x η)
    f hΛ hL0 hρ hLρ (show 0 ≤ D * (a * ρ ^ b) * volume.real K by positivity)
    α.length q hfs hbound
  apply hb.trans_eq
  simp only [pow_add]
  dsimp [D]
  ring

/-- Integrated output-jet bound for the actual complete forward complement in
`app:ch_response:thm:response-literal-transfer`. Its source gap is derived from
the selector plateau and low Fourier support. The full complementary amplitude
retains both positions and every original cutoff. The phase is already
output-demodulated; the graph's outer `(2π)⁻ⁿ` is restored at reconstruction. -/
theorem norm_forwardComplement_outputJetIntegral_le
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (χ : Euclidean n → ℂ) (ζ x : Euclidean n)
    (α : List (Fin n)) (q b : ℕ) (C : ℕ → ℕ → ℝ) (PS Pφ : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hPS : ∀ j, 0 ≤ PS j) (hPφ : ∀ j, 0 ≤ Pφ j)
    {c Z a L ρ Λ : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hL : 1 ≤ L)
    (hLρ : L ≤ ρ) (hΛ : 0 ≤ Λ) (hΛρ : Λ ≤ c * ρ / 2)
    (hζ : ‖ζ‖ ≤ Z) (hχ : ∀ δ, ‖δ‖ < c * ρ → χ δ = 1)
    (hS : ∀ η, ContDiff ℝ ∞ (fun z ↦ S z η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ∀ η, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
      complementaryAmplitude A ζ ρ χ p.1 p.2 η))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ η z y, y ∉ K → complementaryAmplitude A ζ ρ χ z y η = 0)
    (hAj : ∀ η (β : List (Fin n)) k z y,
      ‖iteratedFDeriv ℝ k (fun w ↦ normalMatrixDerivList β
        (fun v ↦ complementaryAmplitude A ζ ρ χ v w η) z) y‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (hSj : ∀ η j, 1 ≤ j → ∀ z,
      ‖iteratedFDeriv ℝ j (fun w ↦ S w η) z‖ ≤ PS j * ‖η‖ * L ^ (j - 1))
    (hφj : ∀ j, 1 ≤ j → ∀ z,
      ‖iteratedFDeriv ℝ j φ z‖ ≤ Pφ j * L ^ (j - 1))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    (hfs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    ‖∫ η, ∫ θ, (sourceKernel
        (forwardSourcePhase (fun z ξ ↦ S z ξ - ρ * φ z) ζ ρ x η θ)
        (outputJetAmplitude (forwardTargetPhase S φ ρ) α
          (complementaryAmplitude A ζ ρ χ)) x η).mulVec (paperL2FourierTransform f θ)‖ ≤
      ((r : ℝ) * lowEnvelopeJetConstant n (forwardGapConstant c Z)
        (1 + Z + c / 2) (fun _ ↦ 0) (fun j ↦ PS j + Pφ j) C α.length q *
        volume.real K * lowEnvelopeRadialMass n) * a * ρ ^ (b + α.length + n) *
        (L / ρ) ^ q *
        (Real.sqrt (volume.real (Metric.ball (0 : Euclidean n) 1)) *
          Λ ^ ((n : ℝ) / 2) * ((2 * Real.pi) ^ (-(n : ℝ) / 2) * ‖f‖)) := by
  have hρ : 0 ≤ ρ := (zero_le_one.trans hL).trans hLρ
  apply norm_lowSupport_outputJetIntegral_le isOpen_univ hK (Set.subset_univ K)
    (fun η θ ↦ forwardSourcePhase (fun z ξ ↦ S z ξ - ρ * φ z) ζ ρ x η θ)
    (forwardTargetPhase S φ ρ) (complementaryAmplitude A ζ ρ χ) x α q b C
    (fun j ↦ PS j + Pφ j) (fun _ ↦ 0) hC
    (fun j ↦ add_nonneg (hPS j) (hPφ j))
    (forwardGapConstant_pos hc ((norm_nonneg ζ).trans hζ)) ha hL hLρ hΛ
    (fun η θ _ ↦ (contDiff_const.sub
      (innerSL ℝ (η - ρ • ζ - θ)).contDiff).contDiffOn)
    (fun η ↦ (hS η).sub (contDiff_const.mul hφ)) hA hs ?_ ?_ ?_ hAj ?_ f hfs
  · intro η hactive θ hθ y _
    obtain ⟨z, w, hne⟩ := hactive
    have hsep : c * ρ ≤ ‖η - ρ • ζ‖ := by
      by_contra hn
      exact hne (by simp [complementaryAmplitude, hχ _ (lt_of_not_ge hn)])
    exact forwardSourcePhase_gap _ hc hρ hζ hsep (hθ.trans hΛρ) x y
  · intro η θ hθ y _
    exact norm_fderiv_forwardSourcePhase_le _ hc.le hρ hζ (hθ.trans hΛρ) x y
  · intro η θ _ y _ j hj
    simp [norm_iteratedFDeriv_forwardSourcePhase_eq_zero _ ζ ρ x η θ y hj]
  · intro η j hj z
    exact norm_iteratedFDeriv_forwardTargetPhase_le S φ η z hρ (zero_le_one.trans hL)
      PS Pφ hPS hPφ (hS η) hφ (fun j hj ↦ hSj η j hj z) (fun j hj ↦ hφj j hj z) j hj

end JanetCartan.ResponseTransfer.LowEnvelope
