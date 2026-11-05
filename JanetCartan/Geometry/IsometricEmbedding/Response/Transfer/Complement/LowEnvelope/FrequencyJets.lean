module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FrequencyJets.Differentiation

/-!
# Frequency-integrated jets of the literal demodulated graphs

For `app:ch_response:thm:response-literal-transfer`, the actual compact-frequency
forward and reverse graphs are smooth, and every ordered scalar coordinate
jet is the integral of the full modified amplitude, with the physical outer
`(2π)⁻ⁿ`. The datum is Hilbert-valued L² with low physical Fourier support;
Fourier L¹ control is proved, not assumed. The original target supports are
preserved by the imported `Basic` support theorems.

The primitive amplitude grades are those consumed by
`norm_forwardComplement_outputJetIntegral_le` and
`norm_lowSupport_outputJetIntegral_le` in `LowEnvelope.IntegratedJets`.
Compact frequency support turns the primitive phase grades into the uniform
profiles needed for differentiation. Only joint continuity and smooth physical
slices of the phase are required, including at frequency zero. The amplitude
can be the complete `complementaryAmplitude` or `reverseFullAmplitude`:
no cutoff, shoulder, bounded-frequency piece, or physical position is removed.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope

open FourierIntegral NormalComparison AmplitudeBound JanetCartan.Localization

variable {n r : ℕ}

/-- Smoothness, ordered output jets, and absolute joint frequency integrability
for the literal forward graph in `app:ch_response:thm:response-literal-transfer`.
The primitive grades match `norm_forwardComplement_outputJetIntegral_le` when
`A` is the complete complementary amplitude. The Fourier datum and normalization
are instantiated here; no physical L¹ premise or output estimate is used. -/
theorem forwardDemodulatedGraph_lowSupport_frequencyJets
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) {ρ L a : ℝ}
    (hρ : 0 ≤ ρ) (hL : 0 ≤ L) (ha : 0 ≤ a) (b : ℕ)
    (hSc : Continuous (fun p : Euclidean n × Euclidean n ↦ S p.1 p.2))
    (hS : ∀ η, ContDiff ℝ ∞ (fun x ↦ S x η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      A p.1.1 p.1.2 p.2))
    {Ks Kη : Set (Euclidean n)} (hKs : IsCompact Ks) (hKη : IsCompact Kη)
    (hs : ∀ x y η, y ∉ Ks → A x y η = 0)
    (hf : ∀ x y η, η ∉ Kη → A x y η = 0)
    (C : ℕ → ℕ → ℝ) (PS Pφ : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hPS : ∀ j, 0 ≤ PS j) (hPφ : ∀ j, 0 ≤ Pφ j)
    (hAj : ∀ η (β : List (Fin n)) k x y,
      ‖iteratedFDeriv ℝ k (fun w ↦ normalMatrixDerivList β (fun z ↦ A z w η) x) y‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (hSj : ∀ η j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ S z η) x‖ ≤ PS j * ‖η‖ * L ^ (j - 1))
    (hφj : ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j φ x‖ ≤ Pφ j * L ^ (j - 1))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hfs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    ContDiff ℝ ∞ (forwardDemodulatedGraph S φ A ζ ρ (fun y ↦ ⇑(f y))) ∧
    (∀ (α : List (Fin n)) (x : Euclidean n) (i : Fin r),
      euclideanCoordinateDerivList α
        (fun z ↦ forwardDemodulatedGraph S φ A ζ ρ (fun y ↦ ⇑(f y)) z i) x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ *
        (∫ η, ∫ θ, (sourceKernel
          (forwardSourcePhase (fun z ξ ↦ S z ξ - ρ * φ z) ζ ρ x η θ)
          (outputJetAmplitude (forwardTargetPhase S φ ρ) α A) x η).mulVec
            (paperL2FourierTransform f θ)) i) ∧
    (∀ (α : List (Fin n)) (x : Euclidean n),
      Integrable (fun p : Euclidean n × Euclidean n ↦
        (sourceKernel
          (forwardSourcePhase (fun z ξ ↦ S z ξ - ρ * φ z) ζ ρ x p.1 p.2)
          (outputJetAmplitude (forwardTargetPhase S φ ρ) α A) x p.1).mulVec
            (paperL2FourierTransform f p.2)) (volume.prod volume)) := by
  obtain ⟨R, hR, hηR⟩ := hKη.isBounded.exists_pos_norm_le
  let C₀ := fun m k ↦ C m k * a * L ^ (b + m + k)
  let P := fun j ↦ (PS j + Pφ j) * (ρ + R) * L ^ (j - 1)
  have hC₀ : ∀ m k, 0 ≤ C₀ m k := fun m k ↦
    mul_nonneg (mul_nonneg (hC m k) ha) (pow_nonneg hL _)
  have hP : ∀ j, 0 ≤ P j := fun j ↦
    mul_nonneg (mul_nonneg (add_nonneg (hPS j) (hPφ j))
      (add_nonneg hρ hR.le)) (pow_nonneg hL _)
  have hτ : Continuous (fun p : Euclidean n × Euclidean n ↦
      forwardTargetPhase S φ ρ p.1 p.2) :=
    hSc.sub (continuous_const.mul (hφ.continuous.comp continuous_fst))
  have hτs : ∀ η, ContDiff ℝ ∞ (forwardTargetPhase S φ ρ · η) :=
    fun η ↦ (hS η).sub (contDiff_const.mul hφ)
  let σ := fun (η θ y : Euclidean n) ↦ -inner ℝ (η - ρ • ζ - θ) y
  have hσ : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      σ p.1.1 p.1.2 p.2) := by dsimp [σ]; fun_prop
  have hσs : ∀ η θ, ContDiff ℝ ∞ (σ η θ) :=
    fun η θ ↦ (innerSL ℝ (η - ρ • ζ - θ)).contDiff.neg
  have hτj : ∀ η ∈ Kη, ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ forwardTargetPhase S φ ρ z η) x‖ ≤ P j := by
    intro η hη j hj x
    exact (norm_iteratedFDeriv_forwardTargetPhase_le S φ η x hρ hL PS Pφ hPS hPφ
      (hS η) hφ (fun j hj ↦ hSj η j hj x) (fun j hj ↦ hφj j hj x) j hj).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add_right (hηR η hη) ρ)
            (add_nonneg (hPS j) (hPφ j))) (pow_nonneg hL _))
  have hH := (paperL2FourierTransform_lowSupport_L1 f hΛ hfs).1
  have hd := contDiff_integral_sourceKernel_splitPhase
    (forwardTargetPhase S φ ρ) σ A hτ hσ hτs hσs hA hKs hKη hs hf
    C₀ P hC₀ hP hAj hτj (paperL2FourierTransform f) hH
  have hj := euclideanCoordinateDerivList_integral_sourceKernel_splitPhase
    (forwardTargetPhase S φ ρ) σ A hτ hσ hτs hσs hA hKs hKη hs hf
    C₀ P hC₀ hP hAj hτj (paperL2FourierTransform f) hH
  have hi := integrable_sourceKernel_outputJet_mulVec_splitPhase
    (forwardTargetPhase S φ ρ) σ A hτ hσ hτs hσs hA hKs hKη hs hf
    C₀ P hC₀ hP hAj hτj (paperL2FourierTransform f) hH
  have he (x : Euclidean n) := forwardDemodulatedGraph_lowSupport_reconstruction
    S φ A ζ ρ x (fun η ↦ hA.continuous.comp
      ((continuous_const.prodMk continuous_id).prodMk continuous_const))
    (fun η ↦ by
      simpa only [outputJetAmplitude_nil] using
        hasCompactSupport_outputJetAmplitude (forwardTargetPhase S φ ρ) [] A hKs hs x η)
    f hΛ hfs
  have he' : forwardDemodulatedGraph S φ A ζ ρ (fun y ↦ ⇑(f y)) =
      fun x ↦ ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ θ,
        (sourceKernel (fun y ↦ forwardTargetPhase S φ ρ x η + σ η θ y)
          A x η).mulVec (paperL2FourierTransform f θ) := funext he
  rw [he']
  refine ⟨hd.const_smul _, ?_, hi⟩
  intro α x i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Pseudodifferential.euclideanCoordinateDerivList_const_mul
    (contDiff_pi.mp hd i)]
  exact congrArg (fun z : ℂ ↦ ((2 * Real.pi) ^ n : ℂ)⁻¹ * z) (hj α x i)


/-- Smoothness, ordered output jets, and absolute joint frequency integrability
for the literal reverse graph in `app:ch_response:thm:response-literal-transfer`.
The full amplitude may in particular be `reverseFullAmplitude`, including its
weights, matrix order and both cutoffs. Only the affine reverse target phase is
differentiated; the nonlinear source phase is retained exactly. -/
theorem reverseDemodulatedGraph_lowSupport_frequencyJets
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) {ρ L a : ℝ}
    (hρ : 0 ≤ ρ) (hL : 0 ≤ L) (ha : 0 ≤ a) (b : ℕ)
    (hSc : Continuous (fun p : Euclidean n × Euclidean n ↦ S p.1 p.2))
    (hS : ∀ η, ContDiff ℝ ∞ (fun x ↦ S x η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      A p.1.1 p.1.2 p.2))
    {Ks Kη : Set (Euclidean n)} (hKs : IsCompact Ks) (hKη : IsCompact Kη)
    (hs : ∀ y x η, x ∉ Ks → A y x η = 0)
    (hf : ∀ y x η, η ∉ Kη → A y x η = 0)
    (C : ℕ → ℕ → ℝ) (hC : ∀ m k, 0 ≤ C m k)
    (hAj : ∀ η (β : List (Fin n)) k y x,
      ‖iteratedFDeriv ℝ k (fun w ↦ normalMatrixDerivList β (fun z ↦ A z w η) y) x‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hfs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    ContDiff ℝ ∞ (reverseDemodulatedGraph S φ A ζ ρ (fun x ↦ ⇑(f x))) ∧
    (∀ (α : List (Fin n)) (y : Euclidean n) (i : Fin r),
      euclideanCoordinateDerivList α
        (fun z ↦ reverseDemodulatedGraph S φ A ζ ρ (fun x ↦ ⇑(f x)) z i) y =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ *
        (∫ η, ∫ θ, (sourceKernel
          (fun x ↦ reverseSourcePhase S φ ρ y η θ x - ρ * inner ℝ y ζ)
          (outputJetAmplitude (reverseTargetPhase ζ ρ) α A) y η).mulVec
            (paperL2FourierTransform f θ)) i) ∧
    (∀ (α : List (Fin n)) (y : Euclidean n),
      Integrable (fun p : Euclidean n × Euclidean n ↦
        (sourceKernel
          (fun x ↦ reverseSourcePhase S φ ρ y p.1 p.2 x - ρ * inner ℝ y ζ)
          (outputJetAmplitude (reverseTargetPhase ζ ρ) α A) y p.1).mulVec
            (paperL2FourierTransform f p.2)) (volume.prod volume)) := by
  simp_rw [reverseSourcePhase_sub_outputCarrier]
  obtain ⟨R, hR, hηR⟩ := hKη.isBounded.exists_pos_norm_le
  let C₀ := fun m k ↦ C m k * a * L ^ (b + m + k)
  let P := fun (_ : ℕ) ↦ (1 + ‖ζ‖) * (ρ + R)
  have hC₀ : ∀ m k, 0 ≤ C₀ m k := fun m k ↦
    mul_nonneg (mul_nonneg (hC m k) ha) (pow_nonneg hL _)
  have hP : ∀ j, 0 ≤ P j := fun _ ↦
    mul_nonneg (by positivity) (add_nonneg hρ hR.le)
  have hτ : Continuous (fun p : Euclidean n × Euclidean n ↦
      reverseTargetPhase ζ ρ p.1 p.2) := by unfold reverseTargetPhase; fun_prop
  have hτs : ∀ η, ContDiff ℝ ∞ (reverseTargetPhase ζ ρ · η) :=
    fun η ↦ contDiff_id.inner ℝ contDiff_const
  let σ := fun (η θ x : Euclidean n) ↦ -S x η + ρ * φ x + inner ℝ x θ
  have hσ : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      σ p.1.1 p.1.2 p.2) :=
    ((hSc.comp (continuous_snd.prodMk continuous_fst.fst)).neg.add
      (continuous_const.mul (hφ.continuous.comp continuous_snd))).add
        (continuous_snd.inner continuous_fst.snd)
  have hσs : ∀ η θ, ContDiff ℝ ∞ (σ η θ) := fun η θ ↦
    ((hS η).neg.add (contDiff_const.mul hφ)).add (contDiff_id.inner ℝ contDiff_const)
  have hτj : ∀ η ∈ Kη, ∀ j, 1 ≤ j → ∀ y,
      ‖iteratedFDeriv ℝ j (fun z ↦ reverseTargetPhase ζ ρ z η) y‖ ≤ P j := by
    intro η hη j hj y
    have hb := norm_iteratedFDeriv_reverseTargetPhase_le ζ y η hρ
      (show (0 : ℝ) ≤ 1 by norm_num) (le_refl ‖ζ‖) j hj
    simp only [one_pow, mul_one] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add_right (hηR η hη) ρ)
      (by positivity))
  have hH := (paperL2FourierTransform_lowSupport_L1 f hΛ hfs).1
  have hd := contDiff_integral_sourceKernel_splitPhase
    (reverseTargetPhase ζ ρ) σ A hτ hσ hτs hσs hA hKs hKη hs hf
    C₀ P hC₀ hP hAj hτj (paperL2FourierTransform f) hH
  have hj := euclideanCoordinateDerivList_integral_sourceKernel_splitPhase
    (reverseTargetPhase ζ ρ) σ A hτ hσ hτs hσs hA hKs hKη hs hf
    C₀ P hC₀ hP hAj hτj (paperL2FourierTransform f) hH
  have hi := integrable_sourceKernel_outputJet_mulVec_splitPhase
    (reverseTargetPhase ζ ρ) σ A hτ hσ hτs hσs hA hKs hKη hs hf
    C₀ P hC₀ hP hAj hτj (paperL2FourierTransform f) hH
  have he (y : Euclidean n) := reverseDemodulatedGraph_lowSupport_reconstruction
    S φ A ζ ρ y hφ.continuous (fun η ↦ (hS η).continuous)
    (fun η ↦ hA.continuous.comp
      ((continuous_const.prodMk continuous_id).prodMk continuous_const))
    (fun η ↦ by
      simpa only [outputJetAmplitude_nil] using
        hasCompactSupport_outputJetAmplitude (reverseTargetPhase ζ ρ) [] A hKs hs y η)
    f hΛ hfs
  simp_rw [reverseSourcePhase_sub_outputCarrier] at he
  have he' : reverseDemodulatedGraph S φ A ζ ρ (fun x ↦ ⇑(f x)) =
      fun y ↦ ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ θ,
        (sourceKernel (fun x ↦ reverseTargetPhase ζ ρ y η + σ η θ x)
          A y η).mulVec (paperL2FourierTransform f θ) := funext he
  rw [he']
  refine ⟨hd.const_smul _, ?_, hi⟩
  intro α y i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Pseudodifferential.euclideanCoordinateDerivList_const_mul
    (contDiff_pi.mp hd i)]
  exact congrArg (fun z : ℂ ↦ ((2 * Real.pi) ^ n : ℂ)⁻¹ * z) (hj α y i)

end JanetCartan.ResponseTransfer.LowEnvelope
