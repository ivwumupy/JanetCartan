module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.IntegratedJets

/-!
# Frequency integration of the complete reverse low-envelope graph

For `app:ch_response:thm:response-literal-transfer`, use the full nonlinear
inverse-chart gap on active frequencies. All other bounds follow from primitive
phase and full-amplitude grades. The loss is fixed independently of accuracy.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.LowEnvelope
open FourierIntegral NormalComparison JanetCartan.Localization
variable {n r : ℕ}

/-- Reverse integrated-jet estimate for
`app:ch_response:thm:response-literal-transfer`. The actual inverse-chart gap
is supplied before perturbation by the low Fourier covector. No separation-only
replacement, kernel bound, or output estimate is assumed. -/
theorem norm_reverse_outputJetIntegral_le
    {Ω K : Set (Euclidean n)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ y : Euclidean n) (α : List (Fin n)) (q b : ℕ)
    (C : ℕ → ℕ → ℝ) (PS Pφ : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hPS : ∀ j, 0 ≤ PS j) (hPφ : ∀ j, 0 ≤ Pφ j)
    {c Z a L ρ Λ : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hL : 1 ≤ L)
    (hLρ : L ≤ ρ) (hΛ : 0 ≤ Λ)
    (hζ : ‖ζ‖ ≤ Z) (hΛρ : Λ ≤ c * ρ / 2)
    (hS : ∀ η, ContDiff ℝ ∞ (fun z ↦ S z η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ∀ η, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    (hs : ∀ η z x, x ∉ K → A z x η = 0)
    (hgap : ∀ η, (∃ z x, A z x η ≠ 0) → ∀ x ∈ Ω,
      c * (ρ + ‖η‖) ≤ ‖ρ • fderiv ℝ φ x - fderiv ℝ (fun z ↦ S z η) x‖)
    (hAj : ∀ η (β : List (Fin n)) k z x,
      ‖iteratedFDeriv ℝ k (fun w ↦ normalMatrixDerivList β (fun v ↦ A v w η) z) x‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (hSj : ∀ η j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ S z η) x‖ ≤ PS j * ‖η‖ * L ^ (j - 1))
    (hφj : ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j φ x‖ ≤ Pφ j * L ^ (j - 1))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    (hfs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    ‖∫ η, ∫ θ, (sourceKernel
        (fun x ↦ reverseSourcePhase S φ ρ y η θ x - ρ * inner ℝ y ζ)
        (outputJetAmplitude (reverseTargetPhase ζ ρ) α A) y η).mulVec
          (paperL2FourierTransform f θ)‖ ≤
      ((r : ℝ) * lowEnvelopeJetConstant n (c / 2) (PS 1 + Pφ 1 + c / 2)
        (fun j ↦ PS (j + 1) + Pφ (j + 1)) (fun _ ↦ 1 + Z) C α.length q *
        volume.real K * lowEnvelopeRadialMass n) * a * ρ ^ (b + α.length + n) *
        (L / ρ) ^ q *
        (Real.sqrt (volume.real (Metric.ball (0 : Euclidean n) 1)) *
          Λ ^ ((n : ℝ) / 2) * ((2 * Real.pi) ^ (-(n : ℝ) / 2) * ‖f‖)) := by
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  have hZ : 0 ≤ Z := (norm_nonneg ζ).trans hζ
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  simp_rw [sourceKernel_sub_const, Matrix.smul_mulVec, integral_smul]
  rw [norm_smul]
  have he : ‖Complex.exp ((-(↑(ρ * inner ℝ y ζ) : ℂ)) * Complex.I)‖ = 1 := by
    simpa using Complex.norm_exp_ofReal_mul_I (-(ρ * inner ℝ y ζ))
  rw [he, one_mul]
  apply norm_lowSupport_outputJetIntegral_le hΩ hK hKΩ
    (fun η θ ↦ reverseSourcePhase S φ ρ y η θ) (reverseTargetPhase ζ ρ) A y α q b C
    (fun _ ↦ 1 + Z) (fun j ↦ PS (j + 1) + Pφ (j + 1)) hC
    (fun _ ↦ add_nonneg zero_le_one hZ) (by positivity) ha hL hLρ hΛ
    (fun η θ _ ↦ (((contDiff_const.sub (hS η)).add (contDiff_const.mul hφ)).add
      (contDiff_id.inner ℝ contDiff_const)).contDiffOn)
    (fun η ↦ contDiff_id.inner ℝ contDiff_const) hA hs
  · intro η hactive θ hθ x hx
    exact reverseSourcePhase_gap S φ hc.le y η θ x
      ((hS η).differentiable (by simp) x) (hφ.differentiable (by simp) x)
      (hgap η hactive x hx) (hθ.trans hΛρ)
  · intro η θ hθ x _
    rw [fderiv_reverseSourcePhase S φ ρ y η θ x
      ((hS η).differentiable (by simp) x) (hφ.differentiable (by simp) x)]
    have hS1 : ‖fderiv ℝ (fun z ↦ S z η) x‖ ≤ PS 1 * ‖η‖ := by
      simpa only [norm_iteratedFDeriv_one, Nat.sub_self, pow_zero, mul_one] using hSj η 1 le_rfl x
    have hφ1 : ‖fderiv ℝ φ x‖ ≤ Pφ 1 := by
      simpa only [norm_iteratedFDeriv_one, Nat.sub_self, pow_zero, mul_one] using hφj 1 le_rfl x
    calc
      _ ≤ ‖ρ • fderiv ℝ φ x‖ + ‖fderiv ℝ (fun z ↦ S z η) x‖ + ‖innerSL ℝ θ‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ ρ * Pφ 1 + PS 1 * ‖η‖ + c * ρ / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, innerSL_apply_norm]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hφ1 hρ.le) hS1) (hθ.trans hΛρ)
      _ ≤ _ := by
        nlinarith [mul_nonneg (hPS 1) hρ.le, mul_nonneg (hPφ 1) (norm_nonneg η),
          mul_nonneg hc.le (norm_nonneg η)]
  · intro η θ _ x _ j hj
    rw [norm_iteratedFDeriv_reverseSourcePhase_eq_forwardTargetPhase S φ ρ y η θ x (hS η) hφ j hj]
    simpa only [Nat.add_sub_cancel] using
      norm_iteratedFDeriv_forwardTargetPhase_le S φ η x hρ.le hL0 PS Pφ hPS hPφ (hS η) hφ
        (fun j hj ↦ hSj η j hj x) (fun j hj ↦ hφj j hj x) (j + 1) (by omega)
  · exact hAj
  · intro η j hj z
    exact norm_iteratedFDeriv_reverseTargetPhase_le ζ z η hρ.le hL0 hζ j hj
  · exact hfs

end JanetCartan.ResponseTransfer.LowEnvelope
