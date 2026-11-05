module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.OutputJets.Integral
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.OutputJets.SourceEstimates

/-!
# Output differentiation for the low-envelope graph kernels

Exact all-order identities, compact support, and quantitative output-derivative
source-kernel bounds for the complete matrix amplitudes in
`app:ch_response:thm:response-literal-transfer`. The primitive mixed derivative
grades imply the modified amplitude bounds with an offset fixed before the
integration order. Radial integration and Sobolev assembly belong to the
consuming low-envelope construction.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope

open FourierIntegral NormalComparison JanetCartan.Localization

variable {n r : ℕ}

/-- Every output derivative of the exact demodulated forward source integral
is the source integral of the modified full amplitude
(`app:ch_response:thm:response-literal-transfer`). -/
theorem normalMatrixDerivList_forwardDemodulatedKernel
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ) (η θ : Euclidean n)
    (hS : ContDiff ℝ ∞ (fun x ↦ S x η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ x y, y ∉ K → A x y η = 0) (α : List (Fin n)) (x : Euclidean n) :
    normalMatrixDerivList α (fun z ↦
        sourceKernel (fun y ↦ forwardSourcePhase S ζ ρ z η θ y - ρ * φ z) A z η) x =
      sourceKernel (fun y ↦ forwardSourcePhase S ζ ρ x η θ y - ρ * φ x)
        (outputJetAmplitude (forwardTargetPhase S φ ρ) α A) x η := by
  simp_rw [forwardSourcePhase_sub_outputCarrier, sub_eq_add_neg]
  exact normalMatrixDerivList_sourceKernel_splitPhase (forwardTargetPhase S φ ρ)
    (fun y ↦ -inner ℝ (η - ρ • ζ - θ) y) A η (hS.sub (contDiff_const.mul hφ))
    (innerSL ℝ (η - ρ • ζ - θ)).contDiff.neg hA hK hs α x

/-- Every output derivative of the exact demodulated reverse source integral,
retaining the nonlinear inverse-chart source phase and all matrix weights
(`app:ch_response:thm:response-literal-transfer`). -/
theorem normalMatrixDerivList_reverseDemodulatedKernel
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ) (η θ : Euclidean n)
    (hS : ContDiff ℝ ∞ (fun x ↦ S x η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ y x, x ∉ K → A y x η = 0) (α : List (Fin n)) (y : Euclidean n) :
    normalMatrixDerivList α (fun z ↦
        sourceKernel (fun x ↦ reverseSourcePhase S φ ρ z η θ x - ρ * inner ℝ z ζ) A z η) y =
      sourceKernel (fun x ↦ reverseSourcePhase S φ ρ y η θ x - ρ * inner ℝ y ζ)
        (outputJetAmplitude (reverseTargetPhase ζ ρ) α A) y η := by
  simp_rw [reverseSourcePhase_sub_outputCarrier]
  apply normalMatrixDerivList_sourceKernel_splitPhase (reverseTargetPhase ζ ρ)
    (fun x ↦ -S x η + ρ * φ x + inner ℝ x θ) A η ?_ ?_ hA hK hs α y
  · exact contDiff_id.inner ℝ contDiff_const
  · exact (hS.neg.add (contDiff_const.mul hφ)).add
      (contDiff_id.inner ℝ contDiff_const)

/-- Norm identity reducing the differentiated forward kernel to the existing
`norm_forwardSourceKernel_le` with the actual modified amplitude
(`app:ch_response:thm:response-literal-transfer`). -/
theorem norm_normalMatrixDerivList_forwardDemodulatedKernel
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ) (η θ : Euclidean n)
    (hS : ContDiff ℝ ∞ (fun x ↦ S x η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ x y, y ∉ K → A x y η = 0) (α : List (Fin n)) (x : Euclidean n) :
    ‖normalMatrixDerivList α (fun z ↦
        sourceKernel (fun y ↦ forwardSourcePhase S ζ ρ z η θ y - ρ * φ z) A z η) x‖ =
      ‖sourceKernel (forwardSourcePhase S ζ ρ x η θ)
        (outputJetAmplitude (forwardTargetPhase S φ ρ) α A) x η‖ := by
  rw [normalMatrixDerivList_forwardDemodulatedKernel S φ A ζ ρ η θ hS hφ hA hK hs,
    norm_sourceKernel_sub_const]

/-- Norm identity reducing the differentiated reverse kernel to the existing
`norm_sourceKernel_le`, with its exact nonlinear reverse source phase
(`app:ch_response:thm:response-literal-transfer`). -/
theorem norm_normalMatrixDerivList_reverseDemodulatedKernel
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ) (η θ : Euclidean n)
    (hS : ContDiff ℝ ∞ (fun x ↦ S x η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ y x, x ∉ K → A y x η = 0) (α : List (Fin n)) (y : Euclidean n) :
    ‖normalMatrixDerivList α (fun z ↦
        sourceKernel (fun x ↦ reverseSourcePhase S φ ρ z η θ x - ρ * inner ℝ z ζ) A z η) y‖ =
      ‖sourceKernel (reverseSourcePhase S φ ρ y η θ)
        (outputJetAmplitude (reverseTargetPhase ζ ρ) α A) y η‖ := by
  rw [normalMatrixDerivList_reverseDemodulatedKernel S φ A ζ ρ η θ hS hφ hA hK hs,
    norm_sourceKernel_sub_const]

/-- Output derivatives of the complete forward source kernel satisfy the
integration-by-parts estimate from primitive full-amplitude and phase jets
(`app:ch_response:thm:response-literal-transfer`). Carrier separation and low
source Fourier frequency produce the source gap. The constants depend on the
profiles and orders, and the fixed offset `b` is independent of `q`.
Radial integration and Sobolev membership remain with the consuming construction. -/
theorem norm_normalMatrixDerivList_forwardDemodulatedKernel_le
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ x η θ : Euclidean n) (α : List (Fin n)) (q b : ℕ)
    (C : ℕ → ℕ → ℝ) (PS Pφ : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hPS : ∀ j, 0 ≤ PS j) (hPφ : ∀ j, 0 ≤ Pφ j)
    {c Z a L ρ : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hL : 1 ≤ L)
    (hρ : 0 < ρ) (hLR : L ≤ ρ + ‖η‖)
    (hζ : ‖ζ‖ ≤ Z) (hη : c * ρ ≤ ‖η - ρ • ζ‖) (hθ : ‖θ‖ ≤ c * ρ / 2)
    (hS : ContDiff ℝ ∞ (fun z ↦ S z η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ z y, y ∉ K → A z y η = 0)
    (hAj : ∀ (β : List (Fin n)) k z y,
      ‖iteratedFDeriv ℝ k (fun w ↦ normalMatrixDerivList β (fun v ↦ A v w η) z) y‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (hSj : ∀ j, 1 ≤ j → ∀ z,
      ‖iteratedFDeriv ℝ j (fun w ↦ S w η) z‖ ≤ PS j * ‖η‖ * L ^ (j - 1))
    (hφj : ∀ j, 1 ≤ j → ∀ z,
      ‖iteratedFDeriv ℝ j φ z‖ ≤ Pφ j * L ^ (j - 1)) :
    ‖normalMatrixDerivList α (fun z ↦
        sourceKernel (fun y ↦ forwardSourcePhase S ζ ρ z η θ y - ρ * φ z) A z η) x‖ ≤
      (transposeDerivativeConstant (EuclideanSpace.basisFun (Fin n) ℝ)
        (phaseCoefficientDerivativeBound (EuclideanSpace.basisFun (Fin n) ℝ)
          ((forwardGapConstant c Z) ^ 2) (1 + Z + c / 2) (fun _ ↦ 0))
        (outputJetAmplitudeGrade (fun j ↦ PS j + Pφ j) C α.length) q 0 *
        ((a * L ^ b * (ρ + ‖η‖) ^ α.length) * (L / (ρ + ‖η‖)) ^ q)) *
          MeasureTheory.volume.real K := by
  rw [norm_normalMatrixDerivList_forwardDemodulatedKernel S φ A ζ ρ η θ hS hφ hA hK hs]
  apply norm_sourceKernel_outputJetAmplitude_le isOpen_univ hK (Set.subset_univ K)
    (forwardSourcePhase S ζ ρ x η θ) (forwardTargetPhase S φ ρ) A x η α q b C
    (fun j ↦ PS j + Pφ j) (fun _ ↦ 0) hC (fun j ↦ add_nonneg (hPS j) (hPφ j))
    (forwardGapConstant_pos hc ((norm_nonneg ζ).trans hζ)) ha hL hρ hLR
    (contDiff_const.sub (innerSL ℝ (η - ρ • ζ - θ)).contDiff).contDiffOn
    (hS.sub (contDiff_const.mul hφ)) hA hs
    (fun y _ ↦ forwardSourcePhase_gap S hc hρ.le hζ hη hθ x y)
    (fun y _ ↦ norm_fderiv_forwardSourcePhase_le S hc.le hρ.le hζ hθ x y)
    (fun y _ j hj ↦ by simp [norm_iteratedFDeriv_forwardSourcePhase_eq_zero S ζ ρ x η θ y hj])
    hAj
  intro j hj z
  exact norm_iteratedFDeriv_forwardTargetPhase_le S φ η z hρ.le (zero_le_one.trans hL)
    PS Pφ hPS hPφ hS hφ (fun j hj ↦ hSj j hj z) (fun j hj ↦ hφj j hj z) j hj

/-- Output derivatives of the exact reverse source kernel satisfy the
integration-by-parts estimate from primitive full-amplitude and phase jets
(`app:ch_response:thm:response-literal-transfer`). The full nonlinear inverse-chart
gap is an explicit geometric premise. Its perturbation by the low Fourier
frequency, all higher source phase grades, and all output-amplitude grades are
proved here. The compact support and fixed offset are independent of `q`. -/
theorem norm_normalMatrixDerivList_reverseDemodulatedKernel_le
    {Ω K : Set (Euclidean n)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ y η θ : Euclidean n) (α : List (Fin n)) (q b : ℕ)
    (C : ℕ → ℕ → ℝ) (PS Pφ : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hPS : ∀ j, 0 ≤ PS j) (hPφ : ∀ j, 0 ≤ Pφ j)
    {c Z a L ρ : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hL : 1 ≤ L)
    (hρ : 0 < ρ) (hLR : L ≤ ρ + ‖η‖)
    (hζ : ‖ζ‖ ≤ Z) (hθ : ‖θ‖ ≤ c * ρ / 2)
    (hS : ContDiff ℝ ∞ (fun z ↦ S z η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    (hs : ∀ z x, x ∉ K → A z x η = 0)
    (hgap : ∀ x ∈ Ω,
      c * (ρ + ‖η‖) ≤ ‖ρ • fderiv ℝ φ x - fderiv ℝ (fun z ↦ S z η) x‖)
    (hAj : ∀ (β : List (Fin n)) k z x,
      ‖iteratedFDeriv ℝ k (fun w ↦ normalMatrixDerivList β (fun v ↦ A v w η) z) x‖ ≤
        C β.length k * a * L ^ (b + β.length + k))
    (hSj : ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ S z η) x‖ ≤ PS j * ‖η‖ * L ^ (j - 1))
    (hφj : ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j φ x‖ ≤ Pφ j * L ^ (j - 1)) :
    ‖normalMatrixDerivList α (fun z ↦
        sourceKernel (fun x ↦ reverseSourcePhase S φ ρ z η θ x - ρ * inner ℝ z ζ) A z η) y‖ ≤
      (transposeDerivativeConstant (EuclideanSpace.basisFun (Fin n) ℝ)
        (phaseCoefficientDerivativeBound (EuclideanSpace.basisFun (Fin n) ℝ)
          ((c / 2) ^ 2) (PS 1 + Pφ 1 + c / 2) (fun j ↦ PS (j + 1) + Pφ (j + 1)))
        (outputJetAmplitudeGrade (fun _ ↦ 1 + Z) C α.length) q 0 *
        ((a * L ^ b * (ρ + ‖η‖) ^ α.length) * (L / (ρ + ‖η‖)) ^ q)) *
          MeasureTheory.volume.real K := by
  rw [norm_normalMatrixDerivList_reverseDemodulatedKernel S φ A ζ ρ η θ hS hφ hA hK hs]
  have hZ : 0 ≤ Z := (norm_nonneg ζ).trans hζ
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  apply norm_sourceKernel_outputJetAmplitude_le hΩ hK hKΩ
    (reverseSourcePhase S φ ρ y η θ) (reverseTargetPhase ζ ρ) A y η α q b C
    (fun _ ↦ 1 + Z) (fun j ↦ PS (j + 1) + Pφ (j + 1)) hC
    (fun _ ↦ add_nonneg zero_le_one hZ) (by positivity) ha hL hρ hLR
    (((contDiff_const.sub hS).add (contDiff_const.mul hφ)).add
      (contDiff_id.inner ℝ contDiff_const)).contDiffOn
    (contDiff_id.inner ℝ contDiff_const) hA hs
  · intro x hx
    exact reverseSourcePhase_gap S φ hc.le y η θ x
      (hS.differentiable (by simp) x) (hφ.differentiable (by simp) x) (hgap x hx) hθ
  · intro x _
    rw [fderiv_reverseSourcePhase S φ ρ y η θ x
      (hS.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
    have hS1 : ‖fderiv ℝ (fun z ↦ S z η) x‖ ≤ PS 1 * ‖η‖ := by
      simpa only [norm_iteratedFDeriv_one, Nat.sub_self, pow_zero, mul_one] using hSj 1 le_rfl x
    have hφ1 : ‖fderiv ℝ φ x‖ ≤ Pφ 1 := by
      simpa only [norm_iteratedFDeriv_one, Nat.sub_self, pow_zero, mul_one] using hφj 1 le_rfl x
    calc
      _ ≤ ‖ρ • fderiv ℝ φ x‖ + ‖fderiv ℝ (fun z ↦ S z η) x‖ + ‖innerSL ℝ θ‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ ρ * Pφ 1 + PS 1 * ‖η‖ + c * ρ / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, innerSL_apply_norm]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hφ1 hρ.le) hS1) hθ
      _ ≤ _ := by
        nlinarith [mul_nonneg (hPS 1) hρ.le, mul_nonneg (hPφ 1) (norm_nonneg η),
          mul_nonneg hc.le (norm_nonneg η)]
  · intro x _ j hj
    rw [norm_iteratedFDeriv_reverseSourcePhase_eq_forwardTargetPhase S φ ρ y η θ x hS hφ j hj]
    simpa only [Nat.add_sub_cancel] using
      norm_iteratedFDeriv_forwardTargetPhase_le S φ η x hρ.le hL0 PS Pφ hPS hPφ hS hφ
        (fun j hj ↦ hSj j hj x) (fun j hj ↦ hφj j hj x) (j + 1) (by omega)
  · exact hAj
  · intro j hj z
    exact norm_iteratedFDeriv_reverseTargetPhase_le ζ z η hρ.le hL0 hζ j hj

end JanetCartan.ResponseTransfer.LowEnvelope
