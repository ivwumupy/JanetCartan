module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FrequencyJets.Basic

/-!
# Scalar coordinates of the differentiated source kernels

The bridge from `NormalComparison.normalMatrixDerivList` to
`AmplitudeBound.euclideanCoordinateDerivList` needed by the frequency integral
in `app:ch_response:thm:response-literal-transfer`. The vector on which the
matrix acts is fixed during target differentiation; its Fourier variable remains
an integration parameter. Matrix multiplication order is unchanged.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope
open FourierIntegral NormalComparison AmplitudeBound JanetCartan.Localization
variable {n r : ℕ}

/-- Evaluation by a fixed matrix functional commutes with the ordered target
derivatives in `app:ch_response:thm:response-literal-transfer`. This is used
below for the coordinates of the matrix acting on the Fourier datum. -/
theorem euclideanCoordinateDerivList_matrixFunctional
    {g : Euclidean n → Matrix (Fin r) (Fin r) ℂ} (hg : ContDiff ℝ ∞ g)
    (T : Matrix (Fin r) (Fin r) ℂ →L[ℝ] ℂ) (α : List (Fin n)) :
    euclideanCoordinateDerivList α (fun x ↦ T (g x)) =
      fun x ↦ T (normalMatrixDerivList α g x) := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    funext x
    simp only [euclideanCoordinateDerivList, normalMatrixDerivList, ih]
    exact congrArg (fun L : Euclidean n →L[ℝ] ℂ ↦ L (EuclideanSpace.single i 1))
      (T.hasFDerivAt.comp x
        ((contDiff_normalMatrixDerivList hg α).differentiable (by simp) x).hasFDerivAt).fderiv

/-- Scalar coordinate jets of matrix action preserve the original action order,
as required by the low-envelope frequency integral in
`app:ch_response:thm:response-literal-transfer`. -/
theorem euclideanCoordinateDerivList_matrixMulVec
    {g : Euclidean n → Matrix (Fin r) (Fin r) ℂ} (hg : ContDiff ℝ ∞ g)
    (v : Fin r → ℂ) (i : Fin r) (α : List (Fin n)) (x : Euclidean n) :
    euclideanCoordinateDerivList α (fun z ↦ (g z).mulVec v i) x =
      (normalMatrixDerivList α g x).mulVec v i := by
  let T : Matrix (Fin r) (Fin r) ℂ →L[ℝ] ℂ :=
    ∑ j, v j • matrixEntryEvaluation i j
  have hT (M : Matrix (Fin r) (Fin r) ℂ) : T M = M.mulVec v i := by
    simp only [T, sum_apply, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    change v j * M i j = M i j * v j
    exact mul_comm _ _
  simpa only [hT] using congrFun
    (euclideanCoordinateDerivList_matrixFunctional hg T α) x

/-- Smoothness of the actual compact source integral in its target, before
frequency integration in `app:ch_response:thm:response-literal-transfer`.
No frequency smoothness of the phase is required. -/
theorem contDiff_sourceKernel_splitPhase
    (τ : Euclidean n → Euclidean n → ℝ) (σ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (η : Euclidean n)
    (hτ : ContDiff ℝ ∞ (fun x ↦ τ x η)) (hσ : ContDiff ℝ ∞ σ)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ x y, y ∉ K → A x y η = 0) :
    ContDiff ℝ ∞ (fun x ↦ sourceKernel (fun y ↦ τ x η + σ y) A x η) := by
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  have hf : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
      phaseOscillation (fun y ↦ τ p.1 η + σ y) p.2 • A p.1 p.2 η) :=
    (contDiff_outputOscillation ((hτ.comp contDiff_fst).add
      (hσ.comp contDiff_snd))).smul hA
  have he (x : Euclidean n) : sourceKernel (fun y ↦ τ x η + σ y) A x η =
      ∫ y in K, phaseOscillation (fun y ↦ τ x η + σ y) y • A x y η := by
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy ↦ by simp [hs x y hy])).symm
  simp_rw [he]
  exact contDiffOn_univ.mp (contDiffOn_compactParameterIntegral
    isOpen_univ isOpen_univ hK (Set.subset_univ _) hf.contDiffOn)

/-- Ordered scalar coordinate identity for the split-phase source kernel,
including its action on the actual Fourier datum. This is the integrand
identity for frequency differentiation in
`app:ch_response:thm:response-literal-transfer`. -/
theorem euclideanCoordinateDerivList_sourceKernel_splitPhase
    (τ : Euclidean n → Euclidean n → ℝ) (σ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (η : Euclidean n)
    (hτ : ContDiff ℝ ∞ (fun x ↦ τ x η)) (hσ : ContDiff ℝ ∞ σ)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ x y, y ∉ K → A x y η = 0)
    (v : Fin r → ℂ) (i : Fin r) (α : List (Fin n)) (x : Euclidean n) :
    euclideanCoordinateDerivList α
        (fun z ↦ (sourceKernel (fun y ↦ τ z η + σ y) A z η).mulVec v i) x =
      (sourceKernel (fun y ↦ τ x η + σ y) (outputJetAmplitude τ α A) x η).mulVec v i := by
  rw [euclideanCoordinateDerivList_matrixMulVec
    (contDiff_sourceKernel_splitPhase τ σ A η hτ hσ hA hK hs),
    normalMatrixDerivList_sourceKernel_splitPhase τ σ A η hτ hσ hA hK hs]

/-- The forward scalar-coordinate source identity in exactly the phase convention
of `norm_forwardComplement_outputJetIntegral_le`
(`app:ch_response:thm:response-literal-transfer`). -/
theorem euclideanCoordinateDerivList_forwardDemodulatedKernel
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ) (η θ : Euclidean n)
    (hS : ContDiff ℝ ∞ (fun x ↦ S x η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ x y, y ∉ K → A x y η = 0)
    (v : Fin r → ℂ) (i : Fin r) (α : List (Fin n)) (x : Euclidean n) :
    euclideanCoordinateDerivList α (fun z ↦
        (sourceKernel (forwardSourcePhase (fun w ξ ↦ S w ξ - ρ * φ w)
          ζ ρ z η θ) A z η).mulVec v i) x =
      (sourceKernel (forwardSourcePhase (fun w ξ ↦ S w ξ - ρ * φ w) ζ ρ x η θ)
        (outputJetAmplitude (forwardTargetPhase S φ ρ) α A) x η).mulVec v i := by
  exact euclideanCoordinateDerivList_sourceKernel_splitPhase (forwardTargetPhase S φ ρ)
    (fun y ↦ -inner ℝ (η - ρ • ζ - θ) y) A η
    (hS.sub (contDiff_const.mul hφ)) (innerSL ℝ (η - ρ • ζ - θ)).contDiff.neg
    hA hK hs v i α x

/-- The reverse scalar-coordinate source identity retains the nonlinear source
phase and output demodulation (`app:ch_response:thm:response-literal-transfer`). -/
theorem euclideanCoordinateDerivList_reverseDemodulatedKernel
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ) (η θ : Euclidean n)
    (hS : ContDiff ℝ ∞ (fun x ↦ S x η)) (hφ : ContDiff ℝ ∞ φ)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ y x, x ∉ K → A y x η = 0)
    (v : Fin r → ℂ) (i : Fin r) (α : List (Fin n)) (y : Euclidean n) :
    euclideanCoordinateDerivList α (fun z ↦
        (sourceKernel (fun x ↦ reverseSourcePhase S φ ρ z η θ x - ρ * inner ℝ z ζ)
          A z η).mulVec v i) y =
      (sourceKernel (fun x ↦ reverseSourcePhase S φ ρ y η θ x - ρ * inner ℝ y ζ)
        (outputJetAmplitude (reverseTargetPhase ζ ρ) α A) y η).mulVec v i := by
  simp_rw [reverseSourcePhase_sub_outputCarrier]
  exact euclideanCoordinateDerivList_sourceKernel_splitPhase (reverseTargetPhase ζ ρ)
    (fun x ↦ -S x η + ρ * φ x + inner ℝ x θ) A η
    (contDiff_id.inner ℝ contDiff_const)
    ((hS.neg.add (contDiff_const.mul hφ)).add (contDiff_id.inner ℝ contDiff_const))
    hA hK hs v i α y

end JanetCartan.ResponseTransfer.LowEnvelope
