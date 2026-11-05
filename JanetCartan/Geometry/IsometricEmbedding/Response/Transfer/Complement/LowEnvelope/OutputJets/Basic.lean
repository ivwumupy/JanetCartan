module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.ForwardGap
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.ReversePhase
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.TransportExtension.CoordinateDerivatives
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral

/-!
# Actual output jets of the complete graph amplitude

The construction in `app:ch_response:thm:response-literal-transfer` retains both
physical positions and the physical frequency. The ordered derivatives are the
existing matrix coordinate derivatives. All cutoffs remain inside the amplitude.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope

open FourierIntegral JanetCartan.Localization NormalComparison

variable {n r : ℕ}

/-- The target-only forward demodulated phase in
`app:ch_response:thm:response-literal-transfer`. -/
def forwardTargetPhase (S : Euclidean n → Euclidean n → ℝ)
    (φ : Euclidean n → ℝ) (ρ : ℝ) (x η : Euclidean n) : ℝ :=
  S x η - ρ * φ x

/-- The target-only reverse demodulated phase in
`app:ch_response:thm:response-literal-transfer`. -/
def reverseTargetPhase (ζ : Euclidean n) (ρ : ℝ) (y η : Euclidean n) : ℝ :=
  inner ℝ y (η - ρ • ζ)

/-- Exact forward splitting used for output differentiation in
`app:ch_response:thm:response-literal-transfer`. -/
theorem forwardSourcePhase_sub_outputCarrier
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (ζ : Euclidean n) (ρ : ℝ) (x η θ y : Euclidean n) :
    forwardSourcePhase S ζ ρ x η θ y - ρ * φ x =
      forwardTargetPhase S φ ρ x η - inner ℝ (η - ρ • ζ - θ) y := by
  unfold forwardSourcePhase forwardTargetPhase
  ring

/-- Exact reverse splitting, keeping the nonlinear source phase, in
`app:ch_response:thm:response-literal-transfer`. -/
theorem reverseSourcePhase_sub_outputCarrier
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (ζ : Euclidean n) (ρ : ℝ) (y η θ x : Euclidean n) :
    reverseSourcePhase S φ ρ y η θ x - ρ * inner ℝ y ζ =
      reverseTargetPhase ζ ρ y η + (-S x η + ρ * φ x + inner ℝ x θ) := by
  simp only [reverseSourcePhase, reverseTargetPhase, inner_sub_right,
    real_inner_smul_right]
  ring

/-- `exp(-iτ) D^α(exp(iτ) A)`, the actual modified full matrix amplitude
for `app:ch_response:thm:response-literal-transfer`. -/
def outputJetAmplitude (τ : Euclidean n → Euclidean n → ℝ)
    (α : List (Fin n)) (A : FullAmplitude n r) : FullAmplitude n r :=
  fun x y η ↦ phaseOscillation (fun z ↦ -τ z η) x •
    normalMatrixDerivList α (fun z ↦ phaseOscillation (fun w ↦ τ w η) z • A z y η) x

/-- Smooth target oscillations in the output-jet construction of
`app:ch_response:thm:response-literal-transfer`. -/
theorem contDiff_outputOscillation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {τ : E → ℝ} (hτ : ContDiff ℝ ∞ τ) : ContDiff ℝ ∞ (phaseOscillation τ) :=
  ((Complex.ofRealCLM.contDiff.comp hτ).mul contDiff_const).cexp

/-- Cancellation of demodulation in the output-jet identity
(`app:ch_response:thm:response-literal-transfer`). -/
theorem outputOscillation_mul_neg (τ : Euclidean n → ℝ) (x : Euclidean n) :
    phaseOscillation τ x * phaseOscillation (fun z ↦ -τ z) x = 1 := by
  simp [phaseOscillation, ← Complex.exp_add ]

/-- Exact derivative identity defining the modified amplitude in
`app:ch_response:thm:response-literal-transfer`; no derivative estimate is assumed. -/
theorem outputOscillation_smul_outputJetAmplitude
    (τ : Euclidean n → Euclidean n → ℝ) (α : List (Fin n))
    (A : FullAmplitude n r) (x y η : Euclidean n) :
    phaseOscillation (fun z ↦ τ z η) x • outputJetAmplitude τ α A x y η =
      normalMatrixDerivList α (fun z ↦ phaseOscillation (fun w ↦ τ w η) z • A z y η) x := by
  rw [outputJetAmplitude, smul_smul, outputOscillation_mul_neg, one_smul]

/-- The order-zero modified amplitude is the original full amplitude
(`app:ch_response:thm:response-literal-transfer`). -/
@[simp] theorem outputJetAmplitude_nil
    (τ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r) :
    outputJetAmplitude τ [] A = A := by
  funext x y η
  simp only [outputJetAmplitude, normalMatrixDerivList, smul_smul]
  rw [mul_comm, outputOscillation_mul_neg, one_smul]

/-- Constant source oscillations pass through target derivatives in
`app:ch_response:thm:response-literal-transfer`. -/
theorem normalMatrixDerivList_const_smul
    {f : Euclidean n → Matrix (Fin r) (Fin r) ℂ} (hf : ContDiff ℝ ∞ f)
    (c : ℂ) (α : List (Fin n)) :
    normalMatrixDerivList α (fun x ↦ c • f x) =
      fun x ↦ c • normalMatrixDerivList α f x := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    funext x
    simp only [normalMatrixDerivList, ih]
    exact congrArg (fun L : Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℂ ↦
      L (EuclideanSpace.single i 1))
      (((contDiff_normalMatrixDerivList hf α).differentiable (by simp) x).hasFDerivAt.const_smul c).fderiv

/-- Ordered target derivatives vanish on a source slice which vanishes
identically, as needed for the original source cutoffs in
`app:ch_response:thm:response-literal-transfer`. -/
theorem normalMatrixDerivList_zero (α : List (Fin n)) :
    normalMatrixDerivList (r := r) α (0 : Euclidean n → Matrix (Fin r) (Fin r) ℂ) = 0 := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    funext x
    simp [normalMatrixDerivList, ih]

/-- Uniform source support is preserved by output differentiation in
`app:ch_response:thm:response-literal-transfer`. The hypothesis applies to all
target positions; support of one individual slice would not suffice. -/
theorem outputJetAmplitude_eq_zero_off_source
    (τ : Euclidean n → Euclidean n → ℝ) (α : List (Fin n))
    (A : FullAmplitude n r) {K : Set (Euclidean n)}
    (hs : ∀ x y η, y ∉ K → A x y η = 0) (x y η : Euclidean n) (hy : y ∉ K) :
    outputJetAmplitude τ α A x y η = 0 := by
  have he : (fun z ↦ phaseOscillation (fun w ↦ τ w η) z • A z y η) = 0 := by
    funext z
    simp [hs z y η hy]
  simp [outputJetAmplitude, he, normalMatrixDerivList_zero]

/-- The original closed source set contains the modified amplitude's topological
support (`app:ch_response:thm:response-literal-transfer`). -/
theorem tsupport_outputJetAmplitude_subset
    (τ : Euclidean n → Euclidean n → ℝ) (α : List (Fin n))
    (A : FullAmplitude n r) {K : Set (Euclidean n)} (hK : IsClosed K)
    (hs : ∀ x y η, y ∉ K → A x y η = 0) (x η : Euclidean n) :
    tsupport (fun y ↦ outputJetAmplitude τ α A x y η) ⊆ K := by
  apply closure_minimal ?_ hK
  intro y hy
  by_contra hn
  exact hy (outputJetAmplitude_eq_zero_off_source τ α A hs x y η hn)

/-- Compact source support survives every output jet, with the same compact
source set (`app:ch_response:thm:response-literal-transfer`). -/
theorem hasCompactSupport_outputJetAmplitude
    (τ : Euclidean n → Euclidean n → ℝ) (α : List (Fin n))
    (A : FullAmplitude n r) {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ x y η, y ∉ K → A x y η = 0) (x η : Euclidean n) :
    HasCompactSupport (fun y ↦ outputJetAmplitude τ α A x y η) :=
  hK.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_outputJetAmplitude_subset τ α A hK.isClosed hs x η)

/-- Joint smoothness of actual target coordinate jets, with the source position
retained as a parameter (`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiff_joint_normalMatrixDerivList
    {f : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hf : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ f p.1 p.2))
    (α : List (Fin n)) :
    ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
      normalMatrixDerivList α (fun x ↦ f x p.2) p.1) := by
  induction α with
  | nil => exact hf
  | cons i α ih =>
    have h := ih.comp (f := fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      (p.2, p.1.2)) (by fun_prop)
    exact h.fderiv_apply contDiff_fst contDiff_const (by simp)

/-- The full modified amplitude is smooth in both physical positions, for
`app:ch_response:thm:response-literal-transfer`. -/
theorem contDiff_outputJetAmplitude
    (τ : Euclidean n → Euclidean n → ℝ) (α : List (Fin n))
    (A : FullAmplitude n r) (η : Euclidean n)
    (hτ : ContDiff ℝ ∞ (fun x ↦ τ x η))
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η)) :
    ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
      outputJetAmplitude τ α A p.1 p.2 η) := by
  exact ((contDiff_outputOscillation hτ.neg).comp contDiff_fst).smul
    (contDiff_joint_normalMatrixDerivList
      (f := fun x y ↦ phaseOscillation (fun w ↦ τ w η) x • A x y η)
      (((contDiff_outputOscillation hτ).comp contDiff_fst).smul hA) α)

/-- The source-only phase is constant under target differentiation. This is the
literal integrand identity for `app:ch_response:thm:response-literal-transfer`. -/
theorem normalMatrixDerivList_splitPhase
    (τ : Euclidean n → Euclidean n → ℝ) (σ : Euclidean n → ℝ)
    (α : List (Fin n)) (A : FullAmplitude n r) (x y η : Euclidean n)
    (hτ : ContDiff ℝ ∞ (fun z ↦ τ z η))
    (hA : ContDiff ℝ ∞ (fun z ↦ A z y η)) :
    normalMatrixDerivList α
        (fun z ↦ phaseOscillation (fun w ↦ τ w η + σ y) z • A z y η) x =
      phaseOscillation (fun z ↦ τ x η + σ z) y • outputJetAmplitude τ α A x y η := by
  have he (z : Euclidean n) :
      phaseOscillation (fun w ↦ τ w η + σ y) z =
        phaseOscillation σ y * phaseOscillation (fun w ↦ τ w η) z := by
    simp only [phaseOscillation, Complex.ofReal_add, add_mul, Complex.exp_add]
    exact mul_comm _ _
  simp_rw [he, mul_smul]
  rw [normalMatrixDerivList_const_smul
    (f := fun z ↦ phaseOscillation (fun w ↦ τ w η) z • A z y η)
    ((contDiff_outputOscillation hτ).smul hA)]
  have he' : phaseOscillation (fun z ↦ τ x η + σ z) y =
      phaseOscillation σ y * phaseOscillation (fun z ↦ τ z η) x := he x
  rw [he', mul_smul, outputOscillation_smul_outputJetAmplitude]

/-- The first output jet is the amplitude derivative plus the actual target
phase derivative, for `app:ch_response:thm:response-literal-transfer`. -/
theorem outputJetAmplitude_singleton (τ : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r) (i : Fin n) (x y η : Euclidean n)
    (hτ : ContDiff ℝ ∞ (fun z ↦ τ z η))
    (hA : ContDiff ℝ ∞ (fun z ↦ A z y η)) :
    outputJetAmplitude τ [i] A x y η =
      normalMatrixDerivList [i] (fun z ↦ A z y η) x +
        (((fderiv ℝ (fun z ↦ τ z η) x (EuclideanSpace.single i 1) : ℝ) : ℂ) *
          Complex.I) • A x y η := by
  unfold outputJetAmplitude
  simp only [normalMatrixDerivList]
  rw [fderiv_fun_smul ((contDiff_outputOscillation hτ).differentiable (by simp) x)
    (hA.differentiable (by simp) x)]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply]
  rw [fderiv_phaseOscillation _ (hτ.differentiable (by simp) x), smul_add]
  simp only [smul_smul]
  rw [show phaseOscillation (fun z ↦ -τ z η) x *
      (phaseOscillation (fun z ↦ τ z η) x *
        ((fderiv ℝ (fun z ↦ τ z η) x (EuclideanSpace.single i 1) : ℝ) : ℂ) * Complex.I) =
      ((fderiv ℝ (fun z ↦ τ z η) x (EuclideanSpace.single i 1) : ℝ) : ℂ) * Complex.I by
        rw [← mul_assoc, ← mul_assoc, mul_comm (phaseOscillation (fun z ↦ -τ z η) x),
          outputOscillation_mul_neg, one_mul],
    mul_comm (phaseOscillation (fun z ↦ -τ z η) x), outputOscillation_mul_neg, one_smul]


/-- Exact ordered recursion for the modified amplitudes in
`app:ch_response:thm:response-literal-transfer`. Together with
`outputJetAmplitude_singleton`, this gives the differential recurrence used
to derive quantitative grades from the primitive amplitude and phase jets. -/
theorem outputJetAmplitude_cons_eq_singleton (τ : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r) (α : List (Fin n)) (i : Fin n) (x y η : Euclidean n) :
    outputJetAmplitude τ (i :: α) A x y η =
      outputJetAmplitude τ [i] (outputJetAmplitude τ α A) x y η := by
  have he : (fun z ↦ phaseOscillation (fun w ↦ τ w η) z •
      outputJetAmplitude τ α A z y η) =
      normalMatrixDerivList α (fun z ↦ phaseOscillation (fun w ↦ τ w η) z • A z y η) :=
    funext fun z ↦ outputOscillation_smul_outputJetAmplitude τ α A z y η
  change _ = phaseOscillation (fun z ↦ -τ z η) x •
    fderiv ℝ (fun z ↦ phaseOscillation (fun w ↦ τ w η) z •
      outputJetAmplitude τ α A z y η) x (EuclideanSpace.single i 1)
  rw [he]
  rfl

end JanetCartan.ResponseTransfer.LowEnvelope
