module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.Selector
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.SourceKernel
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase

/-!
# Actual parameter jets of the complete graph amplitude

For `app:ch_response:thm:response-literal-transfer`, the graph phase `S`, full
amplitude `A`, physical covector `η`, and frequency `ρ` are held fixed.
`complementaryCarrierJet` is the actual parameter derivative of the original
carrier-weighted amplitude with its carrier factored back out. This definition
retains the moving selector. The identities and full-support statements below
are inputs to the finite kernel Leibniz expansion and graph-decay assembly.
No derivative expansion or complementary estimate is an assumption.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives

open FourierIntegral

variable {n r : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n

/-- The forward carrier phase in the original, unshifted physical integral
(`app:ch_response:thm:response-literal-transfer`). -/
def forwardCarrierPhase (ζ : P → E) (φ : P → E → ℝ) (c : P) (x y : E) : ℝ :=
  inner ℝ y (ζ c) - φ c x

/-- The reverse carrier phase, with output `y` and source `x`, for the literal
weighted reverse graph (`app:ch_response:thm:response-literal-transfer`). -/
def reverseCarrierPhase (ζ : P → E) (φ : P → E → ℝ) (c : P) (y x : E) : ℝ :=
  φ c x - inner ℝ y (ζ c)

/-- The two-position physical carrier factor. For a forward graph use
`forwardCarrierPhase`; for a reverse graph use `reverseCarrierPhase`.
Source: `app:ch_response:thm:response-literal-transfer`. -/
def parameterCarrierFactor (ψ : P → E → E → ℝ) (ρ : ℝ) (c : P) (x y : E) : ℂ :=
  Complex.exp (Complex.I * ((ρ * ψ c x y : ℝ) : ℂ))

/-- The complete scalar complementary coefficient, including carrier and
normalized moving selector (`app:ch_response:thm:response-literal-transfer`). -/
def complementaryCarrierCoefficient (q : E → ℂ) (ζ : P → E)
    (ψ : P → E → E → ℝ) (ρ : ℝ) (c : P) (x y η : E) : ℂ :=
  parameterCarrierFactor ψ ρ c x y * (1 - q (normalizedCarrierOffset ζ ρ η c))

/-- The actual differentiated full amplitude with the same carriers factored
back out. Both physical positions and all original weights are retained in `A`.
Source: `app:ch_response:thm:response-literal-transfer`. -/
def complementaryCarrierJet (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E)
    (ψ : P → E → E → ℝ) (ρ : ℝ) (k : ℕ) (v : Fin k → P) (c : P) :
    FullAmplitude n r := fun x y η ↦
  (parameterCarrierFactor ψ (-ρ) c x y *
    iteratedFDeriv ℝ k (fun b ↦ complementaryCarrierCoefficient q ζ ψ ρ b x y η) c v) •
      A x y η

/-- Smoothness of the complete carrier/selector coefficient follows from its
primitive factors on an open parameter neighborhood. In particular the
smoothness premise of `iteratedFDeriv_complementaryCarrierAmplitude` is not a
new realization obligation (`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffAt_complementaryCarrierCoefficient
    (q : E → ℂ) (ζ : P → E) (ψ : P → E → E → ℝ)
    (ρ : ℝ) {c : P} (x y η : E) {N : ℕ∞ω}
    (hζ : ContDiffAt ℝ N ζ c)
    (hq : ContDiffAt ℝ N q (normalizedCarrierOffset ζ ρ η c))
    (hψ : ContDiffAt ℝ N (fun b ↦ ψ b x y) c) :
    ContDiffAt ℝ N (fun b ↦ complementaryCarrierCoefficient q ζ ψ ρ b x y η) c := by
  have ho : ContDiffAt ℝ N (normalizedCarrierOffset ζ ρ η) c := by
    unfold normalizedCarrierOffset
    exact (contDiffAt_const.sub (hζ.const_smul ρ)).const_smul ρ⁻¹
  have he : ContDiffAt ℝ N (fun b ↦ parameterCarrierFactor ψ ρ b x y) c := by
    unfold parameterCarrierFactor
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp c (hψ.const_smul ρ)).const_smul
      Complex.I).cexp
  exact he.mul (contDiffAt_const.sub (hq.comp c ho))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Exact inverse-carrier identity in the physical normalization
(`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterCarrierFactor_neg_mul (ψ : P → E → E → ℝ)
    (ρ : ℝ) (c : P) (x y : E) :
    parameterCarrierFactor ψ (-ρ) c x y * parameterCarrierFactor ψ ρ c x y = 1 := by
  simp only [parameterCarrierFactor, neg_mul, Complex.ofReal_neg, mul_neg,
    ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The forward factor is the literal input carrier times output demodulation;
there is no change from physical covectors to unit Fourier frequencies.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem parameterCarrierFactor_forward (ζ : P → E) (φ : P → E → ℝ)
    (ρ : ℝ) (c : P) (x y : E) :
    parameterCarrierFactor (forwardCarrierPhase ζ φ) ρ c x y =
      carrier (-ρ) (φ c) x * carrier ρ (fun z ↦ inner ℝ z (ζ c)) y := by
  simp only [parameterCarrierFactor, forwardCarrierPhase, carrier, ← Complex.exp_add]
  congr 1
  push_cast
  ring

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The reverse factor uses the nonlinear source carrier and linear output
demodulation (`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterCarrierFactor_reverse (ζ : P → E) (φ : P → E → ℝ)
    (ρ : ℝ) (c : P) (y x : E) :
    parameterCarrierFactor (reverseCarrierPhase ζ φ) ρ c y x =
      carrier (-ρ) (fun z ↦ inner ℝ z (ζ c)) y * carrier ρ (φ c) x := by
  simp only [parameterCarrierFactor, reverseCarrierPhase, carrier, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Order zero recovers the original complete complementary amplitude
(`app:ch_response:thm:response-literal-transfer`). -/
theorem complementaryCarrierJet_zero (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E)
    (ψ : P → E → E → ℝ) (ρ : ℝ) (v : Fin 0 → P) (c : P) :
    complementaryCarrierJet A q ζ ψ ρ 0 v c = complementaryParameterFamily A q ζ ρ c := by
  funext x y η
  simp only [complementaryCarrierJet, iteratedFDeriv_zero_apply,
    complementaryCarrierCoefficient, ← mul_assoc, parameterCarrierFactor_neg_mul,
    one_mul, complementaryParameterFamily, complementaryAmplitude, normalizedCarrierOffset]

/-- Multiplication by the original carrier recovers the actual derivative of
the entire carrier-weighted complementary amplitude. This identifies the
coefficient with `iteratedFDeriv`, not a parameter-labelled family.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem iteratedFDeriv_complementaryCarrierAmplitude
    (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E)
    (ψ : P → E → E → ℝ) (ρ : ℝ) (k : ℕ) (v : Fin k → P) (c : P)
    (x y η : E)
    (h : ContDiffAt ℝ k (fun b ↦ complementaryCarrierCoefficient q ζ ψ ρ b x y η) c) :
    iteratedFDeriv ℝ k
        (fun b ↦ parameterCarrierFactor ψ ρ b x y •
          complementaryParameterFamily A q ζ ρ b x y η) c v =
      parameterCarrierFactor ψ ρ c x y • complementaryCarrierJet A q ζ ψ ρ k v c x y η := by
  have he : (fun b ↦ parameterCarrierFactor ψ ρ b x y •
        complementaryParameterFamily A q ζ ρ b x y η) =
      fun b ↦ complementaryCarrierCoefficient q ζ ψ ρ b x y η • A x y η := by
    funext b
    simp only [complementaryParameterFamily, complementaryAmplitude,
      complementaryCarrierCoefficient, normalizedCarrierOffset, smul_smul]
  rw [he, iteratedFDeriv_smul_const_apply h]
  change (iteratedFDeriv ℝ k
    (fun b ↦ complementaryCarrierCoefficient q ζ ψ ρ b x y η) c v) • A x y η = _
  simp only [complementaryCarrierJet, smul_smul, ← mul_assoc]
  rw [mul_comm (parameterCarrierFactor ψ ρ c x y), parameterCarrierFactor_neg_mul,
    one_mul]

/-- The carrier chain rule contributes precisely one physical frequency.
This is the first step in the fixed polynomial loss for every finite order
(`app:ch_response:thm:response-literal-transfer`). -/
theorem hasLineDerivAt_parameterCarrierFactor (ψ : P → E → E → ℝ)
    (ρ : ℝ) {c : P} (x y : E)
    (hψ : DifferentiableAt ℝ (fun b ↦ ψ b x y) c) (v : P) :
    HasLineDerivAt ℝ (fun b ↦ parameterCarrierFactor ψ ρ b x y)
      ((Complex.I * ((ρ * fderiv ℝ (fun b ↦ ψ b x y) c v : ℝ) : ℂ)) *
        parameterCarrierFactor ψ ρ c x y) c v := by
  have h := (((Complex.ofRealCLM.hasFDerivAt.comp c
    (hψ.hasFDerivAt.const_mul ρ)).const_mul Complex.I).cexp).hasLineDerivAt v
  simpa [parameterCarrierFactor, mul_comm] using h

/-- Actual first derivative of the complete scalar coefficient: both the
carrier term and moving-selector term are retained with their exact signs.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem hasLineDerivAt_complementaryCarrierCoefficient
    (q : E → ℂ) (ζ : P → E) (ψ : P → E → E → ℝ)
    {ρ : ℝ} (hρ : ρ ≠ 0) {c : P} (hζ : DifferentiableAt ℝ ζ c)
    (x y η : E) (hq : DifferentiableAt ℝ q (normalizedCarrierOffset ζ ρ η c))
    (hψ : DifferentiableAt ℝ (fun b ↦ ψ b x y) c) (v : P) :
    HasLineDerivAt ℝ (fun b ↦ complementaryCarrierCoefficient q ζ ψ ρ b x y η)
      (parameterCarrierFactor ψ ρ c x y *
        ((Complex.I * ((ρ * fderiv ℝ (fun b ↦ ψ b x y) c v : ℝ) : ℂ)) *
            (1 - q (normalizedCarrierOffset ζ ρ η c)) +
          fderiv ℝ q (normalizedCarrierOffset ζ ρ η c) (fderiv ℝ ζ c v))) c v := by
  have hd := ((hq.hasFDerivAt.comp c
    (hasFDerivAt_normalizedCarrierOffset ζ hρ η hζ)).const_sub 1).hasLineDerivAt v
  have h := HasDerivAt.mul (hasLineDerivAt_parameterCarrierFactor ψ ρ x y hψ v) hd
  simp only [neg_apply, ContinuousLinearMap.comp_apply,
    map_neg, neg_neg, zero_smul, add_zero, Function.comp_apply] at h
  change HasLineDerivAt ℝ (fun b ↦ complementaryCarrierCoefficient q ζ ψ ρ b x y η)
    ((Complex.I * ((ρ * fderiv ℝ (fun b ↦ ψ b x y) c v : ℝ) : ℂ)) *
        parameterCarrierFactor ψ ρ c x y * (1 - q (normalizedCarrierOffset ζ ρ η c)) +
      parameterCarrierFactor ψ ρ c x y *
        fderiv ℝ q (normalizedCarrierOffset ζ ρ η c) (fderiv ℝ ζ c v)) c v at h
  convert h using 1
  ring

/-- Every actual carrier/selector jet preserves all zeros of the original
full amplitude. In particular the weighted reverse specialization keeps
`j_S U⁻¹` and both physical cutoff positions.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem complementaryCarrierJet_eq_zero_of_amplitude_eq_zero
    (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E)
    (ψ : P → E → E → ℝ) (ρ : ℝ) (k : ℕ) (v : Fin k → P) (c : P)
    (x y η : E) (hA : A x y η = 0) :
    complementaryCarrierJet A q ζ ψ ρ k v c x y η = 0 := by
  simp [complementaryCarrierJet, hA]

/-- The entire carrier-weighted jet vanishes on the original selector plateau,
at arbitrary parameter order. No regularity of the carrier phase is needed
for this support fact (`app:ch_response:thm:response-literal-transfer`). -/
theorem complementaryCarrierJet_eq_zero_of_near
    (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E)
    (ψ : P → E → E → ℝ) (ρ : ℝ)
    {g : ℝ} (hq : ∀ δ, ‖δ‖ < g → q δ = 1)
    {c : P} (hζ : ContinuousAt ζ c) (k : ℕ) (v : Fin k → P)
    (x y η : E) (hη : ‖normalizedCarrierOffset ζ ρ η c‖ < g) :
    complementaryCarrierJet A q ζ ψ ρ k v c x y η = 0 := by
  have hc : ContinuousAt (fun b ↦ ‖normalizedCarrierOffset ζ ρ η b‖) c := by
    unfold normalizedCarrierOffset
    fun_prop
  have he : (fun b ↦ complementaryCarrierCoefficient q ζ ψ ρ b x y η) =ᶠ[𝓝 c]
      fun _ ↦ (0 : ℂ) := by
    filter_upwards [hc.eventually (gt_mem_nhds hη)] with b hb
    simp only [complementaryCarrierCoefficient, hq _ hb, sub_self, mul_zero]
  have hj := (he.iteratedFDeriv ℝ k).eq_of_nhds
  simp [complementaryCarrierJet, hj]

/-- The complete closed source gap survives every carrier/selector jet,
including all radial and angular shoulders.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem tsupport_complementaryCarrierJet_subset_far
    (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E)
    (ψ : P → E → E → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    {g : ℝ} (hq : ∀ δ, ‖δ‖ < g → q δ = 1)
    {c : P} (hζ : ContinuousAt ζ c) (k : ℕ) (v : Fin k → P) (x y : E) :
    tsupport (fun η ↦ complementaryCarrierJet A q ζ ψ ρ k v c x y η) ⊆
      {η | g * ρ ≤ ‖η - ρ • ζ c‖} := by
  apply closure_minimal ?_ (isClosed_le continuous_const (by fun_prop))
  intro η hη
  by_contra hn
  apply hη
  apply complementaryCarrierJet_eq_zero_of_near A q ζ ψ ρ hq hζ k v x y η
  rw [normalizedCarrierOffset, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
  exact (inv_mul_lt_iff₀ hρ).2 (by simpa only [mul_comm] using lt_of_not_ge hn)

/-- Exact auxiliary-selector identity for the carrier-weighted derivative
amplitude consumed by `forwardCompleteComplement_rapidDecay` and
`reverseCompleteComplement_rapidDecay`. There is no mask division.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem complementaryAmplitude_complementaryCarrierJet
    (A : FullAmplitude n r) (q qsmall : E → ℂ) (ζ : P → E)
    (ψ : P → E → E → ℝ) (ρ : ℝ)
    {g : ℝ} (hq : ∀ δ, ‖δ‖ < g → q δ = 1)
    (hsmall : ∀ δ, qsmall δ ≠ 0 → ‖δ‖ < g)
    {c : P} (hζ : ContinuousAt ζ c) (k : ℕ) (v : Fin k → P) :
    complementaryAmplitude (complementaryCarrierJet A q ζ ψ ρ k v c)
        (ζ c) ρ (fun δ ↦ qsmall (ρ⁻¹ • δ)) =
      complementaryCarrierJet A q ζ ψ ρ k v c := by
  funext x y η
  by_cases hqzero : qsmall (normalizedCarrierOffset ζ ρ η c) = 0
  · simp [complementaryAmplitude, normalizedCarrierOffset] at hqzero ⊢
    rw [hqzero, sub_zero, one_smul]
  · have hz := complementaryCarrierJet_eq_zero_of_near A q ζ ψ ρ hq hζ k v x y η
      (hsmall _ hqzero)
    simp [complementaryAmplitude, hz]

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
