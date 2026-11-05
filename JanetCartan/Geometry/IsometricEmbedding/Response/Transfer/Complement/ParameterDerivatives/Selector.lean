module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# The moving complementary selector at fixed physical frequency

The parameter-complement paragraph of
`app:ch_response:thm:response-literal-transfer`. The physical integration variable
`η`, frequency `ρ`, and full amplitude are fixed while the carrier varies.
Consequently the selector is differentiated at `η / ρ - ζ(c)`. Every parameter
jet retains the full complementary gap and the original amplitude support.
The auxiliary-selector identity below multiplies by a smaller complementary
mask; it neither divides by a mask nor projects the source datum.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives

open FourierIntegral

variable {n r : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n

/-- The normalized selector argument at fixed physical covector in
`app:ch_response:thm:response-literal-transfer`. -/
def normalizedCarrierOffset (ζ : P → E) (ρ : ℝ) (η : E) (c : P) : E :=
  ρ⁻¹ • (η - ρ • ζ c)

/-- The complete original amplitude with its moving normalized selector,
including every physical, radial, and angular cutoff
(`app:ch_response:thm:response-literal-transfer`). -/
def complementaryParameterFamily (A : FullAmplitude n r) (q : E → ℂ)
    (ζ : P → E) (ρ : ℝ) (c : P) : FullAmplitude n r :=
  complementaryAmplitude A (ζ c) ρ (fun δ ↦ q (ρ⁻¹ • δ))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Frequency cancellation in the moving selector: its parameter chain rule
has no positive frequency cost (`app:ch_response:thm:response-literal-transfer`). -/
theorem normalizedCarrierOffset_eq (ζ : P → E) {ρ : ℝ} (hρ : ρ ≠ 0)
    (η : E) (c : P) :
    normalizedCarrierOffset ζ ρ η c = ρ⁻¹ • η - ζ c := by
  simp [normalizedCarrierOffset, smul_sub, smul_smul, hρ]

/-- Exact Fréchet derivative of the moving selector argument, with frequency
and physical covector fixed (`app:ch_response:thm:response-literal-transfer`). -/
theorem hasFDerivAt_normalizedCarrierOffset (ζ : P → E) {ρ : ℝ} (hρ : ρ ≠ 0)
    (η : E) {c : P} (hζ : DifferentiableAt ℝ ζ c) :
    HasFDerivAt (normalizedCarrierOffset ζ ρ η) (-fderiv ℝ ζ c) c := by
  change HasFDerivAt (fun b ↦ normalizedCarrierOffset ζ ρ η b) _ c
  simpa only [normalizedCarrierOffset_eq ζ hρ] using
    hζ.hasFDerivAt.const_sub (ρ⁻¹ • η)

/-- At every positive order the normalized selector argument has exactly the
negative carrier jet. Thus no positive frequency power is hidden in its
chain rule (`app:ch_response:thm:response-literal-transfer`). -/
theorem iteratedFDeriv_normalizedCarrierOffset
    (ζ : P → E) {ρ : ℝ} (hρ : ρ ≠ 0) (η : E) {c : P} {k : ℕ}
    (hk : k ≠ 0) (hζ : ContDiffAt ℝ k ζ c) :
    iteratedFDeriv ℝ k (normalizedCarrierOffset ζ ρ η) c = -iteratedFDeriv ℝ k ζ c := by
  have he : normalizedCarrierOffset ζ ρ η = fun b ↦ ρ⁻¹ • η - ζ b :=
    funext (normalizedCarrierOffset_eq ζ hρ η)
  rw [he]
  change iteratedFDeriv ℝ k ((fun _ : P ↦ ρ⁻¹ • η) - ζ) c = _
  rw [iteratedFDeriv_sub_apply contDiffAt_const hζ, iteratedFDeriv_const_of_ne hk]
  simp

/-- The actual derivative of the complete amplitude contains the selector
derivative. The two minus signs cancel, and no derivative of the fixed full
amplitude or integration variable is taken.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem hasLineDerivAt_complementaryParameterFamily
    (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E)
    {ρ : ℝ} (hρ : ρ ≠ 0) {c : P} (hζ : DifferentiableAt ℝ ζ c)
    (x y η : E) (hq : DifferentiableAt ℝ q (normalizedCarrierOffset ζ ρ η c))
    (v : P) :
    HasLineDerivAt ℝ (fun b ↦ complementaryParameterFamily A q ζ ρ b x y η)
      (fderiv ℝ q (normalizedCarrierOffset ζ ρ η c) (fderiv ℝ ζ c v) • A x y η)
      c v := by
  have hd := hq.hasFDerivAt.comp c (hasFDerivAt_normalizedCarrierOffset ζ hρ η hζ)
  have h := ((hd.const_sub 1).smul_const (A x y η)).hasLineDerivAt v
  simpa [complementaryParameterFamily, complementaryAmplitude,
    normalizedCarrierOffset] using h

/-- Every actual parameter jet of the complete amplitude, evaluated on the
specified directions (`app:ch_response:thm:response-literal-transfer`). -/
def complementaryParameterJet (A : FullAmplitude n r) (q : E → ℂ)
    (ζ : P → E) (ρ : ℝ) (k : ℕ) (v : Fin k → P) (c : P) : FullAmplitude n r :=
  fun x y η ↦ iteratedFDeriv ℝ k
    (fun b ↦ complementaryParameterFamily A q ζ ρ b x y η) c v

/-- All parameter jets vanish on the original open near-carrier plateau.
Continuity of the carrier suffices for this support assertion, at every order;
no derivative expansion or complementary estimate is assumed.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem complementaryParameterJet_eq_zero_of_near
    (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E) (ρ : ℝ)
    {g : ℝ} (hq : ∀ δ, ‖δ‖ < g → q δ = 1)
    {c : P} (hζ : ContinuousAt ζ c) (k : ℕ) (v : Fin k → P)
    (x y η : E) (hη : ‖normalizedCarrierOffset ζ ρ η c‖ < g) :
    complementaryParameterJet A q ζ ρ k v c x y η = 0 := by
  have hc : ContinuousAt (fun b ↦ ‖normalizedCarrierOffset ζ ρ η b‖) c := by
    unfold normalizedCarrierOffset
    fun_prop
  have he : (fun b ↦ complementaryParameterFamily A q ζ ρ b x y η) =ᶠ[𝓝 c]
      fun _ ↦ (0 : Matrix (Fin r) (Fin r) ℂ) := by
    filter_upwards [hc.eventually (gt_mem_nhds hη)] with b hb
    change (1 - q (normalizedCarrierOffset ζ ρ η b)) • A x y η = 0
    rw [hq _ hb, sub_self, zero_smul]
  have hj := (he.iteratedFDeriv ℝ k).eq_of_nhds
  simp [complementaryParameterJet, hj]

/-- Parameter jets preserve all original amplitude zeros, including both
physical supports and every radial or angular shoulder.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem complementaryParameterJet_eq_zero_of_amplitude_eq_zero
    (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E) (ρ : ℝ)
    (k : ℕ) (v : Fin k → P) (c : P) (x y η : E) (hA : A x y η = 0) :
    complementaryParameterJet A q ζ ρ k v c x y η = 0 := by
  simp [complementaryParameterJet, complementaryParameterFamily, complementaryAmplitude, hA]

/-- The closed physical-frequency source gap of every actual parameter jet.
This covers the closure of the support, not just nonzero points.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem tsupport_complementaryParameterJet_subset_far
    (A : FullAmplitude n r) (q : E → ℂ) (ζ : P → E) {ρ : ℝ} (hρ : 0 < ρ)
    {g : ℝ} (hq : ∀ δ, ‖δ‖ < g → q δ = 1)
    {c : P} (hζ : ContinuousAt ζ c) (k : ℕ) (v : Fin k → P) (x y : E) :
    tsupport (fun η ↦ complementaryParameterJet A q ζ ρ k v c x y η) ⊆
      {η | g * ρ ≤ ‖η - ρ • ζ c‖} := by
  apply closure_minimal ?_ (isClosed_le continuous_const (by fun_prop))
  intro η hη
  by_contra hn
  apply hη
  apply complementaryParameterJet_eq_zero_of_near A q ζ ρ hq hζ k v x y η
  rw [normalizedCarrierOffset, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
  exact (inv_mul_lt_iff₀ hρ).2 (by simpa only [mul_comm] using lt_of_not_ge hn)

/-- A smaller auxiliary selector expresses every actual derivative amplitude
in the existing `complementaryAmplitude` form, exactly. No complementary mask
is inverted and no envelope is projected.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem complementaryAmplitude_complementaryParameterJet
    (A : FullAmplitude n r) (q qsmall : E → ℂ) (ζ : P → E) (ρ : ℝ)
    {g : ℝ} (hq : ∀ δ, ‖δ‖ < g → q δ = 1)
    (hsmall : ∀ δ, qsmall δ ≠ 0 → ‖δ‖ < g)
    {c : P} (hζ : ContinuousAt ζ c) (k : ℕ) (v : Fin k → P) :
    complementaryAmplitude (complementaryParameterJet A q ζ ρ k v c)
        (ζ c) ρ (fun δ ↦ qsmall (ρ⁻¹ • δ)) =
      complementaryParameterJet A q ζ ρ k v c := by
  funext x y η
  by_cases hqzero : qsmall (normalizedCarrierOffset ζ ρ η c) = 0
  · simp [complementaryAmplitude, normalizedCarrierOffset] at hqzero ⊢
    rw [hqzero, sub_zero, one_smul]
  · have hz := complementaryParameterJet_eq_zero_of_near A q ζ ρ hq hζ k v x y η
      (hsmall _ hqzero)
    simp [complementaryAmplitude, hz]

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
