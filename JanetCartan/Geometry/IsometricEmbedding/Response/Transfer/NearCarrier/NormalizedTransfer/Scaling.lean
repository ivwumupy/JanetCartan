module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.NormalizedTransfer.Basic

/-!
# Frequency normalization of literal amplitude expressions

Only displacement is rescaled. The first factor below is either the pair of
physical positions or the parameter together with those positions. This is
the chain rule needed to use the same expressions in the spatial/parameter
realizations and the low normalized symbol budget of
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.NormalizedTransfer
open IsometricEmbedding.Response.NearCarrier NearCarrierParameter
variable {n : ℕ} {ι W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
local notation "E" => Euclidean n

/-- Recover physical displacement while retaining all physical and parameter
spectators. Source: `app:ch_response:eq:direct-envelope-profile`. -/
def physicalField (ρ : ℝ) (b : W × E → ℂ) : W × E → ℂ :=
  fun z ↦ b (z.1, ρ⁻¹ • z.2)

/-- Displacement recovery is a continuous linear equivalence for nonzero
frequency (`app:ch_response:eq:direct-envelope-profile`). -/
def displacementEquiv (ρ : ℝ) (hρ : ρ ≠ 0) : (W × E) ≃L[ℝ] (W × E) where
  toFun z := (z.1, ρ⁻¹ • z.2)
  invFun z := (z.1, ρ • z.2)
  left_inv z := by simp [smul_smul, hρ]
  right_inv z := by simp [smul_smul, hρ]
  map_add' z w := by simp [smul_add]
  map_smul' c z := by simp [smul_smul, mul_comm]
  continuous_toFun := continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.const_smul ρ)

/-- A normalized direction becomes a physical direction with only its last
component multiplied by frequency. Consumer: normalized low symbol jets in
`app:ch_response:eq:direct-envelope-profile`. -/
def physicalDirection (ρ : ℝ) (v : W × E) : W × E := (v.1, ρ • v.2)

/-- Exact normalized chain rule, including directions with a covector
component. No smoothness is needed for this equivalence identity.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem physicalField_fderiv {ρ : ℝ} (hρ : ρ ≠ 0)
    (b : W × E → ℂ) (v z : W × E) :
    physicalField ρ (fun w ↦ fderiv ℝ b w v) z =
      fderiv ℝ (physicalField ρ b) z (physicalDirection ρ v) := by
  change fderiv ℝ b (z.1, ρ⁻¹ • z.2) v =
    fderiv ℝ (b ∘ displacementEquiv ρ hρ) z (physicalDirection ρ v)
  rw [ContinuousLinearEquiv.comp_right_fderiv]
  change fderiv ℝ b (z.1, ρ⁻¹ • z.2) v =
    fderiv ℝ b (z.1, ρ⁻¹ • z.2) (v.1, ρ⁻¹ • (ρ • v.2))
  simp [smul_smul, hρ]


/-- Transport every direction of an expression into physical displacement
coordinates. Its scalar primitives are recovered by `physicalField`.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
def physicalExpression (ρ : ℝ) :
    AmplitudeExpression (W × E) ℂ ι → AmplitudeExpression (W × E) ℂ ι
  | .primitive i => .primitive i
  | .add b c => .add (physicalExpression ρ b) (physicalExpression ρ c)
  | .bilinear M b c => .bilinear M (physicalExpression ρ b) (physicalExpression ρ c)
  | .deriv v b => .deriv (physicalDirection ρ v) (physicalExpression ρ b)

/-- Literal interpretation commutes with displacement normalization for
every expression, including arbitrary mixed derivatives. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem evaluate_physicalExpression {ρ : ℝ} (hρ : ρ ≠ 0)
    (a : ι → W × E → ℂ) (b : AmplitudeExpression (W × E) ℂ ι) :
    (physicalExpression ρ b).evaluate (fun i ↦ physicalField ρ (a i)) =
      physicalField ρ (b.evaluate a) := by
  induction b with
  | primitive i => rfl
  | add b c hb hc => simp only [physicalExpression, AmplitudeExpression.evaluate, hb, hc]; rfl
  | bilinear M b c hb hc =>
    simp only [physicalExpression, AmplitudeExpression.evaluate, hb, hc]; rfl
  | deriv v b hb =>
    simp only [physicalExpression, AmplitudeExpression.evaluate, hb]
    funext z
    exact (physicalField_fderiv hρ _ v z).symm

/-- Displacement normalization retains the derivative count; it changes only
the directions used for literal evaluation. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
@[simp] theorem derivativeCost_physicalExpression (ρ : ℝ)
    (b : AmplitudeExpression (W × E) ℂ ι) :
    (physicalExpression ρ b).derivativeCost = b.derivativeCost := by
  induction b <;> simp_all [physicalExpression, AmplitudeExpression.derivativeCost]

/-- Product branches commute with expression transport.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
@[simp] theorem physicalExpression_coefficientProduct (ρ : ℝ)
    (b : AmplitudeExpression (W × E) ℂ ι) (M : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (i : ι) :
    physicalExpression ρ (b.coefficientProduct M i) =
      (physicalExpression ρ b).coefficientProduct M i := rfl

/-- Divergence branches commute with transport of their entire direction
list (`app:ch_response:eq:direct-envelope-profile`). -/
theorem physicalExpression_divergenceTransfer (ρ : ℝ)
    (b : AmplitudeExpression (W × E) ℂ ι) (v : W × E)
    (qs : List ((W × E) × ι × (ℂ →L[ℝ] ℂ →L[ℝ] ℂ))) :
    physicalExpression ρ (b.divergenceTransfer v qs) =
      (physicalExpression ρ b).divergenceTransfer (physicalDirection ρ v)
        (qs.map fun q ↦ (physicalDirection ρ q.1, q.2)) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [AmplitudeExpression.divergenceTransfer, physicalExpression,
      physicalExpression_coefficientProduct, List.map_cons, ih]

/-- Smoothness in all spectator variables survives physical recovery.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiff_physicalField (ρ : ℝ) {b : W × E → ℂ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (physicalField ρ b) :=
  hb.comp (contDiff_fst.prodMk (contDiff_snd.const_smul _))

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The output and parameter spectators are fixed by physical recovery, so
their directions carry no power of frequency. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
@[simp] theorem physicalDirection_zero_frequency (ρ : ℝ) (v : W) :
    physicalDirection ρ (v, (0 : E)) = (v, 0) := by
  simp [physicalDirection]

section Parameter
variable {p : ℕ}
local notation "P" => Euclidean p
local notation "Z" => JointAmplitudePoint n p

/-- Parameter/source expression modifications commute with normalization
at fixed frequency. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem physicalExpression_parameterSourceTerms (ρ : ℝ)
    (b : AmplitudeExpression Z ℂ ι) (v : P) (idx : Fin n → ι) :
    physicalExpression ρ
        (b.divergenceTransfer (parameterAmplitudeDirection v) (parameterSourceTerms idx)) =
      (physicalExpression ρ b).divergenceTransfer
        (parameterAmplitudeDirection v) (parameterSourceTerms idx) := by
  rw [physicalExpression_divergenceTransfer]
  simp [parameterAmplitudeDirection, parameterSourceTerms, sourceAmplitudeDirection,
    List.map_ofFn, Function.comp_def, physicalDirection]

end Parameter
end JanetCartan.ResponseTransfer.NormalizedTransfer
