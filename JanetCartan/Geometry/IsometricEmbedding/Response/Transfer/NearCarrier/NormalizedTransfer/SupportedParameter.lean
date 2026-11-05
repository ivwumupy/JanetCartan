module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.NormalizedTransfer.JointSpatial

/-!
# Parameter amplitudes with buffered coefficient agreement

The normalized expressions recover the already defined datum and remainder
amplitudes globally, including outside the complete original joint support. The
coefficient equality is used only after multiplication by the original
supported amplitude. Source: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.NormalizedTransfer
open IsometricEmbedding.Response.NearCarrier NearCarrierParameter
variable {n p : ℕ} {ι : Type*}
local notation "E" => Euclidean n
local notation "P" => Euclidean p
local notation "Z" => JointAmplitudePoint n p

/-- Coefficient agreement on the complete original joint support identifies the
full product everywhere, by the original amplitude support. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_parameterProduct_supported {ρ : ℝ} (hρ : ρ ≠ 0)
    {U : Set P} {X Y F : Set E} {K : Set Z} (a : ι → Z → ℂ)
    (b : AmplitudeExpression Z ℂ ι)
    (hb : SupportedJointAmplitude U X Y F K (b.evaluate a))
    (i : ι) (Q : P → E × E → E → ℂ)
    (hq : ∀ z ∈ K, a i z = Q z.1.1 z.1.2 (ρ • z.2))
    (c : P) (z : E × E) (δ : E) :
    physicalField ρ (a i) ((c, z), δ) * physicalField ρ (b.evaluate a) ((c, z), δ) =
      Q c z δ * physicalField ρ (b.evaluate a) ((c, z), δ) := by
  by_cases hz : ((c, z), ρ⁻¹ • δ) ∈ tsupport (b.evaluate a)
  · change a i ((c, z), ρ⁻¹ • δ) * _ = _
    rw [hq _ (hb.2 hz)]
    simp only [smul_smul, mul_inv_cancel₀ hρ, one_smul]
  · simp only [physicalField, image_eq_zero_of_notMem_tsupport hz, mul_zero]

/-- The recovered forward datum expression is the actual coefficient `C`
times the entire amplitude, including every mask. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_forwardParameterDatum_supported {ρ : ℝ} (hρ : ρ ≠ 0)
    {U : Set P} {X Y F : Set E} {K : Set Z} (a : ι → Z → ℂ)
    (b : AmplitudeExpression Z ℂ ι)
    (hb : SupportedJointAmplitude U X Y F K (b.evaluate a))
    (S : E → E → ℝ) (ζ : P → E) (v : P) (idx : Fin n → ι)
    (hC : ∀ j z, z ∈ K →
      a (idx j) z = (phaseCoefficient S ζ ρ z.1.1 v z.1.2.1 (ρ • z.2) j : ℂ))
    (c : P) (j : Fin n) (z : E × E) (δ : E) :
    physicalField ρ ((b.coefficientProduct (ContinuousLinearMap.mul ℝ ℂ) (idx j)).evaluate a)
        ((c, z), δ) =
      forwardParameterDatum S ζ ρ (fun t z δ ↦ physicalField ρ (b.evaluate a) ((t, z), δ))
        c v j z δ :=
  physical_parameterProduct_supported hρ a b hb (idx j)
    (fun c z δ ↦ (phaseCoefficient S ζ ρ c v z.1 δ j : ℂ)) (hC j) c z δ

/-- The recovered reverse datum expression is the full signed `-C B⁻¹`
product. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_reverseParameterDatum_supported {ρ : ℝ} (hρ : ρ ≠ 0)
    {U : Set P} {X Y F : Set E} {K : Set Z} (a : ι → Z → ℂ)
    (b : AmplitudeExpression Z ℂ ι)
    (hb : SupportedJointAmplitude U X Y F K (b.evaluate a))
    (S : E → E → ℝ) (ζ : P → E) (J : P → E → E → Matrix (Fin n) (Fin n) ℝ)
    (v : P) (idx : Fin n → ι)
    (hC : ∀ j z, z ∈ K →
      a (idx j) z = reverseParameterRow S ζ ρ (J z.1.1) z.1.1 v z.1.2.2 (ρ • z.2) j)
    (c : P) (j : Fin n) (z : E × E) (δ : E) :
    physicalField ρ ((b.coefficientProduct (ContinuousLinearMap.mul ℝ ℂ) (idx j)).evaluate a)
        ((c, z), δ) =
      reverseParameterDatum S ζ ρ (J c)
        (fun t z δ ↦ physicalField ρ (b.evaluate a) ((t, z), δ)) c v j z δ :=
  physical_parameterProduct_supported hρ a b hb (idx j)
    (fun c z δ ↦ reverseParameterRow S ζ ρ (J c) c v z.2 δ j) (hC j) c z δ

/-- The forward recovered remainder is the literal parameter derivative plus
`C` times source derivatives of the whole amplitude. Frequency and the fixed
operator are not differentiated. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_forwardParameterRemainder_supported {ρ : ℝ} (hρ : ρ ≠ 0)
    {U : Set P} (hU : IsOpen U) {X Y F : Set E} {K : Set Z} (a : ι → Z → ℂ)
    (b : AmplitudeExpression Z ℂ ι)
    (hb : SupportedJointAmplitude U X Y F K (b.evaluate a))
    (S : E → E → ℝ) (ζ : P → E) (v : P) (idx : Fin n → ι)
    (ha : ∀ j, ContDiffOn ℝ ∞ (a (idx j)) ((U ×ˢ univ) ×ˢ univ))
    (hC : ∀ j z, z ∈ K →
      a (idx j) z = (phaseCoefficient S ζ ρ z.1.1 v z.1.2.1 (ρ • z.2) j : ℂ))
    {c : P} (hc : c ∈ U) (z : E × E) (δ : E) :
    physicalField ρ
        ((b.divergenceTransfer (parameterAmplitudeDirection v) (parameterSourceTerms idx)).evaluate a)
        ((c, z), δ) =
      forwardParameterRemainder S ζ ρ
        (fun t z δ ↦ physicalField ρ (b.evaluate a) ((t, z), δ)) c v z δ := by
  rw [physical_parameterSourceTerms_slice hρ hU a b v idx hb.1 ha hc]
  unfold forwardParameterRemainder
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he := funext fun y ↦ physical_parameterProduct_supported hρ a b hb (idx j)
    (fun c z δ ↦ (phaseCoefficient S ζ ρ c v z.1 δ j : ℂ)) (hC j) c (z.1, y) δ
  rw [he]
  have hd : DifferentiableAt ℝ (fun y ↦ physicalField ρ (b.evaluate a) ((c, (z.1, y)), δ)) z.2 :=
    (hb.1.differentiableAt hU hc z (ρ⁻¹ • δ)).comp z.2
      (((differentiableAt_const c).prodMk
        ((differentiableAt_const z.1).prodMk differentiableAt_id)).prodMk (differentiableAt_const (ρ⁻¹ • δ)))
  exact congrArg (fun L : E →L[ℝ] ℂ ↦ L (EuclideanSpace.single j 1))
    (fderiv_const_mul hd (phaseCoefficient S ζ ρ c v z.1 δ j : ℂ))

/-- The reverse recovered remainder is the literal parameter derivative plus
the derivative of the full signed datum product. Inverse-coefficient and mask
derivatives are retained even on closed support shoulders.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_reverseParameterRemainder_supported {ρ : ℝ} (hρ : ρ ≠ 0)
    {U : Set P} (hU : IsOpen U) {X Y F : Set E} {K : Set Z} (a : ι → Z → ℂ)
    (b : AmplitudeExpression Z ℂ ι)
    (hb : SupportedJointAmplitude U X Y F K (b.evaluate a))
    (S : E → E → ℝ) (ζ : P → E) (J : P → E → E → Matrix (Fin n) (Fin n) ℝ)
    (v : P) (idx : Fin n → ι)
    (ha : ∀ j, ContDiffOn ℝ ∞ (a (idx j)) ((U ×ˢ univ) ×ˢ univ))
    (hC : ∀ j z, z ∈ K →
      a (idx j) z = reverseParameterRow S ζ ρ (J z.1.1) z.1.1 v z.1.2.2 (ρ • z.2) j)
    {c : P} (hc : c ∈ U) (z : E × E) (δ : E) :
    physicalField ρ
        ((b.divergenceTransfer (parameterAmplitudeDirection v) (parameterSourceTerms idx)).evaluate a)
        ((c, z), δ) =
      reverseParameterRemainder S ζ ρ (J c)
        (fun t z δ ↦ physicalField ρ (b.evaluate a) ((t, z), δ)) c v z δ := by
  rw [physical_parameterSourceTerms_slice hρ hU a b v idx hb.1 ha hc]
  unfold reverseParameterRemainder
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he := funext fun y ↦ physical_reverseParameterDatum_supported hρ a b hb S ζ J v idx hC c j (z.1, y) δ
  change fderiv ℝ (fun y ↦ physicalField ρ
      ((b.coefficientProduct (ContinuousLinearMap.mul ℝ ℂ) (idx j)).evaluate a)
      ((c, (z.1, y)), δ)) z.2 _ = _
  rw [he]

end JanetCartan.ResponseTransfer.NormalizedTransfer
