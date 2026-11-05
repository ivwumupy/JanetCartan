module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.NormalizedTransfer.Scaling
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.NormalizedTransfer.SpatialAssembly
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.Assembly

/-!
# Physical recovery and freezing of joint parameter amplitudes

The parameter frequency is fixed. Normalization changes only `δ = ρ ε`;
the open parameter neighborhood, both physical supports, and the original
selector support remain. These results feed the parameter realization and the
frozen low symbol budget in `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.NormalizedTransfer
open FourierIntegral FullAmplitudePrimitiveBudget.Local
open IsometricEmbedding.Response.NearCarrier NearCarrierParameter
variable {n p : ℕ} {ι : Type*}
local notation "E" => Euclidean n
local notation "P" => Euclidean p
local notation "Z" => JointAmplitudePoint n p

/-- Local parameter smoothness is retained by physical recovery at fixed
frequency (`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiffOn_physicalField_parameter (ρ : ℝ) {U : Set P} {b : Z → ℂ}
    (hb : ContDiffOn ℝ ∞ b ((U ×ˢ univ) ×ˢ univ)) :
    ContDiffOn ℝ ∞ (physicalField ρ b) ((U ×ˢ univ) ×ˢ univ) :=
  hb.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ⁻¹)).contDiffOn
    (fun _ hz ↦ ⟨hz.1, mem_univ _⟩)

/-- The original parameter amplitude's support implies physical admissibility;
support preservation is proved rather than included as a transfer input.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem admissible_physicalField_parameter {ρ : ℝ} (hρ : ρ ≠ 0)
    {U : Set P} {X Y F : Set E} {b : Z → ℂ}
    (hb : ParameterAmplitudeAdmissible U X Y F b) :
    ParameterAmplitudeAdmissible U X Y ((fun ε ↦ ρ • ε) '' F) (physicalField ρ b) := by
  refine ⟨contDiffOn_physicalField_parameter ρ hb.1, ?_, ?_⟩
  · intro c hc δ hδ
    obtain ⟨ε, hε, rfl⟩ := hδ
    simpa only [physicalField, smul_smul, inv_mul_cancel₀ hρ, one_smul] using
      hb.2.1 c hc ε hε
  · intro c hc z δ hδ
    apply hb.2.2 c hc z (ρ⁻¹ • δ)
    intro hε
    exact hδ ⟨ρ⁻¹ • δ, hε, by simp [smul_smul, hρ]⟩

/-- Freeze only the parameter in the normalized joint field; both positions
and the normalized covector remain (`app:ch_response:eq:direct-envelope-profile`). -/
def frozenField (c : P) (b : Z → ℂ) : Point n → ℂ :=
  fun z ↦ b ((c, z.1), z.2)

/-- Frozen normalized amplitudes are globally smooth in the full spatial and
covector variables, from local parameter smoothness. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiff_frozenField {U : Set P} {b : Z → ℂ}
    (hb : ContDiffOn ℝ ∞ b ((U ×ˢ univ) ×ˢ univ)) {c : P} (hc : c ∈ U) :
    ContDiff ℝ ∞ (frozenField c b) :=
  contDiffOn_univ.mp (hb.comp
    ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd).contDiffOn
    (fun _ _ ↦ ⟨⟨hc, mem_univ _⟩, mem_univ _⟩))

/-- Freezing a parameter slice retains the original compact supports, closing
the support input to the spatial and low-symbol leaves.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem supportedAmplitude_frozenField {U : Set P} {X Y F : Set E}
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {b : Z → ℂ} (hb : ParameterAmplitudeAdmissible U X Y F b)
    {c : P} (hc : c ∈ U) :
    SupportedAmplitude ((X ×ˢ Y) ×ˢ F) (frozenField c b) := by
  apply supportedAmplitude_of_masks hX hY hF (contDiff_frozenField hb.1 hc)
  intro x y ε h
  by_cases hε : ε ∈ F
  · apply image_eq_zero_of_notMem_tsupport (f := fun z : E × E ↦ b ((c, z), ε))
    intro hz
    have hs := hb.2.1 c hc ε hε hz
    rcases h with h | h | h
    · exact h hs.1
    · exact h hs.2
    · exact h hε
  · exact hb.2.2 c hc (x, y) ε hε

/-- Freezing and physical recovery commute exactly, without rescaling either
physical position (`app:ch_response:eq:direct-envelope-profile`). -/
theorem frozenField_physicalField (ρ : ℝ) (c : P) (b : Z → ℂ) :
    frozenField c (physicalField ρ b) = physicalField ρ (frozenField c b) := rfl

/-- Compatibility with the existing Fourier normalization used by the
parameter literal kernel. No extra normalization is inserted by displacement
recovery. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem normalizedScalarAmplitude_frozenField (ρ : ℝ) (c : P) (b : Z → ℂ)
    (z : E × E) (δ : E) :
    normalizedScalarAmplitude (scalarPhysicalAmplitude ρ (frozenField c b)) z δ =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ * physicalField ρ b ((c, z), δ) := by
  simp only [normalizedScalarAmplitude, scalarPhysicalAmplitude_apply,
    physicalField, frozenField]

/-- Physical recovery of the normalized parameter remainder is the complete
parameter derivative plus physical source divergences. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_parameterSourceTerms_slice {ρ : ℝ} (hρ : ρ ≠ 0)
    {U : Set P} (hU : IsOpen U) {X Y F : Set E}
    (a : ι → Z → ℂ) (b : AmplitudeExpression Z ℂ ι) (v : P) (idx : Fin n → ι)
    (hb : ParameterAmplitudeAdmissible U X Y F (b.evaluate a))
    (ha : ∀ j, ContDiffOn ℝ ∞ (a (idx j)) ((U ×ˢ univ) ×ˢ univ))
    {c : P} (hc : c ∈ U) (z : E × E) (δ : E) :
    physicalField ρ
        ((b.divergenceTransfer (parameterAmplitudeDirection v) (parameterSourceTerms idx)).evaluate a)
        ((c, z), δ) =
      fderiv ℝ (fun t ↦ physicalField ρ (b.evaluate a) ((t, z), δ)) c v +
        ∑ j, fderiv ℝ (fun y ↦ physicalField ρ (a (idx j)) ((c, (z.1, y)), δ) *
          physicalField ρ (b.evaluate a) ((c, (z.1, y)), δ)) z.2 (EuclideanSpace.single j 1) := by
  have h := evaluate_parameterSourceTerms_slice hU
    (fun i ↦ physicalField ρ (a i)) (physicalExpression ρ b) v idx
    (by rw [evaluate_physicalExpression hρ]; exact admissible_physicalField_parameter hρ hb)
    (fun j ↦ contDiffOn_physicalField_parameter ρ (ha j)) hc z δ
  rw [← physicalExpression_parameterSourceTerms, evaluate_physicalExpression hρ,
    evaluate_physicalExpression hρ] at h
  exact h

/-- Datum expression recovery is the full signed physical product, for both
the coefficient `C` and the coefficient `-C B⁻¹`.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem physical_parameterDatum (ρ : ℝ) (a : ι → Z → ℂ)
    (b : AmplitudeExpression Z ℂ ι) (i : ι) :
    physicalField ρ ((b.coefficientProduct (ContinuousLinearMap.mul ℝ ℂ) i).evaluate a) =
      fun z ↦ physicalField ρ (a i) z * physicalField ρ (b.evaluate a) z := rfl

end JanetCartan.ResponseTransfer.NormalizedTransfer
