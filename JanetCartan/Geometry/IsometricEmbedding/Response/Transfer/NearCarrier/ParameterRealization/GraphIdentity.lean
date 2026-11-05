module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.Realizations

/-!
# Normalized scalar graph kernels

The scalar specialization and Fubini identification used by the parameter
realization of `app:ch_response:eq:direct-envelope-profile`. The physical
Fourier normalization is included exactly once. Both source and frequency
integrability follow from continuity and compact support.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.NearCarrierParameter
open FourierIntegral
variable {d p : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin p)

/-- The scalar entry of a full amplitude, including the physical Fourier
normalization of `app:ch_regular_base:eq:actual-normal-kernel`. -/
def normalizedScalarAmplitude (A : FullAmplitude d 1) (z : E × E) (δ : E) : ℂ :=
  ((2 * Real.pi) ^ d : ℂ)⁻¹ * A z.1 z.2 δ 0 0

/-- Fubini for the literal selected scalar kernel. This is the identification
needed to apply the compact-kernel derivative theorem to the original iterated
graph integral in `app:ch_response:eq:direct-envelope-profile`. -/
theorem integral_frequencyKernel_mul
    {Y F : Set E} (hY : IsCompact Y) (hF : IsCompact F)
    {k : E × E → E → ℂ} (hk : Continuous (Function.uncurry k))
    (hs : ∀ x y δ, y ∉ Y ∨ δ ∉ F → k (x, y) δ = 0)
    {g : E → ℂ} (hg : Continuous g) (x : E) :
    (∫ y, frequencyKernel F k (x, y) * g y) = ∫ δ, ∫ y, k (x, y) δ * g y := by
  have hi : Integrable (fun z : E × E ↦ k (x, z.1) z.2 * g z.1)
      (volume.prod volume) := by
    apply ((hk.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)).mul
      (hg.comp continuous_fst)).integrable_of_hasCompactSupport
    apply (hY.prod hF).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (hY.prod hF).isClosed
    intro z hz
    by_contra hn
    apply hz
    change k (x, z.1) z.2 * g z.1 = 0
    rw [hs x z.1 z.2 (by tauto), zero_mul]
  calc
    _ = ∫ y, ∫ δ, k (x, y) δ * g y := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change (∫ δ in F, k (x, y) δ) * g y = _
      rw [← integral_mul_const,
        setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro δ hδ
      rw [hs x y δ (Or.inr hδ), zero_mul]
    _ = _ := integral_integral_swap hi

private theorem integral_single_apply {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → Fin 1 → ℂ) : (∫ x, f x ∂μ) 0 = ∫ x, f x 0 ∂μ :=
  ((ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)).integral_comp_comm f).symm

/-- Scalar entry of the original normalized forward graph, without any
integrability assumption or change of measure. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem graphOperator_scalar_entry (Φ : E → E → ℝ) (A : FullAmplitude d 1)
    (g : E → ℂ) (x : E) :
    graphOperator Φ A (fun y _ ↦ g y) x 0 =
      ∫ δ, ∫ y, graphOscillation Φ x y δ * normalizedScalarAmplitude A (x, y) δ * g y := by
  simp only [graphOperator, Pi.smul_apply, smul_eq_mul, integral_single_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_one, normalizedScalarAmplitude]
  simp_rw [mul_left_comm (graphOscillation Φ x _ _), mul_assoc,
    integral_const_mul]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro δ
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ mul_left_comm _ _ _)

/-- Scalar entry of the reverse graph, with its opposite phase and unchanged
full inverse weight. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem envelopeGraph_scalar_entry (S : E → E → ℝ) (ζ : E) (ρ : ℝ)
    (A : FullAmplitude d 1) (g : E → ℂ) (x : E) :
    ReverseDerivative.envelopeGraph S ζ ρ A (fun y _ ↦ g y) x 0 =
      ∫ δ, ∫ y, ReverseDerivative.oscillation S ζ ρ x y δ *
        normalizedScalarAmplitude A (x, y) δ * g y := by
  simp only [ReverseDerivative.envelopeGraph, Pi.smul_apply, smul_eq_mul,
    integral_single_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
    normalizedScalarAmplitude]
  simp_rw [mul_left_comm (ReverseDerivative.oscillation S ζ ρ x _ _), mul_assoc,
    integral_const_mul]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro δ
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ mul_left_comm _ _ _)

/-- The compact frequency kernel is the existing normalized forward graph
on scalar tests, with the original frequency/source integration order.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem frequencyKernel_eq_graphOperator
    {Y F : Set E} (hY : IsCompact Y) (hF : IsCompact F)
    (Φ : E → E → ℝ) (A : FullAmplitude d 1)
    (hk : Continuous (fun z : (E × E) × E ↦
      graphOscillation Φ z.1.1 z.1.2 z.2 * normalizedScalarAmplitude A z.1 z.2))
    (hs : ∀ x y δ, y ∉ Y ∨ δ ∉ F → A x y δ = 0)
    {g : E → ℂ} (hg : Continuous g) (x : E) :
    (∫ y, frequencyKernel F (fun z δ ↦ graphOscillation Φ z.1 z.2 δ *
      normalizedScalarAmplitude A z δ) (x, y) * g y) =
      graphOperator Φ A (fun y _ ↦ g y) x 0 := by
  rw [integral_frequencyKernel_mul (k := fun z δ ↦
    graphOscillation Φ z.1 z.2 δ * normalizedScalarAmplitude A z δ) hY hF hk]
  · exact (graphOperator_scalar_entry Φ A g x).symm
  · intro x y δ h
    simp [normalizedScalarAmplitude, hs x y δ h]
  · exact hg

/-- The same Fubini identification for the existing normalized reverse graph.
It preserves the literal inverse weight and all cutoffs in `A`.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem frequencyKernel_eq_envelopeGraph
    {Y F : Set E} (hY : IsCompact Y) (hF : IsCompact F)
    (S : E → E → ℝ) (ζ : E) (ρ : ℝ) (A : FullAmplitude d 1)
    (hk : Continuous (fun z : (E × E) × E ↦
      ReverseDerivative.oscillation S ζ ρ z.1.1 z.1.2 z.2 * normalizedScalarAmplitude A z.1 z.2))
    (hs : ∀ x y δ, y ∉ Y ∨ δ ∉ F → A x y δ = 0)
    {g : E → ℂ} (hg : Continuous g) (x : E) :
    (∫ y, frequencyKernel F (fun z δ ↦ ReverseDerivative.oscillation S ζ ρ z.1 z.2 δ *
      normalizedScalarAmplitude A z δ) (x, y) * g y) =
      ReverseDerivative.envelopeGraph S ζ ρ A (fun y _ ↦ g y) x 0 := by
  rw [integral_frequencyKernel_mul (k := fun z δ ↦
    ReverseDerivative.oscillation S ζ ρ z.1 z.2 δ * normalizedScalarAmplitude A z δ) hY hF hk]
  · exact (envelopeGraph_scalar_entry S ζ ρ A g x).symm
  · intro x y δ h
    simp [normalizedScalarAmplitude, hs x y δ h]
  · exact hg

/-- The selected full-amplitude chain rule specializes to the normalized
scalar kernel, including the selector derivative. The original amplitude and
frequency stay fixed (`app:ch_response:eq:direct-envelope-profile`). -/
theorem hasLineDerivAt_normalized_selectedFamily
    (A : FullAmplitude d 1) (q : P × E → ℂ) (ζ : P → E)
    (ρ : ℝ) (c v : P) (x y δ : E)
    (hζ : DifferentiableAt ℝ ζ c)
    (hA : DifferentiableAt ℝ (fun z : E × E × E ↦ A z.1 z.2.1 z.2.2)
      (x, y, ρ • ζ c + δ)) (hq : DifferentiableAt ℝ q (c, ρ⁻¹ • δ)) :
    HasLineDerivAt ℝ
      (fun a ↦ normalizedScalarAmplitude (selectedFamily A q ζ ρ a) (x, y) δ)
      (normalizedScalarAmplitude (selectedAmplitudeDifferential A q ζ ρ c v) (x, y) δ) c v := by
  have h := hasLineDerivAt_selectedFamily A q ζ ρ c v x y δ hζ hA hq
  have hentry := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℂ) 0).hasFDerivAt.comp 0
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ Fin 1 → ℂ) 0).hasFDerivAt.comp 0 h.hasFDerivAt)
  have hd := hentry.hasDerivAt
  change HasDerivAt (fun t : ℝ ↦ selectedFamily A q ζ ρ (c + t • v) x y δ 0 0)
    ((1 : ℝ) • selectedAmplitudeDifferential A q ζ ρ c v x y δ 0 0) 0 at hd
  simpa only [one_smul, HasLineDerivAt, normalizedScalarAmplitude] using hd.const_mul (((2 * Real.pi) ^ d : ℂ)⁻¹)

end JanetCartan.ResponseTransfer.NearCarrierParameter
