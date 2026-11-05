module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.StrongAssembly
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles

/-!
# Supported order-zero bounds from original normalized seminorms

This instantiates every primitive profile and interpolation premise of
`StrongAssembly` using the actual finite normalized charts. The high quantity
in `app:ch_regular_base:eq:fio-input` is the sum of the complete amplitude and
phase seminorms, with fixed shift `μ₀ + 2`. The inverse jets, weak expansion,
branch norms, Fourier interpolation, membership, and density extension are
proved, not inputs.

The geometric chart cover, ordinary phase/amplitude smoothness, homogeneity,
actual mixed inverse gap, fixed low seminorm bounds, distributional realizations,
and fixed low L² reserve remain conditional. Their producers are the Hamilton
phase, compatible geometry, graph realization, and finite-calculus constructions.
These theorems are the order-zero deduction, not an unconditional construction
of those analytic inputs.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Filter JanetCartan.Pseudodifferential
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SupportedSobolev
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
open PrimitiveProfiles
variable {n r : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Strong order-zero forward graph estimate with the actual normalized
seminorm high quantity and fixed shift `μ₀ + 2`. No individual interpolation,
high inverse-jet, branch norm, or weak derivative identity is assumed.
Source: `app:ch_regular_base:eq:fio-input`, `d = 0`. -/
theorem exists_graph_sobolev_constant_of_normalized_seminorms
    (z : ι → Point n) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (U : ι → Set (Point n)) {V : Set (Point n)}
    (hU : ∀ i, IsOpen (U i)) (hV : IsOpen V)
    (hball : ∀ i, Metric.closedBall (z i) (δ i) ⊆ U i)
    (hrad : ∀ i, ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U i, (p.1, R • p.2) ∈ V)
    {X D : Set E} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (μ₀ : ℕ) {M : ℝ} (hM : 0 ≤ M) (B C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ → IsCompact Y₀ → IsClosed F₀ → (0 : E) ∉ F₀ →
      ∀ (O : Set (Point n)), IsOpen O → (X₀ ×ˢ Y₀) ×ˢ F₀ ⊆ O →
      ∀ (S : E → E → ℝ), SupportedPhaseRegularity S O →
      SupportedMixedInvertibility S O → SupportedPhaseHomogeneity S O →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η) →
      (∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det) →
      (∀ i, ∀ p ∈ Metric.closedBall (z i) (δ i), ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B) →
      (∀ i, cNorm (Metric.closedBall (z i) (δ i)) (μ₀ + 2)
        (fun p : Point n ↦ S p.1.1 p.2) ≤ M) →
      ∀ (χ : ℕ → E → ℂ), (∀ j, ContDiff ℝ ∞ (χ j)) →
      (∀ j, HasCompactSupport (χ j)) →
      ∀ (T : FullAmplitude n r → H →L[ℂ] H) (A : FullAmplitude n r),
      ForwardAmplitudeAdmissible X₀ Y₀ F₀ A →
      (∀ i j, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j (uncurry A)) →
      (∀ i, normalizedSeminorm (Metric.closedBall (z i) (δ i)) μ₀ (uncurry A) ≤ M) →
      ∀ (ρ : E → ℝ), (∀ η, 0 ≤ ρ η) →
      (∀ p ∈ (X₀ ×ˢ Y₀) ×ˢ F₀, ∃ i, ∃ R : ℝ, 1 ≤ R ∧
        ∃ v ∈ Metric.closedBall (z i) (δ i), p = (v.1, R • v.2) ∧ ρ p.2 ≤ R) →
      (∀ (G : FullAmplitude n r), ForwardAmplitudeAdmissible X₀ Y₀ F₀ G →
        GraphDistributionalRealization (graphOperator S) χ G (T G) → ∀ L : ℝ, 0 ≤ L →
        (∀ w : List (Coordinate n), w.length ≤ μ₀ → ∀ x y η,
          (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ L) → ‖T G‖ ≤ C₀ * L) →
      (∀ is : List (Fin n), is.length ≤ s →
        ∀ p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
          (graphTransferDatum S) A is,
          GraphDistributionalRealization (graphOperator S) χ p.1 (T p.1)) →
      ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (T A u) ∧
          vectorFourierSobolevNorm (s : ℝ) (T A u) ≤ C *
            (vectorFourierSobolevNorm (s : ℝ) u +
              normalizedGraphHigh z δ (s + (μ₀ + 2)) S A * ‖u‖) := by
  obtain ⟨L, hL, hp⟩ := exists_finitePrimitiveProfile_inputs (r := r)
    z δ hδ U hU hV hball hrad hX hD hchart hcone μ₀ hM B
  intro s
  obtain ⟨C₁, I, hC₁, hI, hprofiles⟩ := hp s
  obtain ⟨C₂, hC₂, hbound⟩ := exists_graph_sobolev_constant_of_weighted_primitives
    (n := n) (r := r) μ₀ s L I C₀ hL hI hC₀
  refine ⟨C₂ * C₁, mul_pos hC₂ (lt_of_lt_of_le zero_lt_one hC₁), ?_⟩
  intro X₀ Y₀ F₀ hX₀ hY₀ hF₀ hF₀0 O hO hcarrier S hS hinv hhom
    hSchart hhomChart hinvChart hgap hlowS χ hχ hχs T A hA hbA hlowA
    ρ hρ hcover hl2 hreal u hu
  have hAc : ContDiffOn ℝ ∞ (uncurry A) V :=
    (hA.smooth.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))).contDiffOn
  obtain ⟨hq, hmono, hhigh1, hlow, hhigh, hinterp, hjets⟩ :=
    hprofiles S A hSchart hhomChart hinvChart hgap hAc hbA hlowS hlowA
  obtain ⟨hAmp, hScalar⟩ := hjets ((X₀ ×ˢ Y₀) ×ˢ F₀) ρ hρ hcover
  have hb := hbound X₀ Y₀ F₀ hX₀ hY₀ hF₀ hF₀0 O hO hcarrier S hS hinv hhom χ hχ hχs T A hA
    ρ hρ hl2 (finitePrimitiveProfile z δ S A)
    (C₁ * normalizedGraphHigh z δ (s + (μ₀ + 2)) S A)
    hq hmono hhigh1 hlow hhigh hinterp hAmp hScalar hreal u hu
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hnorm : 0 ≤ vectorFourierSobolevNorm (s : ℝ) u := norm_nonneg _
  calc
    _ ≤ C₂ * (C₁ * vectorFourierSobolevNorm (s : ℝ) u +
        C₁ * normalizedGraphHigh z δ (s + (μ₀ + 2)) S A * ‖u‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (le_mul_of_one_le_left hnorm hC₁) le_rfl) hC₂.le
    _ = _ := by ring

/-- Strong order-zero estimate for the literal Hilbert adjoint with the same
normalized original amplitude seminorms and fixed shift `μ₀ + 2`. The original
coordinate order, Frobenius norm, and once-conjugated regularizers are retained.
Source: `app:ch_regular_base:eq:fio-input`, `d = 0`, and
`app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem exists_adjoint_sobolev_constant_of_normalized_seminorms
    (z : ι → Point n) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (U : ι → Set (Point n)) {V : Set (Point n)}
    (hU : ∀ i, IsOpen (U i)) (hV : IsOpen V)
    (hball : ∀ i, Metric.closedBall (z i) (δ i) ⊆ U i)
    (hrad : ∀ i, ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U i, (p.1, R • p.2) ∈ V)
    {X D : Set E} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (μ₀ : ℕ) {M : ℝ} (hM : 0 ≤ M) (B C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (K₀ : Set (E × E)) (F₀ : Set E), IsCompact K₀ → IsClosed F₀ → (0 : E) ∉ F₀ →
      ∀ (O : Set (Point n)), IsOpen O → K₀ ×ˢ F₀ ⊆ O →
      ∀ (S : E → E → ℝ), SupportedPhaseRegularity S O →
      SupportedMixedInvertibility S O → SupportedPhaseHomogeneity S O →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η) →
      (∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det) →
      (∀ i, ∀ p ∈ Metric.closedBall (z i) (δ i), ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B) →
      (∀ i, cNorm (Metric.closedBall (z i) (δ i)) (μ₀ + 2)
        (fun p : Point n ↦ S p.1.1 p.2) ≤ M) →
      ∀ (χ : ℕ → E → ℂ), (∀ j, ContDiff ℝ ∞ (χ j)) →
      (∀ j, HasCompactSupport (χ j)) → (∀ j, (0 : E) ∉ tsupport (χ j)) →
      ∀ (T : FullAmplitude n r → H →L[ℂ] H) (A : FullAmplitude n r),
      ReverseAmplitudeAdmissible K₀ A → (∀ x y η, η ∉ F₀ → A x y η = 0) →
      ContDiffOn ℝ ∞ (uncurry A) V →
      (∀ i j, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j (uncurry A)) →
      (∀ i, normalizedSeminorm (Metric.closedBall (z i) (δ i)) μ₀ (uncurry A) ≤ M) →
      ∀ W : H →L[ℂ] H,
      GraphDistributionalRealization (reverseGraphOperator S)
        (fun j η ↦ star (χ j η)) (fun x y η ↦ (A x y η).conjTranspose) W.adjoint →
      ∀ (ρ : E → ℝ), (∀ η, 0 ≤ ρ η) →
      (∀ p ∈ K₀ ×ˢ F₀, ∃ i, ∃ R : ℝ, 1 ≤ R ∧
        ∃ v ∈ Metric.closedBall (z i) (δ i), p = (v.1, R • v.2) ∧ ρ p.2 ≤ R) →
      (∀ (G : FullAmplitude n r), ReverseAmplitudeAdmissible K₀ G →
        (∀ x y η, η ∉ F₀ → G x y η = 0) →
        GraphDistributionalRealization (reverseGraphOperator S)
          (fun j η ↦ star (χ j η)) G (T G) → ∀ L : ℝ, 0 ≤ L →
        (∀ w : List (Coordinate n), w.length ≤ μ₀ → ∀ x y η,
          (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ L) → ‖T G‖ ≤ C₀ * L) →
      (∀ is : List (Fin n), is.length ≤ s →
        ∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
          (adjointTransferDatum S) (fun x y η ↦ (A x y η).conjTranspose) is,
          GraphDistributionalRealization (reverseGraphOperator S)
            (fun j η ↦ star (χ j η)) p.1 (T p.1)) →
      ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W.adjoint u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W.adjoint u) ≤ C *
            (vectorFourierSobolevNorm (s : ℝ) u +
              normalizedGraphHigh z δ (s + (μ₀ + 2)) S A * ‖u‖) := by
  obtain ⟨L, hL, hp⟩ := exists_finitePrimitiveProfile_inputs (r := r)
    z δ hδ U hU hV hball hrad hX hD hchart hcone μ₀ hM B
  intro s
  obtain ⟨C₁, I, hC₁, hI, hprofiles⟩ := hp s
  obtain ⟨C₂, hC₂, hbound⟩ := exists_adjoint_sobolev_constant_of_weighted_primitives
    (n := n) (r := r) μ₀ s L I C₀ hL hI hC₀
  refine ⟨C₂ * C₁, mul_pos hC₂ (lt_of_lt_of_le zero_lt_one hC₁), ?_⟩
  intro K₀ F₀ hK₀ hF₀ hF₀0 O hO hcarrier S hS hinv hhom
    hSchart hhomChart hinvChart hgap hlowS χ hχ hχs hχ0 T A hA hAF hAc hbA hlowA
    W hW ρ hρ hcover hl2 hreal u hu
  obtain ⟨hq, hmono, hhigh1, hlow, hhigh, hinterp, hjets⟩ :=
    hprofiles S A hSchart hhomChart hinvChart hgap hAc hbA hlowS hlowA
  obtain ⟨hAmp, hScalar⟩ := hjets (K₀ ×ˢ F₀) ρ hρ hcover
  have hb := hbound K₀ F₀ hK₀ hF₀ hF₀0 O hO hcarrier S hS hinv hhom χ hχ hχs hχ0 T A hA hAF W hW
    ρ hρ hl2 (finitePrimitiveProfile z δ S A)
    (C₁ * normalizedGraphHigh z δ (s + (μ₀ + 2)) S A)
    hq hmono hhigh1 hlow hhigh hinterp hAmp hScalar hreal u hu
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hnorm : 0 ≤ vectorFourierSobolevNorm (s : ℝ) u := norm_nonneg _
  calc
    _ ≤ C₂ * (C₁ * vectorFourierSobolevNorm (s : ℝ) u +
        C₁ * normalizedGraphHigh z δ (s + (μ₀ + 2)) S A * ‖u‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (le_mul_of_one_le_left hnorm hC₁) le_rfl) hC₂.le
    _ = _ := by ring

end JanetCartan.FourierIntegral.SupportedSobolev
