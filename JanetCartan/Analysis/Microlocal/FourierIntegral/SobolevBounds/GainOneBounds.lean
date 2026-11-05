module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.GainOneAssembly
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.GainOneProfiles

/-!
# Strong gain-one graph bounds from normalized seminorms

This closes the primitive-profile premises of `GainOneAssembly` for the actual
order-minus-one normalization `R • A(x,y,Rη)`. Both estimates hold for every
natural output order, including zero, with input order `s - 1 = max(s-1,0)`.
The high quantity is exactly `1 + |A|_{-1,s+μ} + |S|_{s+μ}`, with the fixed
shift `μ = μ₀ + 2`. The fixed low baselines are `μ₀+1` for the amplitude and
`μ₀+3` for the phase. Constants precede the phase, amplitude and datum.

The finite normalized chart cover, smoothness, homogeneity, actual inverse gap,
low seminorm bounds, low L² bounds and distributional realizations remain
conditional inputs of the Hamilton phase, compatible geometry, graph realization
and finite-calculus producers. Individual interpolation, inverse jets, all
branch estimates and weak identities, and Sobolev membership are proved.
Consumers are the finite calculus, regular sector and response constructions.
Source: `app:ch_regular_base:eq:fio-input` and the gain-one paragraph following
`app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Filter JanetCartan.Pseudodifferential
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
open PrimitiveProfiles GainOneProfiles
variable {n r : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

private theorem low_bound_zero (T : H →L[ℂ] H) {C₀ C Hhigh : ℝ}
    (hC₀ : 0 ≤ C₀) (hC : C₀ ≤ C) (hH : 0 ≤ Hhigh) (hT : ‖T‖ ≤ C₀) (u : H) :
    MemVectorFourierSobolev 0 (T u) ∧
      vectorFourierSobolevNorm 0 (T u) ≤ C *
        (vectorFourierSobolevNorm 0 u + Hhigh * ‖u‖) := by
  refine ⟨fun i ↦ memFourierSobolev_zero _, ?_⟩
  simp only [vectorFourierSobolevNorm_zero]
  calc
    ‖T u‖ ≤ C₀ * ‖u‖ := (T.le_opNorm u).trans
      (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
    _ ≤ C * (‖u‖ + Hhigh * ‖u‖) := mul_le_mul hC
      (le_add_of_nonneg_right (mul_nonneg hH (norm_nonneg _))) (norm_nonneg _) (hC₀.trans hC)

/-- Strong gain-one forward graph estimate on every vector Sobolev datum, including
output order zero. All primitive profiles are instantiated from normalized
seminorms, with fixed shift `μ₀+2`; no high branch norm or derivative identity
is assumed. Source: `app:ch_regular_base:eq:fio-input`, `d = 1`. -/
theorem exists_graph_gain_one_constant_of_normalized_seminorms
    (z : ι → Point n) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (U : ι → Set (Point n)) {V : Set (Point n)}
    (hU : ∀ i, IsOpen (U i)) (hV : IsOpen V)
    (hball : ∀ i, Metric.closedBall (z i) (δ i) ⊆ U i)
    (hrad : ∀ i, ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U i, (p.1, R • p.2) ∈ V)
    {X D : Set E} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (μ₀ : ℕ) {M : ℝ} (hM : 0 ≤ M) (B c C₀ : ℝ) (hc : 1 ≤ c) (hC₀ : 0 ≤ C₀) :
    ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ → IsCompact Y₀ → IsClosed F₀ → (0 : E) ∉ F₀ →
      ∀ (S : E → E → ℝ),
      (∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η)) →
      (∀ p ∈ X₀ ×ˢ Y₀, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det) →
      (∀ x η, η ≠ 0 → ∀ᶠ t : ℝ in 𝓝 1,
        (fun z ↦ S z (t • η)) =ᶠ[𝓝 x] (fun z ↦ t * S z η)) →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η) →
      (∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det) →
      (∀ i, ∀ p ∈ Metric.closedBall (z i) (δ i), ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B) →
      (∀ i, cNorm (Metric.closedBall (z i) (δ i)) (μ₀ + 3)
        (fun p : Point n ↦ S p.1.1 p.2) ≤ M) →
      ∀ (χ : ℕ → E → ℂ), (∀ j, ContDiff ℝ ∞ (χ j)) →
      (∀ j, HasCompactSupport (χ j)) →
      ∀ (T : FullAmplitude n r → H →L[ℂ] H) (A : FullAmplitude n r),
      ForwardAmplitudeAdmissible X₀ Y₀ F₀ A →
      GraphDistributionalRealization (graphOperator S) χ A (T A) → ‖T A‖ ≤ C₀ →
      (∀ i j, BoundedOrderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) j A) →
      (∀ i, orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) (μ₀ + 1) A ≤ M) →
      ∀ (ρ : E → ℝ), (∀ η, 1 ≤ ρ η) →
      (∀ p ∈ (X₀ ×ˢ Y₀) ×ˢ F₀, ∃ i, ∃ R : ℝ, 1 ≤ R ∧
        ∃ v ∈ Metric.closedBall (z i) (δ i), p = (v.1, R • v.2) ∧ ρ p.2 ≤ R ∧ R ≤ c * ρ p.2) →
      (∀ (G : FullAmplitude n r), ForwardAmplitudeAdmissible X₀ Y₀ F₀ G →
        GraphDistributionalRealization (graphOperator S) χ G (T G) → ∀ L : ℝ, 0 ≤ L →
        (∀ w : List (Coordinate n), w.length ≤ μ₀ → ∀ x y η,
          (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ L) → ‖T G‖ ≤ C₀ * L) →
      (∀ i (is : List (Fin n)), is.length ≤ s - 1 →
        ∀ p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
          (graphTransferDatum S) (graphFirstOutputAmplitude S A i) is,
          GraphDistributionalRealization (graphOperator S) χ p.1 (T p.1)) →
      ∀ u : H, MemVectorFourierSobolev ((s - 1 : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (T A u) ∧
          vectorFourierSobolevNorm (s : ℝ) (T A u) ≤ C *
            (vectorFourierSobolevNorm ((s - 1 : ℕ) : ℝ) u +
              normalizedGainOneHigh z δ (s + (μ₀ + 2)) S A * ‖u‖) := by
  intro s
  obtain ⟨P, C₁, hP, hC₁, hprofiles⟩ := exists_finiteGainOne_primitive_inputs (r := r)
    z δ hδ U hU hV hball hrad hX hD hchart hcone μ₀ hM B c hc (s - 1)
  obtain ⟨C₂, hC₂, hbound⟩ := exists_graph_gain_one_constant_of_primitive_profiles
    (n := n) (r := r) μ₀ (s - 1) P C₀ hP hC₀
  have hCprod : 0 < C₂ * C₁ := mul_pos hC₂ (lt_of_lt_of_le zero_lt_one hC₁)
  refine ⟨C₂ * C₁ + C₀ + 1, by linarith, ?_⟩
  intro X₀ Y₀ F₀ hX₀ hY₀ hF₀ hF₀0 S hS hinv hhom
    hSchart hhomChart hinvChart hgap hlowS χ hχ hχs T A hA hrealA hlow hbA hlowA
    ρ hρ hcover hl2 hreal u hu
  by_cases hs : s = 0
  · subst s
    simpa only [Nat.zero_sub, Nat.cast_zero] using low_bound_zero (T A) hC₀
      (by linarith : C₀ ≤ C₂ * C₁ + C₀ + 1)
      (zero_le_one.trans (one_le_normalizedGainOneHigh z δ (0 + (μ₀ + 2)) S A)) hlow u
  have hs' : s - 1 + 1 = s := by omega
  have hAc : ContDiffOn ℝ ∞ (uncurry A) V :=
    (hA.smooth.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))).contDiffOn
  obtain ⟨hH, hjets⟩ := hprofiles S A hSchart hhomChart hinvChart hgap hAc hbA hlowS hlowA
  rw [hs'] at hH hjets hbound
  obtain ⟨hAmp, hPhase, hScalar⟩ := hjets ((X₀ ×ˢ Y₀) ×ˢ F₀) ρ hρ hcover
  have hb := hbound X₀ Y₀ F₀ hX₀ hY₀ hF₀ hF₀0 S hS hinv hhom χ hχ hχs T A hA
    hrealA hlow ρ hρ hl2 (C₁ * normalizedGainOneHigh z δ (s + (μ₀ + 2)) S A)
    hH hAmp hPhase hScalar hreal u hu
  have hcast : ((s - 1 : ℕ) : ℝ) + 1 = (s : ℝ) := by exact_mod_cast hs'
  rw [hcast] at hb
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hnorm : 0 ≤ vectorFourierSobolevNorm ((s - 1 : ℕ) : ℝ) u := norm_nonneg _
  have hhigh := zero_le_one.trans (one_le_normalizedGainOneHigh z δ (s + (μ₀ + 2)) S A)
  calc
    _ ≤ C₂ * (C₁ * vectorFourierSobolevNorm ((s - 1 : ℕ) : ℝ) u +
        C₁ * normalizedGainOneHigh z δ (s + (μ₀ + 2)) S A * ‖u‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (le_mul_of_one_le_left hnorm hC₁) le_rfl) hC₂.le
    _ = (C₂ * C₁) * (vectorFourierSobolevNorm ((s - 1 : ℕ) : ℝ) u +
        normalizedGainOneHigh z δ (s + (μ₀ + 2)) S A * ‖u‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
      (add_nonneg hnorm (mul_nonneg hhigh (norm_nonneg _)))

/-- Strong gain-one literal Hilbert adjoint estimate on every vector Sobolev datum, including
output order zero. All primitive profiles are instantiated from normalized
seminorms, with fixed shift `μ₀+2`; no high branch norm or derivative identity
is assumed. Source: `app:ch_regular_base:eq:fio-input`, `d = 1`. -/
theorem exists_adjoint_gain_one_constant_of_normalized_seminorms
    (z : ι → Point n) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (U : ι → Set (Point n)) {V : Set (Point n)}
    (hU : ∀ i, IsOpen (U i)) (hV : IsOpen V)
    (hball : ∀ i, Metric.closedBall (z i) (δ i) ⊆ U i)
    (hrad : ∀ i, ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U i, (p.1, R • p.2) ∈ V)
    {X D : Set E} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (μ₀ : ℕ) {M : ℝ} (hM : 0 ≤ M) (B c C₀ : ℝ) (hc : 1 ≤ c) (hC₀ : 0 ≤ C₀) :
    ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (K₀ : Set (E × E)) (F₀ : Set E), IsCompact K₀ → IsClosed F₀ → (0 : E) ∉ F₀ →
      ∀ (S : E → E → ℝ),
      (∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η)) →
      (∀ p ∈ K₀, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det) →
      (∀ p ∈ K₀, ∀ η, η ≠ 0 → ∀ᶠ t : ℝ in 𝓝 1,
        (fun z ↦ S z (t • η)) =ᶠ[𝓝 p.1] (fun z ↦ t * S z η)) →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η) →
      (∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det) →
      (∀ i, ∀ p ∈ Metric.closedBall (z i) (δ i), ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B) →
      (∀ i, cNorm (Metric.closedBall (z i) (δ i)) (μ₀ + 3)
        (fun p : Point n ↦ S p.1.1 p.2) ≤ M) →
      ∀ (χ : ℕ → E → ℂ), (∀ j, ContDiff ℝ ∞ (χ j)) →
      (∀ j, HasCompactSupport (χ j)) → (∀ j, (0 : E) ∉ tsupport (χ j)) →
      ∀ (T : FullAmplitude n r → H →L[ℂ] H) (A : FullAmplitude n r),
      ReverseAmplitudeAdmissible K₀ A → (∀ x y η, η ∉ F₀ → A x y η = 0) →
      ContDiffOn ℝ ∞ (uncurry A) V →
      (∀ i j, BoundedOrderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) j A) →
      (∀ i, orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) (μ₀ + 1) A ≤ M) →
      ∀ W : H →L[ℂ] H,
      GraphDistributionalRealization (reverseGraphOperator S)
        (fun j η ↦ star (χ j η)) (fun x y η ↦ (A x y η).conjTranspose) W.adjoint → ‖W.adjoint‖ ≤ C₀ →
      ∀ (ρ : E → ℝ), (∀ η, 1 ≤ ρ η) → (∀ η, ‖η‖ ≤ ρ η) →
      (∀ p ∈ K₀ ×ˢ F₀, ∃ i, ∃ R : ℝ, 1 ≤ R ∧
        ∃ v ∈ Metric.closedBall (z i) (δ i), p = (v.1, R • v.2) ∧ ρ p.2 ≤ R ∧ R ≤ c * ρ p.2) →
      (∀ (G : FullAmplitude n r), ReverseAmplitudeAdmissible K₀ G →
        (∀ x y η, η ∉ F₀ → G x y η = 0) →
        GraphDistributionalRealization (reverseGraphOperator S)
          (fun j η ↦ star (χ j η)) G (T G) → ∀ L : ℝ, 0 ≤ L →
        (∀ w : List (Coordinate n), w.length ≤ μ₀ → ∀ x y η,
          (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ L) → ‖T G‖ ≤ C₀ * L) →
      (∀ i (is : List (Fin n)), is.length ≤ s - 1 →
        ∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
          (adjointTransferDatum S) (adjointFirstOutputAmplitude A i) is,
          GraphDistributionalRealization (reverseGraphOperator S)
            (fun j η ↦ star (χ j η)) p.1 (T p.1)) →
      ∀ u : H, MemVectorFourierSobolev ((s - 1 : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W.adjoint u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W.adjoint u) ≤ C *
            (vectorFourierSobolevNorm ((s - 1 : ℕ) : ℝ) u +
              normalizedGainOneHigh z δ (s + (μ₀ + 2)) S A * ‖u‖) := by
  intro s
  obtain ⟨P, C₁, hP, hC₁, hprofiles⟩ := exists_finiteGainOne_primitive_inputs (r := r)
    z δ hδ U hU hV hball hrad hX hD hchart hcone μ₀ hM B c hc (s - 1)
  obtain ⟨C₂, hC₂, hbound⟩ := exists_adjoint_gain_one_constant_of_primitive_profiles
    (n := n) (r := r) μ₀ (s - 1) P C₀ hP hC₀
  have hCprod : 0 < C₂ * C₁ := mul_pos hC₂ (lt_of_lt_of_le zero_lt_one hC₁)
  refine ⟨C₂ * C₁ + C₀ + 1, by linarith, ?_⟩
  intro K₀ F₀ hK₀ hF₀ hF₀0 S hS hinv hhom
    hSchart hhomChart hinvChart hgap hlowS χ hχ hχs hχ0 T A hA hAF hAc hbA hlowA
    W hW hlow ρ hρ hηρ hcover hl2 hreal u hu
  by_cases hs : s = 0
  · subst s
    simpa only [Nat.zero_sub, Nat.cast_zero] using low_bound_zero W.adjoint hC₀
      (by linarith : C₀ ≤ C₂ * C₁ + C₀ + 1)
      (zero_le_one.trans (one_le_normalizedGainOneHigh z δ (0 + (μ₀ + 2)) S A)) hlow u
  have hs' : s - 1 + 1 = s := by omega
  obtain ⟨hH, hjets⟩ := hprofiles S A hSchart hhomChart hinvChart hgap hAc hbA hlowS hlowA
  rw [hs'] at hH hjets hbound
  obtain ⟨hAmp, hPhase, hScalar⟩ := hjets (K₀ ×ˢ F₀) ρ hρ hcover
  have hb := hbound K₀ F₀ hK₀ hF₀ hF₀0 S hS hinv hhom χ hχ hχs hχ0 T A hA hAF
    W hW hlow ρ hρ hηρ hl2 (C₁ * normalizedGainOneHigh z δ (s + (μ₀ + 2)) S A)
    hH hAmp hScalar hreal u hu
  have hcast : ((s - 1 : ℕ) : ℝ) + 1 = (s : ℝ) := by exact_mod_cast hs'
  rw [hcast] at hb
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hnorm : 0 ≤ vectorFourierSobolevNorm ((s - 1 : ℕ) : ℝ) u := norm_nonneg _
  have hhigh := zero_le_one.trans (one_le_normalizedGainOneHigh z δ (s + (μ₀ + 2)) S A)
  calc
    _ ≤ C₂ * (C₁ * vectorFourierSobolevNorm ((s - 1 : ℕ) : ℝ) u +
        C₁ * normalizedGainOneHigh z δ (s + (μ₀ + 2)) S A * ‖u‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (le_mul_of_one_le_left hnorm hC₁) le_rfl) hC₂.le
    _ = (C₂ * C₁) * (vectorFourierSobolevNorm ((s - 1 : ℕ) : ℝ) u +
        normalizedGainOneHigh z δ (s + (μ₀ + 2)) S A * ‖u‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
      (add_nonneg hnorm (mul_nonneg hhigh (norm_nonneg _)))

end JanetCartan.FourierIntegral
