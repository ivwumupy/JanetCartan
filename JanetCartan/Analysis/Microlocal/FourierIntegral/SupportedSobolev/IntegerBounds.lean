module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.NormalizedBounds
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.GainOneBounds

/-!
# Supported integer Sobolev bounds for orders zero and minus one

These are the unified conditional deductions in
`app:ch_regular_base:eq:fio-input`: for `d ∈ {0,1}`, the forward graph and
its literal Hilbert adjoint map `H^(max(s-d,0))` into `H^s`, with the tame
bound and fixed shift `μ = μ₀+2`. Natural subtraction implements the maximum.
The order-minus-one branch is derived through the actual first output
amplitudes, their weak identities, and vector derivative reconstruction.

All input hypotheses are explicit. Phase/geometry producers owe smoothness,
homogeneity and inverse gaps only on the open buffered supported chart and
the normalized chart cover. There are no global off-zero phase assumptions. The finite-calculus
and graph-realization producers owe the complete amplitudes with fixed low
seminorm bounds, the distributional L² realizations and the fixed low L²
reserve for every complete modified two-position amplitude. The source-independent
low graph theorem alone does not discharge that reserve. They do not owe a high
derivative-transfer or Sobolev estimate. Instantiation for their actual objects
remains their construction obligation.
The Euclidean Lebesgue spaces, Frobenius matrix norms, both physical positions,
all cutoffs, physical covectors and `(2*pi)^(-n)` kernel convention are unchanged.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Filter JanetCartan.Pseudodifferential
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SupportedSobolev
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
open PrimitiveProfiles GainOneProfiles
variable {n r : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The full integer-order forward graph estimate for `p=-d`, `d ∈ {0,1}`,
with output membership and high quantity `1 + |A|_{-d,s+μ} + |S|_{s+μ}`,
where `μ=μ₀+2` is independent of `s`. The constants precede `S`, `A` and `u`.
All branch bounds, weak derivative identities and primitive interpolation are
proved by the imported assemblies. The displayed geometric, primitive low
bounds and actual low L² realizations remain conditional producer inputs.
Source: `app:ch_regular_base:eq:fio-input`. -/
theorem exists_graph_integer_sobolev_constant
    (z : ι → Point n) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (U : ι → Set (Point n)) {V : Set (Point n)}
    (hU : ∀ i, IsOpen (U i)) (hV : IsOpen V)
    (hball : ∀ i, Metric.closedBall (z i) (δ i) ⊆ U i)
    (hrad : ∀ i, ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U i, (p.1, R • p.2) ∈ V)
    {X D : Set E} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (μ₀ : ℕ) {M : ℝ} (hM : 0 ≤ M) (B c C₀ : ℝ) (hc : 1 ≤ c) (hC₀ : 0 ≤ C₀)
    (d : ℕ) (hd : d = 0 ∨ d = 1) :
    ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ → IsCompact Y₀ → IsClosed F₀ → (0 : E) ∉ F₀ →
      ∀ (O : Set (Point n)), IsOpen O → (X₀ ×ˢ Y₀) ×ˢ F₀ ⊆ O →
      ∀ (S : E → E → ℝ), SupportedPhaseRegularity S O →
      SupportedMixedInvertibility S O → SupportedPhaseHomogeneity S O →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η) →
      (∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det) →
      (∀ i, ∀ p ∈ Metric.closedBall (z i) (δ i), ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B) →
      (∀ i, cNorm (Metric.closedBall (z i) (δ i)) (μ₀ + d + 2)
        (fun p : Point n ↦ S p.1.1 p.2) ≤ M) →
      ∀ (χ : ℕ → E → ℂ), (∀ j, ContDiff ℝ ∞ (χ j)) →
      (∀ j, HasCompactSupport (χ j)) →
      ∀ (T : FullAmplitude n r → H →L[ℂ] H) (A : FullAmplitude n r),
      ForwardAmplitudeAdmissible X₀ Y₀ F₀ A →
      GraphDistributionalRealization (graphOperator S) χ A (T A) → ‖T A‖ ≤ C₀ →
      (∀ i j, if d = 0 then
        BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j (uncurry A)
        else BoundedOrderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) j A) →
      (∀ i, (if d = 0 then
        normalizedSeminorm (Metric.closedBall (z i) (δ i)) μ₀ (uncurry A)
        else orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) (μ₀ + 1) A) ≤ M) →
      ∀ (ρ : E → ℝ), (∀ η, 1 ≤ ρ η) →
      (∀ p ∈ (X₀ ×ˢ Y₀) ×ˢ F₀, ∃ i, ∃ R : ℝ, 1 ≤ R ∧
        ∃ v ∈ Metric.closedBall (z i) (δ i), p = (v.1, R • v.2) ∧ ρ p.2 ≤ R ∧ R ≤ c * ρ p.2) →
      (∀ (G : FullAmplitude n r), ForwardAmplitudeAdmissible X₀ Y₀ F₀ G →
        GraphDistributionalRealization (graphOperator S) χ G (T G) → ∀ L : ℝ, 0 ≤ L →
        (∀ w : List (Coordinate n), w.length ≤ μ₀ → ∀ x y η,
          (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ L) → ‖T G‖ ≤ C₀ * L) →
      (if d = 0 then
        (∀ is : List (Fin n), is.length ≤ s →
          ∀ p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
            (graphTransferDatum S) A is,
            GraphDistributionalRealization (graphOperator S) χ p.1 (T p.1))
      else
        (∀ i (is : List (Fin n)), is.length ≤ s - 1 →
          ∀ p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
            (graphTransferDatum S) (graphFirstOutputAmplitude S A i) is,
            GraphDistributionalRealization (graphOperator S) χ p.1 (T p.1))) →
      ∀ u : H, MemVectorFourierSobolev ((s - d : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (T A u) ∧
          vectorFourierSobolevNorm (s : ℝ) (T A u) ≤ C *
            (vectorFourierSobolevNorm ((s - d : ℕ) : ℝ) u +
              normalizedGraphOrderHigh d z δ (s + (μ₀ + 2)) S A * ‖u‖) := by
  rcases hd with rfl | rfl
  · intro s
    obtain ⟨C, hC, hb⟩ := exists_graph_sobolev_constant_of_normalized_seminorms
      (n := n) (r := r) z δ hδ U hU hV hball hrad hX hD hchart hcone
      μ₀ hM B C₀ hC₀ s
    refine ⟨C, hC, ?_⟩
    intro X₀ Y₀ F₀ hX₀ hY₀ hF₀ hF₀0 O hO hcarrier S hS hinv hhom
      hSchart hhomChart hinvChart hgap hlowS χ hχ hχs T A hA hrealA hlow hbA hlowA
      ρ hρ hcover hl2 hreal u hu
    simp only [normalizedGraphOrderHigh, ↓reduceIte, Nat.sub_zero] at hbA hlowA hreal hu ⊢
    have hcover₀ : ∀ p ∈ ((X₀ ×ˢ Y₀) ×ˢ F₀), ∃ i, ∃ R : ℝ, 1 ≤ R ∧
        ∃ v ∈ Metric.closedBall (z i) (δ i), p = (v.1, R • v.2) ∧ ρ p.2 ≤ R := by
      intro p hp
      obtain ⟨i, R, hR, v, hv, he, hρR, _⟩ := hcover p hp
      exact ⟨i, R, hR, v, hv, he, hρR⟩
    exact hb X₀ Y₀ F₀ hX₀ hY₀ hF₀ hF₀0 O hO hcarrier S hS hinv hhom
      hSchart hhomChart hinvChart hgap hlowS χ hχ hχs T A hA hbA hlowA
      ρ (fun η ↦ zero_le_one.trans (hρ η)) hcover₀ hl2 hreal u hu
  · intro s
    obtain ⟨C, hC, hb⟩ := exists_graph_gain_one_constant_of_normalized_seminorms
      (n := n) (r := r) z δ hδ U hU hV hball hrad hX hD hchart hcone
      μ₀ hM B c C₀ hc hC₀ s
    refine ⟨C, hC, ?_⟩
    intro X₀ Y₀ F₀ hX₀ hY₀ hF₀ hF₀0 O hO hcarrier S hS hinv hhom
      hSchart hhomChart hinvChart hgap hlowS χ hχ hχs T A hA hrealA hlow hbA hlowA
      ρ hρ hcover hl2 hreal u hu
    simp only [normalizedGraphOrderHigh, Nat.one_ne_zero, ↓reduceIte] at hbA hlowA hreal hu ⊢
    exact hb X₀ Y₀ F₀ hX₀ hY₀ hF₀ hF₀0 O hO hcarrier S hS hinv hhom
      hSchart hhomChart hinvChart hgap hlowS χ hχ hχs T A hA hrealA hlow hbA hlowA
      ρ hρ hcover hl2 hreal u hu

/-- The full integer-order literal Hilbert adjoint estimate for `p=-d`, `d ∈ {0,1}`,
with output membership and high quantity `1 + |A|_{-d,s+μ} + |S|_{s+μ}`,
where `μ=μ₀+2` is independent of `s`. The constants precede `S`, `A` and `u`.
All branch bounds, weak derivative identities and primitive interpolation are
proved by the imported assemblies. The displayed geometric, primitive low
bounds and actual low L² realizations remain conditional producer inputs.
Source: `app:ch_regular_base:eq:fio-input`. -/
theorem exists_adjoint_integer_sobolev_constant
    (z : ι → Point n) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (U : ι → Set (Point n)) {V : Set (Point n)}
    (hU : ∀ i, IsOpen (U i)) (hV : IsOpen V)
    (hball : ∀ i, Metric.closedBall (z i) (δ i) ⊆ U i)
    (hrad : ∀ i, ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U i, (p.1, R • p.2) ∈ V)
    {X D : Set E} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (μ₀ : ℕ) {M : ℝ} (hM : 0 ≤ M) (B c C₀ : ℝ) (hc : 1 ≤ c) (hC₀ : 0 ≤ C₀)
    (d : ℕ) (hd : d = 0 ∨ d = 1) :
    ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (K₀ : Set (E × E)) (F₀ : Set E), IsCompact K₀ → IsClosed F₀ → (0 : E) ∉ F₀ →
      ∀ (O : Set (Point n)), IsOpen O → K₀ ×ˢ F₀ ⊆ O →
      ∀ (S : E → E → ℝ), SupportedPhaseRegularity S O →
      SupportedMixedInvertibility S O → SupportedPhaseHomogeneity S O →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η) →
      (∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det) →
      (∀ i, ∀ p ∈ Metric.closedBall (z i) (δ i), ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B) →
      (∀ i, cNorm (Metric.closedBall (z i) (δ i)) (μ₀ + d + 2)
        (fun p : Point n ↦ S p.1.1 p.2) ≤ M) →
      ∀ (χ : ℕ → E → ℂ), (∀ j, ContDiff ℝ ∞ (χ j)) →
      (∀ j, HasCompactSupport (χ j)) → (∀ j, (0 : E) ∉ tsupport (χ j)) →
      ∀ (T : FullAmplitude n r → H →L[ℂ] H) (A : FullAmplitude n r),
      ReverseAmplitudeAdmissible K₀ A → (∀ x y η, η ∉ F₀ → A x y η = 0) →
      ContDiffOn ℝ ∞ (uncurry A) V →
      (∀ i j, if d = 0 then
        BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j (uncurry A)
        else BoundedOrderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) j A) →
      (∀ i, (if d = 0 then
        normalizedSeminorm (Metric.closedBall (z i) (δ i)) μ₀ (uncurry A)
        else orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) (μ₀ + 1) A) ≤ M) →
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
      (if d = 0 then
        (∀ is : List (Fin n), is.length ≤ s →
          ∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
            (adjointTransferDatum S) (fun x y η ↦ (A x y η).conjTranspose) is,
            GraphDistributionalRealization (reverseGraphOperator S)
              (fun j η ↦ star (χ j η)) p.1 (T p.1))
      else
        (∀ i (is : List (Fin n)), is.length ≤ s - 1 →
          ∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
            (adjointTransferDatum S) (adjointFirstOutputAmplitude A i) is,
            GraphDistributionalRealization (reverseGraphOperator S)
              (fun j η ↦ star (χ j η)) p.1 (T p.1))) →
      ∀ u : H, MemVectorFourierSobolev ((s - d : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W.adjoint u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W.adjoint u) ≤ C *
            (vectorFourierSobolevNorm ((s - d : ℕ) : ℝ) u +
              normalizedGraphOrderHigh d z δ (s + (μ₀ + 2)) S A * ‖u‖) := by
  rcases hd with rfl | rfl
  · intro s
    obtain ⟨C, hC, hb⟩ := exists_adjoint_sobolev_constant_of_normalized_seminorms
      (n := n) (r := r) z δ hδ U hU hV hball hrad hX hD hchart hcone
      μ₀ hM B C₀ hC₀ s
    refine ⟨C, hC, ?_⟩
    intro K₀ F₀ hK₀ hF₀ hF₀0 O hO hcarrier S hS hinv hhom
      hSchart hhomChart hinvChart hgap hlowS χ hχ hχs hχ0 T A hA hAF hAc hbA hlowA
      W hW hlow ρ hρ hηρ hcover hl2 hreal u hu
    simp only [normalizedGraphOrderHigh, ↓reduceIte, Nat.sub_zero] at hbA hlowA hreal hu ⊢
    have hcover₀ : ∀ p ∈ (K₀ ×ˢ F₀), ∃ i, ∃ R : ℝ, 1 ≤ R ∧
        ∃ v ∈ Metric.closedBall (z i) (δ i), p = (v.1, R • v.2) ∧ ρ p.2 ≤ R := by
      intro p hp
      obtain ⟨i, R, hR, v, hv, he, hρR, _⟩ := hcover p hp
      exact ⟨i, R, hR, v, hv, he, hρR⟩
    exact hb K₀ F₀ hK₀ hF₀ hF₀0 O hO hcarrier S hS hinv hhom
      hSchart hhomChart hinvChart hgap hlowS χ hχ hχs hχ0 T A hA hAF hAc hbA hlowA
      W hW ρ (fun η ↦ zero_le_one.trans (hρ η)) hcover₀ hl2 hreal u hu
  · intro s
    obtain ⟨C, hC, hb⟩ := exists_adjoint_gain_one_constant_of_normalized_seminorms
      (n := n) (r := r) z δ hδ U hU hV hball hrad hX hD hchart hcone
      μ₀ hM B c C₀ hc hC₀ s
    refine ⟨C, hC, ?_⟩
    intro K₀ F₀ hK₀ hF₀ hF₀0 O hO hcarrier S hS hinv hhom
      hSchart hhomChart hinvChart hgap hlowS χ hχ hχs hχ0 T A hA hAF hAc hbA hlowA
      W hW hlow ρ hρ hηρ hcover hl2 hreal u hu
    simp only [normalizedGraphOrderHigh, Nat.one_ne_zero, ↓reduceIte] at hbA hlowA hreal hu ⊢
    exact hb K₀ F₀ hK₀ hF₀ hF₀0 O hO hcarrier S hS hinv hhom
      hSchart hhomChart hinvChart hgap hlowS χ hχ hχs hχ0 T A hA hAF hAc hbA hlowA
      W hW hlow ρ hρ hηρ hcover hl2 hreal u hu

end JanetCartan.FourierIntegral.SupportedSobolev
