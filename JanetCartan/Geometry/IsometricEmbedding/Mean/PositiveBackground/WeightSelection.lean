module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.WeightBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RetainedAssembly.ExternalWeights

/-!
# Original external-weight and fixed measurement selection

Select the external squared weights on the supplied retained cells, covering
the full detector projection. Then select one physical measurement buffer on
their entire compact supports. Both choices precede the source mean, source
scale, inverse and histories. The old scale-by-scale measurement choices are
not identified with this choice; the normalized row must be constructed with
these same fixed cutoffs.

The source consumer is `RetainedAssembly.NormalizedMeanSource`, and the
cancellation consumer is `physicalDensityMean_uncorrected_core_cancellation`.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.PositiveBackground
open ContinuumRow CanonicalCarrier CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow.LeadingPrimitive RetainedAssembly.ExternalWeights

/-- Choose the original external weights and physical measurement radius
jointly on the SAME supplied retained family. The full detector projection,
any prescribed original compact plateau, the scalar domains, and the literal
factor-four synthesis are retained. The radius is fixed on the entire weight
support before any source-scale parameter enters the construction
(`app:ch_background:prop:bg-positive`, `app:ch_background:prop:bg-normalized`,
`new:sec:order-of-choices`).

This constructs the fixed geometric choices. The normalized row and its
uniform gap and inverse estimates must still be instantiated on these choices.
When weights are already selected, use `exists_fixed_weight_measurement_buffer`
instead of selecting them a second time. -/
theorem exists_retained_external_weights_and_measurement_buffer
    {n : ℕ} {A : Type*} [Fintype A]
    {P : A → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (h0U : (0 : Euclidean n) ∈ U)
    (T : (i : A) → PatchQuantitativeFamily (P i) U hU)
    (zCell zRoot : A → Euclidean 3) (ηb : A → Euclidean (n - 1))
    {L σcell τ r a rm am : A → ℝ}
    (hL : ∀ i, 0 < L i) (hσcell : ∀ i, 0 < σcell i)
    (hηb : ∀ i, ηb i ≠ 0) (hrm : ∀ i, 0 < rm i) (ham : ∀ i, 0 < am i)
    (hamr : ∀ i, am i ≤ rm i) (hrmr : ∀ i, rm i ≤ r i) (hama : ∀ i, am i ≤ a i)
    (E : A → Set (Euclidean n × CarrierParameter)) (hE : ∀ i, IsOpen (E i))
    (houter : ∀ i, coefficientDomain (zRoot i) (r i) (6 * a i) ⊆ E i)
    (hgraph : ∀ i, MapsTo (carrierGraph (T i)) (E i)
      (ball ((0 : Euclidean n), (zCell i, (T i).reference.spatialPatch (zCell i))) (σcell i)))
    (hworking : ∀ i,
      closedBall ((0 : Euclidean n), (zCell i, (T i).reference.spatialPatch (zCell i)))
          (2 * σcell i) ⊆
        (coordinates (adaptedCoordinates (T i).data.adapted)).symm ''
          (Icc (-τ i / 2) (τ i / 2) ×ˢ
            closedBall ((0 : Euclidean (n - 1)),
              (zCell i, (T i).reference.spatialPatch (zCell i))) (L i / 64)))
    (K₀ : A → Set CarrierParameter) (hK₀ : ∀ i, IsCompact (K₀ i))
    (hK₀E : ∀ i, K₀ i ⊆ carrierNeighborhood (E i)) {cap : ℝ} (hcap : 0 < cap) :
    ∃ χ : A → CarrierParameter → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧ (∀ i z, χ i z ∈ Icc (0 : ℝ) 1) ∧
      (∀ i, HasCompactSupport (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ carrierNeighborhood (E i)) ∧
      (∀ i, tsupport (χ i) ⊆ parameter ⁻¹' ball (zCell i) (L i / 8)) ∧
      (∀ i, K₀ i ∪ maskCarrierProjection (zRoot i) (ηb i) (rm i) (am i) ⊆
        interior {z | χ i z = 1}) ∧
      (∀ i, ContDiff ℝ ∞ (squaredCarrierWeight (χ i))) ∧
      (∀ i z, 0 ≤ squaredCarrierWeight (χ i) z) ∧
      (∀ i, tsupport (squaredCarrierWeight (χ i)) = tsupport (χ i)) ∧
      (∀ i, IsFiniteMeasure (squaredCarrierMeasure (χ i))) ∧
      (∀ i z η, angularMask (zRoot i) (NormedSpace.normalize (ηb i)) (ham i)
        (angularWidth_spec (hηb i) (hrm i)).1 z η ≠ 0 → χ i z = 1) ∧
      (∀ (N : ℕ) (d : A → CarrierData n N),
        (∀ i, (d i).angularCutoff = angularMask (zRoot i) (NormedSpace.normalize (ηb i))
          (ham i) (angularWidth_spec (hηb i) (hrm i)).1) →
        ∀ i (f : CarrierVariable n → ℂ) (p : CarrierVariable n),
          squaredCarrierWeight (χ i) p.1 * UncutDensity.initialDensity (d i) 4 f p =
            UncutDensity.initialDensity (d i) 4 f p) ∧
      ∃ (b : ℝ) (hb : 0 < b), 4 * b < 1 / 2 ∧ 6 * b < cap ∧ 6 * b < 1 / 2 ∧
        closedBall (0 : Euclidean n) (6 * b) ⊆ U ∧
        ∃ V : A → Set CarrierParameter,
          (∀ i, IsOpen (V i)) ∧ (∀ i, tsupport (χ i) ⊆ V i) ∧
          (∀ i, closedBall (0 : Euclidean n) (6 * b) ×ˢ V i ⊆ E i) ∧
          ∀ (i : A) (j : Fin 3),
            tsupport (FixedCutoffs.physical (n := n) hb j) ×ˢ tsupport (χ i) ⊆ E i := by
  obtain ⟨χ, hχ, hχrange, hcompact, hsupport, hscalar, hplateau,
    hweight, hnonneg, hweightsupport, hfinite, hmask, hdensity⟩ :=
    exists_externalWeights T zCell zRoot ηb hL hσcell hηb hrm ham hamr hrmr hama
      E hE houter hgraph hworking K₀ hK₀ hK₀E
  exact ⟨χ, hχ, hχrange, hcompact, hsupport, hscalar, hplateau,
    hweight, hnonneg, hweightsupport, hfinite, hmask, hdensity,
    exists_fixed_weight_measurement_buffer E hE χ hcompact hsupport hU h0U hcap⟩

end JanetCartan.PositiveBackground
