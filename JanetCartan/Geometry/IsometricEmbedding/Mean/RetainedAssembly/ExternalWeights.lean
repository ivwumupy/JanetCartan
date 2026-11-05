module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.RetainedAssembly.ExternalWeights.Measure

/-!
# External weights for the supplied retained scalar/detector family

This is the external-weight selection in `app:ch_background:prop:bg-positive`.
The supplied retained cells, scalar centers, scalar domains, incidence roots,
and conic mask radii are unchanged. The carrier projection is derived from
the full actual `conicMaskSupport`; the original working cylinder puts the
chosen support inside the original scalar domain even when the two centers
differ. The weights precede every immersion, initial scalar and raw density.

The geometric inputs are exported by `RetainedRowGeometry`'s common geometry
and the working-cylinder part of the supplied `ChartCenters.CarrierData`.
There is no inverse, coercivity, current-mean or density-estimate premise.
The parent must use these very weights in the supplied-weight source of
`RetainedAssembly.NormalizedMeanSource`, then in
`PositiveBackground.uncorrectedDensity_core_cancellation`. An already fixed
weight uses `fixedCutoff_*`; the existence theorem is used at the original
selection point, not to replace a weight after constructing its source.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RetainedAssembly.ExternalWeights
open ContinuumRow CanonicalCarrier CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow.LeadingPrimitive

variable {n N : ℕ}

/-- Select all external cutoffs on the SAME supplied retained family, from
its actual mask widths and scalar working cylinders. `K₀` allows the original
selection to preserve any already prescribed compact plateau (take `∅` if
none is prescribed). Both the projection's compactness and its containment
are proved from these data. The actual square is smooth, nonnegative, has
the same fixed support, and defines a finite measure. The final two clauses
give the precise plateau and factor-four absorption inputs to
`PositiveBackground.uncorrectedDensity_core_cancellation`
(`app:ch_background:prop:bg-positive`, `eq:bg-current-raising`,
`eq:bg-density-four`, `eq:bg-density-twice`). -/
theorem exists_externalWeights
    {A : Type*} {P : A → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : A) → PatchQuantitativeFamily (P i) U hU)
    (zCell zRoot : A → Euclidean 3) (ηb : A → Euclidean (n - 1))
    {L σ τ r a rm am : A → ℝ}
    (hL : ∀ i, 0 < L i) (hσ : ∀ i, 0 < σ i)
    (hηb : ∀ i, ηb i ≠ 0) (hrm : ∀ i, 0 < rm i) (ham : ∀ i, 0 < am i)
    (hamr : ∀ i, am i ≤ rm i) (hrmr : ∀ i, rm i ≤ r i) (hama : ∀ i, am i ≤ a i)
    (E : A → Set (Euclidean n × CarrierParameter)) (hE : ∀ i, IsOpen (E i))
    (houter : ∀ i, coefficientDomain (zRoot i) (r i) (6 * a i) ⊆ E i)
    (hgraph : ∀ i, MapsTo (carrierGraph (T i)) (E i)
      (ball ((0 : Euclidean n), (zCell i, (T i).reference.spatialPatch (zCell i))) (σ i)))
    (hworking : ∀ i,
      closedBall ((0 : Euclidean n), (zCell i, (T i).reference.spatialPatch (zCell i))) (2 * σ i) ⊆
        (coordinates (adaptedCoordinates (T i).data.adapted)).symm ''
          (Icc (-τ i / 2) (τ i / 2) ×ˢ
            closedBall ((0 : Euclidean (n - 1)),
              (zCell i, (T i).reference.spatialPatch (zCell i))) (L i / 64)))
    (K₀ : A → Set CarrierParameter) (hK₀ : ∀ i, IsCompact (K₀ i))
    (hK₀E : ∀ i, K₀ i ⊆ carrierNeighborhood (E i)) :
    ∃ χ : A → CarrierParameter → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i z, χ i z ∈ Icc (0 : ℝ) 1) ∧
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
      ∀ (N : ℕ) (d : A → CarrierData n N),
        (∀ i, (d i).angularCutoff = angularMask (zRoot i) (NormedSpace.normalize (ηb i))
          (ham i) (angularWidth_spec (hηb i) (hrm i)).1) →
        ∀ i (f : CarrierVariable n → ℂ) (p : CarrierVariable n),
          squaredCarrierWeight (χ i) p.1 * UncutDensity.initialDensity (d i) 4 f p =
            UncutDensity.initialDensity (d i) 4 f p := by
  classical
  choose χ hχ hχrange hχcompact hχE hχplateau using fun i ↦
    exists_externalCutoff_in_retained_cell (hηb i) (hrm i) (ham i) (hamr i) (hrmr i)
      (hama i) (hE i) (houter i) (hK₀ i) (hK₀E i)
  have hp i : maskCarrierProjection (zRoot i) (ηb i) (rm i) (am i) ⊆
      interior {z | χ i z = 1} := (subset_union_right).trans (hχplateau i)
  refine ⟨χ, hχ, hχrange, hχcompact, hχE, ?_, hχplateau,
    fun i ↦ squaredCarrierWeight_contDiff (hχ i), fun i z ↦ squaredCarrierWeight_nonneg (χ i) z,
    fun i ↦ squaredCarrierWeight_tsupport (χ i),
    fun i ↦ squaredCarrierMeasure_finite (hχ i) (hχcompact i), ?_, ?_⟩
  · intro i
    exact (hχE i).trans (carrierNeighborhood_subset_original_scalar_domain (T i) (zCell i)
      (hL i) (hσ i) (hgraph i) (hworking i))
  · intro i z η h
    exact fixedCutoff_one_of_angularMask (hηb i) (hrm i) (ham i) (χ i) (hp i) h
  · intro N d hd i f p
    exact fixedCutoff_sq_mul_initialDensity (hηb i) (hrm i) (ham i) (χ i) (hp i)
      (d i) (hd i) f p

/-- Specialize the plateau product to the literal `CanonicalCarrier.data`
used by `RetainedFrozen.Row`. The measurement radius `b` is independent of
the mask width, so this applies to both the local and common-measurement row.
All scalar/ODE maps, the original initial variables, the full angular mask,
the high-pass mask, and the real factor four are retained. Both real
quadratures are still represented by the same complex raw input
(`app:ch_background:eq:bg-density-four`, `eq:bg-realification`). -/
theorem fixedCutoff_sq_mul_canonical_initialDensity
    {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {rm am b : ℝ}
    (hηb : ηb ≠ 0) (hrm : 0 < rm) (ham : 0 < am)
    (χ : CarrierParameter → ℝ)
    (hplateau : maskCarrierProjection zRoot ηb rm am ⊆ interior {z | χ z = 1})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hb : 0 < b) (hcell : 4 * b < 1 / 2)
    (f : CarrierVariable n → ℂ) (p : CarrierVariable n) :
    let d := data T Q F row col Φ Y initial hb hcell
      (angularMask zRoot (NormedSpace.normalize ηb) ham (angularWidth_spec hηb hrm).1)
      FixedCutoffs.highFrequency
    χ p.1 ^ 2 * UncutDensity.initialDensity d 4 f p = UncutDensity.initialDensity d 4 f p :=
  fixedCutoff_sq_mul_initialDensity hηb hrm ham χ hplateau _ rfl f p

end JanetCartan.RetainedAssembly.ExternalWeights
