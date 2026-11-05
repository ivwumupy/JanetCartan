module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.FiniteIncidence
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.MultiplierComparison

/-!
# Construction of the finite frozen spectral gap

This is the finite-matrix assembly of `app:ch_background:prop:bg-frame` at
`new:lem:scaling`'s zero scale. The cover, minors, conic radii, inverse
reference maps and common frame threshold are chosen from the original fixed
data before the immersion. The constructed incidence roots, positive literal
weights and detection discharge the hypotheses of the compact-sphere gap
argument. The symbol retains the original Hamilton charts, canonical masks,
high cutoff, reflected integrals and Lebesgue spectator balls.

The initial-multiplier conclusion retains exactly the smoothness, flow-range,
initial-section and lower-bound hypotheses of `MultiplierComparison`.
`NullTransport.exists_projected_local_positive_amplitude` produces the flow
smoothness and range; the realization producer must match its initial section
to these same radii. `frozenInitial_sqrt_admissible_of_cNorm` supplies the
paper's square-root initial-data smoothness and lower bound. The theorem also
constructs the unit-amplitude spectral gap without any of these extra inputs.
The Hilbert-space carrier realization and its Fourier identity are separate
obligations; no existence of those operators is asserted here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol ConicChart
open ProjectedStressFrame

/-- Construct the literal finite frozen matrix and its uniform high-frequency
gap from the original finite cover and primitive immersion hypotheses. All
selected-root geometry, positive weights, detection, spectator integrability,
continuity and boundedness are proved. The common radius is the sum of the
actual inverse-comparison thresholds. The SAME measured coefficients satisfy
the full reflected-amplitude identity at physical frequency `2πξ`. A single
unit gap transfers with the exact factor `1/16` to every permitted initial
multiplier under its original flow and initial-data hypotheses. Consumer:
the same-model assembly in `FrozenModel` and its Fourier energy comparison
(`app:ch_background:prop:bg-frame`, `bg-full-complex-amplitude`). -/
theorem exists_finite_frozen_spectral_gap {n : ℕ} (hn : 5 ≤ n)
    {D : CoverData n} {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {b s : ℝ} (hBU : closedBall (0 : Euclidean n) b ⊆ U)
    (hframe : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      closedBall (0 : Euclidean n) b)
    (hs : 0 < s) (hsradius : ∀ i, 3 * s < (T i).physicalRadius) (hsb : 3 * s < b)
    (M : ℝ) {κmet κnormal cap : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hcap : 0 < cap) :
    ∃ R : IncidenceRefinement D, R.IsValid ∧
    ∃ (m : ℕ) (chart : Fin m → Fin R.chartCount) (center : Fin m → Euclidean n)
      (ρ : Fin m → ℝ),
    ∃ d : (l : Fin m) → (a : Fin (D.patchCount (R.sourceChart (chart l)))) →
      FrozenIncidencePatchData (T ⟨R.sourceChart (chart l), a⟩)
        (D.roots (R.sourceChart (chart l)) a (center l))
        ((T ⟨R.sourceChart (chart l), a⟩).data.adapted.embedding.toContinuousLinearMap.adjoint
          (center l)),
      (∀ l, center l ∈ sphere (0 : Euclidean n) 1) ∧
      (∀ l, 0 < ρ l) ∧
      (∀ l, ball (center l) (ρ l) ⊆ ball (R.center (chart l)) (R.radius (chart l))) ∧
      (sphere (0 : Euclidean n) 1 ⊆ ⋃ l, ball (center l) (ρ l)) ∧
      (∀ l a, 6 * (d l a).a < cap) ∧
      ∃ δ > (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm (closedBall (0 : Euclidean n) b) 4 F ≤ M →
        (∀ x ∈ closedBall (0 : Euclidean n) b, ∀ v,
          κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ closedBall (0 : Euclidean n) b, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        (∀ i, cNorm (closedBall (0 : Euclidean n) b) 6
          (fun x ↦ projectedStress F x i - cubeStress n i) < δ) →
        let hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
        ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
          (∀ l a, (d l a).Geometry ⟨projectedStress F, hQ, hlow ⟨R.sourceChart (chart l), a⟩⟩) ∧
          let I := (l : Fin m) × Fin (D.patchCount (R.sourceChart (chart l)))
          let source := fun i : I ↦ ⟨R.sourceChart (chart i.1), i.2⟩
          let T' := fun i : I ↦ T (source i)
          let d' := fun i : I ↦ d i.1 i.2
          let z₀ := fun i : I ↦ D.roots (source i).1 (source i).2 (center i.1)
          let ηb := fun i : I ↦ (T' i).data.adapted.embedding.toContinuousLinearMap.adjoint (center i.1)
          let Q' (i : I) : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
              cNorm (closedBall (0 : Euclidean n) (T' i).data.localReference.stateRadius) 6
                (Q - fun _ ↦ cubeStress n) < (T' i).family.threshold} :=
            ⟨projectedStress F, hQ, hlow (source i)⟩
          let u := fun i : I ↦ frozenSymbolInverse (T' i) (Q' i) (z₀ i) (ηb i) (d' i).r (6 * (d' i).a)
          let Ω := fun i : I ↦ frozenSymbolDomain (T' i) (Q' i) (z₀ i) (ηb i) (d' i).r (6 * (d' i).a)
          let J := fun i : I ↦ transportAbsoluteJacobian (adaptedSliceCoordinates (T' i))
            (normalizedTransportPosition (T' i) (Q' i) 0)
          let S := fun i : I ↦ closedBall (spectatorCenter (z₀ i)) ((d' i).a / 2)
          let R₀ := frozenFamilyHighFrequencyRadius T' (fun i ↦ (d' i).G)
          1 ≤ R₀ ∧
          ∀ (Φ Y : I → ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3),
          let coeff := fun initial i ↦ uncutFrozenCoefficients (T' i) (Q' i) F
            (d' i).row (d' i).col (Φ i) (Y i) (initial i)
            (angularMask (z₀ i) (NormedSpace.normalize (ηb i)) (d' i).ha
              (angularWidth_spec (d' i).hηb (d' i).hr).1) FixedCutoffs.highFrequency
          let carrier := fun initial i ↦ canonicalFrozenCarrierSymbol (T' i) (Q' i) F
            (d' i).row (d' i).col (Φ i) (Y i) (initial i) (z₀ i) (d' i).hηb (d' i).hr (d' i).ha
          let e := fun initial ↦ canonicalFrozenMatrixSymbol T' (projectedStress F) hQ
            (fun i ↦ hlow (source i)) F (fun i ↦ (d' i).row) (fun i ↦ (d' i).col) Φ Y initial
            z₀ ηb (fun i ↦ (d' i).r) (fun i ↦ (d' i).a)
            (fun i ↦ (d' i).hηb) (fun i ↦ (d' i).hr) (fun i ↦ (d' i).ha)
          (∀ i,
            (∀ p, Integrable (fun v ↦ extendedDensity (coeff (fun _ _ ↦ 1) i) (J i) (u i) (Ω i) (p, v))
              (volume.restrict (S i))) ∧
            Continuous (carrier (fun _ _ ↦ 1) i) ∧
            ∃ B ≥ (0 : ℝ), ∀ k, ‖carrier (fun _ _ ↦ 1) i k‖ ≤ B) ∧
          Continuous (e (fun _ _ ↦ 1)) ∧
          (∃ B ≥ (0 : ℝ), ∀ k, ‖e (fun _ _ ↦ 1) k‖ ≤ B) ∧
          (∀ initial k, (e initial k).PosSemidef) ∧
          (∀ initial (measurement : Euclidean n → ℝ) i x y ξ,
            fullReflectedMatrixAmplitude {(coeff initial i) with measurement := measurement}
              (J i) (u i) (Ω i) (S i) ξ (AmplitudeBound.pairedPosition x y) =
              (measurement x * measurement y) •
                (fun l q ↦ (carrier initial i ((2 * Real.pi) • ξ) l q : ℂ))) ∧
          ∃ γ > (0 : ℝ),
            (∀ k, R₀ ≤ ‖k‖ → ∀ v : Euclidean n,
              γ * ‖v‖ ^ 2 ≤ dotProduct (fun i ↦ v i) (e (fun _ _ ↦ 1) k *ᵥ (fun i ↦ v i))) ∧
            ∀ (initial : I → Euclidean (n - 1) × Euclidean 3 → ℝ)
              (initialDomain : I → Set (Euclidean (n - 1) × Euclidean 3))
              (flowDomain : I → Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
              (∀ i, ContDiffOn ℝ ∞ (initial i) (initialDomain i)) →
              (∀ i, ContDiffOn ℝ ∞ (Y i) (flowDomain i)) →
              (∀ i, MapsTo
                (fun z : CarrierParameter ↦ ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z)))
                (ball (z₀ i 0) (d' i).r ×ˢ ball (spectatorCenter (z₀ i)) (6 * (d' i).a))
                (flowDomain i)) →
              (∀ i, MapsTo (Y i) (flowDomain i) (initialDomain i)) →
              (∀ i, ∀ z ∈ carrierSupport (z₀ i) (r := (d' i).a),
                (1 / 2 : ℝ) ≤ initial i (Y i (0, (0, parameter z)))) →
              (∀ i,
                (∀ p, Integrable (fun v ↦ extendedDensity (coeff initial i) (J i) (u i) (Ω i) (p, v))
                  (volume.restrict (S i))) ∧
                Continuous (carrier initial i) ∧
                ∃ B ≥ (0 : ℝ), ∀ k, ‖carrier initial i k‖ ≤ B) ∧
              Continuous (e initial) ∧
              (∃ B ≥ (0 : ℝ), ∀ k, ‖e initial k‖ ≤ B) ∧
              ∀ k, R₀ ≤ ‖k‖ → ∀ v : Euclidean n,
                (γ / 16) * ‖v‖ ^ 2 ≤ dotProduct (fun i ↦ v i) (e initial k *ᵥ (fun i ↦ v i)) := by
  classical
  obtain ⟨R, hR, c, B, ε, δ, cdet, hc, hB, hε, hδ, hcdet, m, chart, center, ρ, d,
    hcenter, hρ, hchart, hcover, hcaproot, hconstruct⟩ :=
    exists_finite_frozen_incidence_inputs hn hD T hBU hframe hs hsradius hsb
      M hκmet hκnormal hcap
  refine ⟨R, hR, m, chart, center, ρ, d, hcenter, hρ, hchart, hcover,
    fun l a ↦ (hcaproot l a).1, δ, hδ, ?_⟩
  intro F hF hi hrank hM hmet hnormal hclose
  have hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  obtain ⟨hlow, g, hg, hgeom, active, z, hactive, hz, hroot, hdetect⟩ :=
    hconstruct F hF hi hrank hM hmet hnormal hclose
  refine ⟨hlow, hgeom, ?_⟩
  dsimp only
  let I := (l : Fin m) × Fin (D.patchCount (R.sourceChart (chart l)))
  let source (i : I) := (⟨R.sourceChart (chart i.1), i.2⟩ : (j : Fin D.chartCount) × Fin (D.patchCount j))
  let T' := fun i : I ↦ T (source i)
  let d' := fun i : I ↦ d i.1 i.2
  let z₀ := fun i : I ↦ D.roots (source i).1 (source i).2 (center i.1)
  let ηb := fun i : I ↦ (T' i).data.adapted.embedding.toContinuousLinearMap.adjoint (center i.1)
  let Q' (i : I) : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) (T' i).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T' i).family.threshold} :=
    ⟨projectedStress F, hQ, hlow (source i)⟩
  let G := fun i : I ↦ (d' i).G
  have hP (i : I) : (D.patches (source i).1 (source i).2).IsValid c₀ C₀ :=
    (hD.2.2.2.2.1 _ _).1
  have har (i : I) : 6 * (d' i).a ≤ 3 * (d' i).r := by
    have hh := (d' i).har
    have hr := (d' i).hr
    linarith
  have hf := fun i : I ↦ (hgeom i.1 i.2).1
  have hgap := fun i : I ↦ (hgeom i.1 i.2).2.1
  have hInv := fun i : I ↦ (hgeom i.1 i.2).2.2.1
  have htrans := fun i : I ↦ (hgeom i.1 i.2).2.2.2
  refine ⟨one_le_frozenFamilyHighFrequencyRadius T' G, ?_⟩
  intro Φ Y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨frozenExtendedDensity_unit_integrable (T' i) (Q' i) F (d' i).row (d' i).col
      (Φ i) (Y i) (hP i) (d' i).hηb (d' i).hr (d' i).ha (har i) (d' i).hcarrier
      (hf i) (hInv i) (htrans i) (d' i).hcJ (d' i).hV (d' i).hLV,
      canonicalFrozenCarrierSymbol_unit_continuous (T' i) (Q' i) F (d' i).row (d' i).col
        (Φ i) (Y i) (hP i) (d' i).hηb (d' i).hr (d' i).ha (har i) (d' i).hcarrier
        (hf i) (hInv i) (htrans i) (d' i).hcJ (d' i).hV (d' i).hLV,
      canonicalFrozenCarrierSymbol_unit_bounded (T' i) (Q' i) F (d' i).row (d' i).col
        (Φ i) (Y i) (hP i) (d' i).hηb (d' i).hr (d' i).ha (har i) (d' i).hcarrier
        (hf i) (hInv i) (htrans i) (d' i).hcJ⟩
  · exact canonicalFrozenMatrixSymbol_unit_continuous T' G (projectedStress F) hQ
      (fun i ↦ hlow (source i)) F (fun i ↦ (d' i).row) (fun i ↦ (d' i).col) Φ Y
      z₀ ηb (fun i ↦ (d' i).r) (fun i ↦ (d' i).a)
      (fun i ↦ (d' i).hηb) (fun i ↦ (d' i).hr) (fun i ↦ (d' i).ha)
      hP har (fun i ↦ (d' i).hcarrier) hf hInv htrans
      (fun i ↦ (d' i).hcJ) (fun i ↦ (d' i).hV) (fun i ↦ (d' i).hLV)
  · exact canonicalFrozenMatrixSymbol_unit_bounded T' G (projectedStress F) hQ
      (fun i ↦ hlow (source i)) F (fun i ↦ (d' i).row) (fun i ↦ (d' i).col) Φ Y
      z₀ ηb (fun i ↦ (d' i).r) (fun i ↦ (d' i).a)
      (fun i ↦ (d' i).hηb) (fun i ↦ (d' i).hr) (fun i ↦ (d' i).ha)
      hP har (fun i ↦ (d' i).hcarrier) hf hInv htrans (fun i ↦ (d' i).hcJ)
  · intro initial k
    exact canonicalFrozenMatrixSymbol_posSemidef T' (projectedStress F) hQ
      (fun i ↦ hlow (source i)) F (fun i ↦ (d' i).row) (fun i ↦ (d' i).col) Φ Y initial
      z₀ ηb (fun i ↦ (d' i).r) (fun i ↦ (d' i).a)
      (fun i ↦ (d' i).hηb) (fun i ↦ (d' i).hr) (fun i ↦ (d' i).ha) k
  · intro initial measurement i x y ξ
    exact fullReflectedMatrixAmplitude_frozen_measurement (T' i) (Q' i) F (d' i).row (d' i).col
      (Φ i) (Y i) (initial i)
      (angularMask (z₀ i) (NormedSpace.normalize (ηb i)) (d' i).ha
        (angularWidth_spec (d' i).hηb (d' i).hr).1) FixedCutoffs.highFrequency
      (adaptedSliceCoordinates (T' i)) measurement (hP i) (d' i).hηb (d' i).hr
      (har i) (d' i).hcarrier (hInv i) (htrans i)
      (closedBall (spectatorCenter (z₀ i)) ((d' i).a / 2)) x y ξ
  · have hroots k (hk : ‖k‖ = frozenFamilyHighFrequencyRadius T' G) i (hi : i ∈ active k) :=
      hroot k hk.ge i hi
    obtain ⟨γ, hγ, hunit⟩ := exists_canonicalFrozenMatrixSymbol_unit_gap_of_incidence
      T' G (projectedStress F) hQ (fun i ↦ hlow (source i)) F
      (fun i ↦ (d' i).row) (fun i ↦ (d' i).col) Φ Y z₀ ηb
      (fun i ↦ (d' i).r) (fun i ↦ (d' i).a)
      (fun i ↦ (d' i).hηb) (fun i ↦ (d' i).hr) (fun i ↦ (d' i).ha)
      hP har (fun i ↦ (d' i).hcarrier) hf hInv htrans
      (fun i ↦ (d' i).hcJ) (fun i ↦ (d' i).hV) (fun i ↦ (d' i).hLV) hgap
      active z (fun k hk i hi ↦ ⟨(hroots k hk i hi).1, (hroots k hk i hi).2.1,
        (hroots k hk i hi).2.2 (Φ i) (Y i) (fun _ ↦ 1) (by norm_num)⟩)
      (fun k hk ↦ hdetect k hk.ge)
    refine ⟨γ, hγ, hunit, ?_⟩
    intro initial initialDomain flowDomain hi hY hseed hYrange hlower
    have hreg (i : I) := canonicalFrozenCarrierSymbol_initial_regularity
      (T' i) (Q' i) F (d' i).row (d' i).col (Φ i) (Y i) (initial i)
      (hP i) (d' i).hηb (d' i).hr (d' i).ha (har i) (d' i).hcarrier
      (hf i) (hInv i) (htrans i) (d' i).hcJ (d' i).hV (d' i).hLV
      (hi i) (hY i) (hseed i) (hYrange i)
    refine ⟨hreg, ?_, ?_, ?_⟩
    · exact (frozenImageSymbol_continuous (projectedStress F 0)).add
        (continuous_finsetSum _ (fun i _ ↦ (hreg i).2.1))
    · choose B hB hb using fun i ↦ (hreg i).2.2
      refine ⟨‖pencilContinuousLinearMap (projectedStress F 0)‖ ^ 2 + ∑ i, B i,
        add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ ↦ hB i), fun k ↦ ?_⟩
      rw [canonicalFrozenMatrixSymbol_eq]
      exact (norm_add_le _ _).trans (add_le_add (frozenImageSymbol_norm_le (projectedStress F 0) k)
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ hb i k)))
    · intro k hk v
      have hcompare := canonicalFrozenMatrixSymbol_initial_quadratic_ge_unit
        T' G (projectedStress F) hQ (fun i ↦ hlow (source i)) F
        (fun i ↦ (d' i).row) (fun i ↦ (d' i).col) Φ Y z₀ ηb
        (fun i ↦ (d' i).r) (fun i ↦ (d' i).a)
        (fun i ↦ (d' i).hηb) (fun i ↦ (d' i).hr) (fun i ↦ (d' i).ha)
        hP har (fun i ↦ (d' i).hcarrier) hf hInv htrans
        (fun i ↦ (d' i).hcJ) (fun i ↦ (d' i).hV) (fun i ↦ (d' i).hLV)
        initial hi hY hseed hYrange hlower k v
      have hscaled := mul_le_mul_of_nonneg_left (hunit k hk v) (by norm_num : (0 : ℝ) ≤ 1 / 16)
      calc
        _ = (1 / 16 : ℝ) * (γ * ‖v‖ ^ 2) := by ring
        _ ≤ _ := hscaled.trans hcompare

end JanetCartan.ContinuumNormal.FrozenModel
