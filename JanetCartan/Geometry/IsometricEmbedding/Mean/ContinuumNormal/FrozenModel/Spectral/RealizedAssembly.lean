module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.RealizedIncidence.FiniteCover
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.CommonMeasurement
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.RealizedAssembly.Energy
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.MultiplierComparison

/-!
# Spectral gap and Fourier realization for the same finite frozen family

This assembles the frozen step of `app:ch_background:prop:bg-frame` and
`new:lem:scaling` for the actual locally realized masks. The unit sphere centers
are retained for incidence detection; their small radial representatives select
the conic inverses. All shrinking precedes the finite subcover. The geometric
frequency threshold, matrix gap, literal carrier extensions and common-measurement
Fourier identities consequently refer to identical masks and spectator balls.

The common measurement radius is chosen before the immersion. The conclusion
also permits every further positive radius that fits all retained angular radii,
so the outer coercivity construction can shrink it after obtaining the gap.
Nonconstant initial multipliers retain their exact flow, range, smoothness and
lower-bound hypotheses; the unconditional operator conclusion here is for the
unit initial amplitude.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol TransportKernel ConicChart
open ProjectedStressFrame
open Pseudodifferential AmplitudeBound PeriodicLocalL2 CommonMeasurement

/-- Construct the finite frozen spectral gap and its SAME literal carrier
realizations from the original immersion hypotheses. The geometry, incidence
weights and detection are instantiated from the realized finite cover. The
common-measurement operators have the original Lebesgue test action, unique
extension, literal adjoint, full reflected normal and exact Euclidean Fourier
energy. Both quadratures, factor four, reflection and `k = 2πξ` are retained.
Every permitted positive initial multiplier has the gap divided by `16`, under
its original analytic hypotheses. Consumer: the frozen continuum-model
coercivity assembly (`app:ch_background:prop:bg-frame`,
`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem exists_finite_realized_frozen_spectral_gap {n : ℕ} (hn : 5 ≤ n)
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
    ∃ scale : (l : Fin m) → Fin (D.patchCount (R.sourceChart (chart l))) → ℝ,
    ∃ d : (l : Fin m) → (a : Fin (D.patchCount (R.sourceChart (chart l)))) →
      FrozenIncidencePatchData (T ⟨R.sourceChart (chart l), a⟩)
        (D.roots (R.sourceChart (chart l)) a (center l))
        ((T ⟨R.sourceChart (chart l), a⟩).data.adapted.embedding.toContinuousLinearMap.adjoint
          (scale l a • center l)),
    ∃ hcell : ∀ l a, 4 * (d l a).a < 1 / 2,
      (∀ l a, 0 < scale l a ∧ ‖scale l a • center l‖ = 1 / 4 ∧
        NormedSpace.normalize (scale l a • center l) = NormedSpace.normalize (center l) ∧
        NormedSpace.normalize
          ((T ⟨R.sourceChart (chart l), a⟩).data.adapted.embedding.toContinuousLinearMap.adjoint
            (scale l a • center l)) =
        NormedSpace.normalize
          ((T ⟨R.sourceChart (chart l), a⟩).data.adapted.embedding.toContinuousLinearMap.adjoint
            (center l))) ∧
      (∀ l, center l ∈ sphere (0 : Euclidean n) 1) ∧
      (∀ l, 0 < ρ l) ∧
      (∀ l, ball (center l) (ρ l) ⊆ ball (R.center (chart l)) (R.radius (chart l))) ∧
      (sphere (0 : Euclidean n) 1 ⊆ ⋃ l, ball (center l) (ρ l)) ∧
      (∀ l a, 6 * (d l a).a < cap) ∧
      ∃ μ₀ > (0 : ℝ), 4 * μ₀ < 1 / 2 ∧ (∀ l a, 6 * μ₀ < (d l a).a) ∧
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
          (∀ l a, (d l a).UnitRealization
            ⟨projectedStress F, hQ, hlow ⟨R.sourceChart (chart l), a⟩⟩ F (hcell l a)) ∧
          let I := (l : Fin m) × Fin (D.patchCount (R.sourceChart (chart l)))
          let source := fun i : I ↦ ⟨R.sourceChart (chart i.1), i.2⟩
          let T' := fun i : I ↦ T (source i)
          let d' := fun i : I ↦ d i.1 i.2
          let z₀ := fun i : I ↦ D.roots (source i).1 (source i).2 (center i.1)
          let ηb := fun i : I ↦ (T' i).data.adapted.embedding.toContinuousLinearMap.adjoint (scale i.1 i.2 • center i.1)
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
          (∀ (μ : ℝ) (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2),
            (∀ i, 6 * μ < (d' i).a) → ∀ i,
            let data := normalizedCarrierData (T' i) (Q' i) F (d' i).row (d' i).col
              (Φ i) (Y i) (fun _ ↦ 1) hμ hμcell
              (angularMask (z₀ i) (NormedSpace.normalize (ηb i)) (d' i).ha
                (angularWidth_spec (d' i).hηb (d' i).hr).1) FixedCutoffs.highFrequency 0
            let a := coefficientsOfCarrier data (FixedCutoffs.physical hμ 1)
            ∃ (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
              (A : EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
                EuclideanL2 n (EuclideanSpace ℂ (Fin n))),
              (∀ v : carrierInitialTestSpace n,
                V (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral data v.val) ∧
              (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ data.outputChart → V f x = 0) ∧
              (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
                (∀ v : carrierInitialTestSpace n,
                  W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral data v.val) → W = V) ∧
              (∀ w : ComplexOutputL2 n,
                MemLp (carrierAdjointIntegral data w) 2 (carrierMeasure n) ∧
                V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral data w) ∧
              (realQuadratureChannel V).comp (realQuadratureChannel V).adjoint =
                realOutputCompression (transferOperator A) ∧
              (∀ (f : Euclidean n → EuclideanSpace ℂ (Fin n)) (hf : MemLp f 2 volume),
                ContDiff ℝ ∞ f → HasCompactSupport f →
                A (hf.toLp f) =ᵐ[volume] fun x ↦ WithLp.toLp 2
                  (matrixFullAmplitudeOperator
                    (fun x y ξ ↦ fullReflectedMatrixAmplitude a (J i) (u i) (Ω i) (S i)
                      ξ (pairedPosition x y)) (fun y j ↦ f y j) x)) ∧
              (∀ ξ x y l q,
                fullReflectedMatrixAmplitude a (J i) (u i) (Ω i) (S i) ξ (pairedPosition x y) l q =
                  (FixedCutoffs.physical hμ 1 x : ℂ) * (FixedCutoffs.physical hμ 1 y : ℂ) *
                    (carrier (fun _ _ ↦ 1) i ((2 * Real.pi) • ξ) l q : ℂ)) ∧
              ∀ w : OutputL2 n, ‖(realQuadratureChannel V).adjoint w‖ ^ 2 =
                euclideanFrozenEnergy (carrier (fun _ _ ↦ 1) i)
                  (fun x ↦ euclideanComplexInclusion
                    (FixedCutoffs.physical hμ 1 x • toEuclidean (𝕜 := ℝ) w x))) ∧
          (∀ i,
            (∀ p, Integrable (fun v ↦ extendedDensity (coeff (fun _ _ ↦ 1) i) (J i) (u i) (Ω i) (p, v))
              (volume.restrict (S i))) ∧
            Continuous (carrier (fun _ _ ↦ 1) i) ∧
            ∃ B ≥ (0 : ℝ), ∀ k, ‖carrier (fun _ _ ↦ 1) i k‖ ≤ B) ∧
          Continuous (e (fun _ _ ↦ 1)) ∧
          (∃ B ≥ (0 : ℝ), ∀ k, ‖e (fun _ _ ↦ 1) k‖ ≤ B) ∧
          (∀ f : Euclidean n → EuclideanSpace ℂ (Fin n),
            Integrable f → MemLp f 2 volume →
            euclideanFrozenEnergy (e (fun _ _ ↦ 1)) f =
              euclideanFrozenEnergy (frozenImageSymbol (projectedStress F 0)) f +
                ∑ i, euclideanFrozenEnergy (carrier (fun _ _ ↦ 1) i) f) ∧
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
  obtain ⟨R, hR, c, B, εmax, ε, δ, cdet, hc, hB, hemax, hε, hδ, hcdet,
    m, chart, center, ρ, scale, d, hcell, hscale,
    hcenter, hρ, hchart, hcover, hradpatch, hcaproot, hconstruct⟩ :=
    exists_finite_realized_frozen_incidence_inputs hn hD T hBU hframe hs hsradius hsb
      M hκmet hκnormal hcap
  let I := (l : Fin m) × Fin (D.patchCount (R.sourceChart (chart l)))
  obtain ⟨μpatch, hμpatch, hμpatchi⟩ := Pi.exists_forall_pos_add_lt
    (fun i : I ↦ (d i.1 i.2).ha)
  let μ₀ := min (μpatch / 12) (1 / 16)
  have hμ₀ : 0 < μ₀ := lt_min (by positivity) (by norm_num)
  have hμcell : 4 * μ₀ < 1 / 2 := by
    have := min_le_right (μpatch / 12) (1 / 16 : ℝ)
    dsimp only [μ₀]
    linarith
  have hμa (l) (a) : 6 * μ₀ < (d l a).a := by
    have := hμpatchi (⟨l, a⟩ : I)
    have := min_le_left (μpatch / 12) (1 / 16 : ℝ)
    dsimp only [μ₀]
    linarith
  refine ⟨R, hR, m, chart, center, ρ, scale, d, hcell, hscale,
    hcenter, hρ, hchart, hcover, fun l a ↦ (hcaproot l a).1,
    μ₀, hμ₀, hμcell, hμa, δ, hδ, ?_⟩
  intro F hF hi hrank hM hmet hnormal hclose
  have hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  obtain ⟨hlow, g, hg, hgeom, hreal, active, z, hactive, hz, hroot, hdetect⟩ :=
    hconstruct F hF hi hrank hM hmet hnormal hclose
  refine ⟨hlow, hgeom, hreal, ?_⟩
  dsimp only
  let source (i : I) := (⟨R.sourceChart (chart i.1), i.2⟩ : (j : Fin D.chartCount) × Fin (D.patchCount j))
  let T' := fun i : I ↦ T (source i)
  let d' := fun i : I ↦ d i.1 i.2
  let z₀ := fun i : I ↦ D.roots (source i).1 (source i).2 (center i.1)
  let ηb := fun i : I ↦ (T' i).data.adapted.embedding.toContinuousLinearMap.adjoint (scale i.1 i.2 • center i.1)
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
  have hreg (i : I) :=
    And.intro
      (frozenExtendedDensity_unit_integrable (T' i) (Q' i) F (d' i).row (d' i).col
        (Φ i) (Y i) (hP i) (d' i).hηb (d' i).hr (d' i).ha (har i) (d' i).hcarrier
        (hf i) (hInv i) (htrans i) (d' i).hcJ (d' i).hV (d' i).hLV)
      (And.intro
        (canonicalFrozenCarrierSymbol_unit_continuous (T' i) (Q' i) F (d' i).row (d' i).col
          (Φ i) (Y i) (hP i) (d' i).hηb (d' i).hr (d' i).ha (har i) (d' i).hcarrier
          (hf i) (hInv i) (htrans i) (d' i).hcJ (d' i).hV (d' i).hLV)
        (canonicalFrozenCarrierSymbol_unit_bounded (T' i) (Q' i) F (d' i).row (d' i).col
          (Φ i) (Y i) (hP i) (d' i).hηb (d' i).hr (d' i).ha (har i) (d' i).hcarrier
          (hf i) (hInv i) (htrans i) (d' i).hcJ))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro μ hμ hμcell hμa i
    obtain ⟨_, V, A, _, _, _, _, _, _, htest, hsupp, hunique, hadj,
      hnormal, haction, hsep, henergy⟩ :=
      (d' i).exists_common_measurement_realization (Q' i) F (Φ i) (Y i) (hcell i.1 i.2)
        (hP i) (hgeom i.1 i.2) (hreal i.1 i.2) hμ (hμa i)
    exact ⟨restrictCarrier (FixedCutoffs.periodic hμ hμcell 1) V,
      (freezingVectorPhysicalMultiplier (FixedCutoffs.physical hμ 1)
        (FixedCutoffs.physical hμ 1).continuous (FixedCutoffs.physical hμ 1).hasCompactSupport) ∘L A ∘L
      (freezingVectorPhysicalMultiplier (FixedCutoffs.physical hμ 1)
        (FixedCutoffs.physical hμ 1).continuous (FixedCutoffs.physical hμ 1).hasCompactSupport),
      htest, hsupp, hunique, hadj, hnormal, haction, hsep, henergy _ htest⟩
  · exact hreg
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
  · intro f hfi hf₂
    choose B _ hB using fun i ↦ (hreg i).2.2
    exact euclideanFrozenEnergy_image_add_sum (projectedStress F 0) _
      (fun i ↦ (hreg i).2.1) B hB f hfi hf₂
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
