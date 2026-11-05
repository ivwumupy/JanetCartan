module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.RealizedAssembly
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.EnergyBound
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.MeasuredData

/-!
# The constructed finite frozen model and its Euclidean lower bound

For `app:ch_background:prop:bg-frame`, combine the actual finite incidence
construction with its literal supported carrier extensions and the proved
Euclidean Plancherel estimate. The masks, inverses, spectator balls, common
measurement, both quadratures and physical frequency `2πξ` are unchanged.
The image summand here is the ideal Euclidean frozen image energy. Its comparison
with the periodic source-masked image, absorption and exterior completion belong
to the consuming continuum-normal construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol TransportKernel ConicChart
open ProjectedStressFrame
open Pseudodifferential AmplitudeBound PeriodicLocalL2 CommonMeasurement EuclideanSupportGap

/-- The actual normalized unit-initial frozen model, its SAME finite family
of uncut carrier extensions, and the Euclidean energy bound of
`app:ch_background:prop:bg-frame`. Geometry and the common cutoff cap precede
the immersion. The positive spectral constant and explicit low-frequency loss
precede all data. The literal test action, unique extension, adjoint, full normal
and Fourier identities are conclusions of the construction. The last two bounds
hold for every real torus L² datum and its measured Euclidean zero extension.
No symbol-gap or successful-operator-construction premise is used. -/
theorem exists_finite_realized_frozen_model_energy {n : ℕ} (hn : 5 ≤ n)
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
          let carrier := fun initial i ↦ canonicalFrozenCarrierSymbol (T' i) (Q' i) F
            (d' i).row (d' i).col (Φ i) (Y i) (initial i) (z₀ i) (d' i).hηb (d' i).hr (d' i).ha
          let e := fun initial ↦ canonicalFrozenMatrixSymbol T' (projectedStress F) hQ
            (fun i ↦ hlow (source i)) F (fun i ↦ (d' i).row) (fun i ↦ (d' i).col) Φ Y initial
            z₀ ηb (fun i ↦ (d' i).r) (fun i ↦ (d' i).a)
            (fun i ↦ (d' i).hηb) (fun i ↦ (d' i).hr) (fun i ↦ (d' i).ha)
          Continuous (e (fun _ _ ↦ 1)) ∧
          (∃ B ≥ (0 : ℝ), ∀ k, ‖e (fun _ _ ↦ 1) k‖ ≤ B) ∧
          (∀ k, (e (fun _ _ ↦ 1) k).PosSemidef) ∧
          ∃ γ > (0 : ℝ),
            (∀ k, R₀ ≤ ‖k‖ → ∀ v : Euclidean n,
              γ * ‖v‖ ^ 2 ≤ dotProduct (fun i ↦ v i) (e (fun _ _ ↦ 1) k *ᵥ (fun i ↦ v i))) ∧
            let C_low := lowFrequencyConstant n γ R₀
            0 ≤ C_low ∧
            (∀ (f : Euclidean n → EuclideanSpace ℂ (Fin n)),
              Integrable f → MemLp f 2 volume →
              γ * (∫ x, ‖f x‖ ^ 2) - C_low * (∫ x, ‖f x‖) ^ 2 ≤
                euclideanFrozenEnergy (e (fun _ _ ↦ 1)) f) ∧
            (∀ (f : Euclidean n → EuclideanSpace ℂ (Fin n)), MemLp f 2 volume →
              ∀ K : Set (Euclidean n), MeasurableSet K → volume K ≠ ⊤ →
              (∀ᵐ x, x ∉ K → f x = 0) →
              (γ - C_low * (volume K).toReal) * (∫ x, ‖f x‖ ^ 2) ≤
                euclideanFrozenEnergy (e (fun _ _ ↦ 1)) f) ∧
            ∀ (μ : ℝ) (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2),
              (∀ i, 6 * μ < (d' i).a) →
              let data := fun i ↦ normalizedCarrierData (T' i) (Q' i) F (d' i).row (d' i).col
                (Φ i) (Y i) (fun _ ↦ 1) hμ hμcell
                (angularMask (z₀ i) (NormedSpace.normalize (ηb i)) (d' i).ha
                  (angularWidth_spec (d' i).hηb (d' i).hr).1) FixedCutoffs.highFrequency 0
              let a := fun i ↦ coefficientsOfCarrier (data i) (FixedCutoffs.physical hμ 1)
              ∃ (V : I → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
                (A : I → EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
                  EuclideanL2 n (EuclideanSpace ℂ (Fin n))),
                (∀ i,
                  (∀ v : carrierInitialTestSpace n,
                    V i (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral (data i) v.val) ∧
                  (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ (data i).outputChart → V i f x = 0) ∧
                  (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
                    (∀ v : carrierInitialTestSpace n,
                      W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral (data i) v.val) →
                    W = V i) ∧
                  (∀ w : ComplexOutputL2 n,
                    MemLp (carrierAdjointIntegral (data i) w) 2 (carrierMeasure n) ∧
                    (V i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (data i) w) ∧
                  (realQuadratureChannel (V i)).comp (realQuadratureChannel (V i)).adjoint =
                    realOutputCompression (transferOperator (A i)) ∧
                  (∀ (f : Euclidean n → EuclideanSpace ℂ (Fin n)) (hf : MemLp f 2 volume),
                    ContDiff ℝ ∞ f → HasCompactSupport f →
                    A i (hf.toLp f) =ᵐ[volume] fun x ↦ WithLp.toLp 2
                      (matrixFullAmplitudeOperator
                        (fun x y ξ ↦ fullReflectedMatrixAmplitude (a i) (J i) (u i) (Ω i) (S i)
                          ξ (pairedPosition x y)) (fun y j ↦ f y j) x)) ∧
                  (∀ ξ x y l q,
                    fullReflectedMatrixAmplitude (a i) (J i) (u i) (Ω i) (S i) ξ
                        (pairedPosition x y) l q =
                      (FixedCutoffs.physical hμ 1 x : ℂ) * (FixedCutoffs.physical hμ 1 y : ℂ) *
                        (carrier (fun _ _ ↦ 1) i ((2 * Real.pi) • ξ) l q : ℂ)) ∧
                  ∀ w : OutputL2 n, ‖(realQuadratureChannel (V i)).adjoint w‖ ^ 2 =
                    euclideanFrozenEnergy (carrier (fun _ _ ↦ 1) i)
                      (fun x ↦ euclideanComplexInclusion
                        (FixedCutoffs.physical hμ 1 x • toEuclidean (𝕜 := ℝ) w x))) ∧
                ∀ w : OutputL2 n,
                  let measured := fun x ↦ FixedCutoffs.physical hμ 1 x • toEuclidean (𝕜 := ℝ) w x
                  let f := fun x ↦ euclideanComplexInclusion (measured x)
                  let energy := euclideanFrozenEnergy (frozenImageSymbol (projectedStress F 0)) f +
                    ∑ i, ‖(realQuadratureChannel (V i)).adjoint w‖ ^ 2
                  euclideanFrozenEnergy (e (fun _ _ ↦ 1)) f = energy ∧
                  γ * (∫ x, ‖measured x‖ ^ 2) - C_low * (∫ x, ‖measured x‖) ^ 2 ≤ energy ∧
                  (γ - C_low * (volume (ball (0 : Euclidean n) (3 * μ))).toReal) *
                    (∫ x, ‖measured x‖ ^ 2) ≤ energy := by
  classical
  obtain ⟨R, hR, m, chart, center, ρ, scale, d, hcell, hscale,
    hcenter, hρ, hchart, hcover, hcap', μ₀, hμ₀, hμ₀cell, hμ₀a, δ, hδ, hfamily⟩ :=
    exists_finite_realized_frozen_spectral_gap hn hD T hBU hframe hs hsradius hsb
      M hκmet hκnormal hcap
  refine ⟨R, hR, m, chart, center, ρ, scale, d, hcell, hscale,
    hcenter, hρ, hchart, hcover, hcap', μ₀, hμ₀, hμ₀cell, hμ₀a, δ, hδ, ?_⟩
  intro F hF hi hrank hM hmet hnormal hclose
  obtain ⟨hlow, hgeom, hreal, hrest⟩ := hfamily F hF hi hrank hM hmet hnormal hclose
  refine ⟨hlow, hgeom, hreal, ?_⟩
  dsimp only at hrest ⊢
  obtain ⟨hR₀, hmodels⟩ := hrest
  refine ⟨hR₀, ?_⟩
  intro Φ Y
  obtain ⟨hconstruct, _hreg, hecont, hebound, hsum, hnonneg, _hsep,
    γ, hγ, hgap, _hmult⟩ := hmodels Φ Y
  obtain ⟨B, hB, hbound⟩ := hebound
  refine ⟨hecont, ⟨B, hB, hbound⟩, hnonneg (fun _ _ ↦ 1), γ, hγ, hgap, ?_⟩
  have hlow_energy := euclideanFrozenEnergy_ge_sub_low_frequency _ hecont hγ.le hbound
    (hnonneg (fun _ _ ↦ 1)) hgap
  have hsupport_energy := euclideanFrozenEnergy_ge_support_volume_of_memLp _ hecont hγ.le hbound
    (hnonneg (fun _ _ ↦ 1)) hgap
  refine ⟨lowFrequencyConstant_nonneg hγ.le, hlow_energy, hsupport_energy, ?_⟩
  intro μ hμ hμcell hμa
  choose V A htest hsupp huniq hadj hnormal haction hamp henergy using
    hconstruct μ hμ hμcell hμa
  refine ⟨V, A, fun i ↦ ⟨htest i, hsupp i, huniq i, hadj i, hnormal i, haction i,
    hamp i, henergy i⟩, ?_⟩
  intro w
  obtain ⟨hf, hf₂, hfsupp⟩ := frozen_measured_zero_extension_integrable_memLp_support hμ w
  have hid := hsum _ hf hf₂
  simp_rw [← henergy] at hid
  refine ⟨hid, ?_, ?_⟩
  · have hh := hlow_energy _ hf hf₂
    rw [hid] at hh
    simpa only [euclideanComplexInclusion_norm] using hh
  · have hh := hsupport_energy _ hf₂ (ball 0 (3 * μ)) measurableSet_ball
      measure_ball_lt_top.ne (Filter.Eventually.of_forall hfsupp)
    rw [hid] at hh
    simpa only [euclideanComplexInclusion_norm] using hh

end JanetCartan.ContinuumNormal.FrozenModel
