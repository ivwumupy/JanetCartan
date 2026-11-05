module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.ConstructedSeedMatching

/-!
# Matched normalized means on a prescribed retained history menu

The relative form of `app:ch_background:prop:bg-normalized` used by
`ReferenceInitialization.NormalizedHistory`: the original source and Hamilton
menu are supplied before the seed is selected. The primitive frozen gap comes
from `exists_transverse_retained_seed_family`; the mean, scalar transports and
positive-scale chart matching are constructed on that very menu.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric MeasureTheory
open scoped ContDiff Matrix Matrix.Norms.Frobenius JanetCartan.TensorFrobenius InnerProductSpace

namespace JanetCartan.ReferenceInitialization.NormalizedHistory
open NormalizedBackground ActualCarriers FrozenMenu FrozenPhaseReference CurrentFullPhase ProjectedStressFrame
open HamiltonPhase ContinuumRow
open ContinuumNormal.CarrierVariation.FamilyInputs
open NullTransport ActualFlow FlowAmplitude NormalizedBackground.SourceGeometry

/-- `main:prop:seed` and `app:ch_background:prop:bg-normalized`: construct
unit transports, the Lebesgue normalized mean and literal source-matched
scalars/charts for a prescribed original flat source and retained finite menu.
The arbitrary cap can therefore already include the history and extension
caps for this menu. No independent existential family is identified.
The proof uses the same relative mean and scalar-uniqueness leaves as
`NormalizedBackground.exists_constructed_flat_seed_matched_mean`. -/
theorem exists_relative_matched_seed_mean {n : ℕ} (hn : 5 ≤ n)
    (G₀ : FlatReference n) (D₀ : CoverData n) {c₀ C₀ : ℝ} (hD : D₀.IsValid c₀ C₀)
    {Rsource : ℝ} (hsource : ball (0 : Euclidean n) Rsource ⊆ G₀.domain.chart n)
    (T : (i : (j : Fin D₀.chartCount) × Fin (D₀.patchCount j)) →
      PatchQuantitativeFamily (D₀.patches i.1 i.2) (ball 0 Rsource) isOpen_ball)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ ball 0 Rsource)
    (hball : ∀ i, closedBall (0 : Euclidean n)
      (T i).data.localReference.stateRadius ⊆ K)
    {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ i, ∀ q ∈ closedBall (0, (T i).data.center)
      (T i).data.localReference.stateRadius,
      γ ≤ |⟪(frozenSymbol n).hp q, (T i).data.adapted.normal⟫_ℝ|)
    {cap : ℝ} (hcap : 0 < cap) :
        ∃ θ : ℝ, 0 < θ ∧ θ < cap ∧ θ ≤ 1 ∧
          ∃ G : FlatReference n, G.domain = G₀.domain ∧ G.map = sourceDilation G₀.map θ ∧
          ∃ hQ : ContDiffOn ℝ ∞ (projectedStress G.map) (ball (0 : Euclidean n) Rsource),
          ∃ hlow : ∀ a, cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
            (projectedStress G.map - fun _ ↦ cubeStress n) < (T a).family.threshold,
          ∃ centers : (a : ((j : Fin D₀.chartCount) × Fin (D₀.patchCount j))) → Finset (parameterCube (D₀.patches a.1 a.2).radius),
          ∃ radius : (a : ((j : Fin D₀.chartCount) × Fin (D₀.patchCount j))) → centers a → ℝ,
            (∀ a j, 0 < radius a j) ∧
            (∀ a, parameterCube (D₀.patches a.1 a.2).radius ⊆ ⋃ j : centers a,
              ball j.1.1 (radius a j / 4)) ∧
            ∃ ε : ℝ, 0 < ε ∧ ball (0 : Euclidean n) (2 * ε) ⊆ G.domain.chart n ∧
            (∀ a, 2 * ε < (T a).physicalRadius) ∧
            let I := (a : ((j : Fin D₀.chartCount) × Fin (D₀.patchCount j))) × centers a
            let Q := fun a ↦ (⟨projectedStress G.map, hQ, hlow a⟩ :
              {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) Rsource) ∧
                cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
                  (Q - fun _ ↦ cubeStress n) < (T a).family.threshold})
            (∀ a,
              (∀ z ∈ closedBall (0, (T a).data.center) (T a).data.localReference.stateRadius,
                ⟪(normalizedHomogeneousSymbol isOpen_ball (Q a).1 (Q a).2.1).hp z,
                  (T a).data.adapted.normal⟫_ℝ ≠ 0) ∧
              ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
                ∃ Qσ : {Q : Euclidean n → Fin n → MetricTensor n //
                    ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) Rsource) ∧
                    cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
                      (Q - fun _ ↦ cubeStress n) < (T a).family.threshold},
                  Qσ.1 = projectedStress (sourceDilation G.map σ) ∧
                  EqOn ((T a).currentChart Qσ).coordinates
                    (sourceCoordinates ((T a).currentChart (Q a)).coordinates σ) (T a).target ∧
                  EqOn (phase ((T a).currentChart Qσ).coordinates)
                    (sourcePhase (phase ((T a).currentChart (Q a)).coordinates) σ) (T a).target ∧
                  (∀ m : ℕ, EqOn (iteratedFDeriv ℝ m (phase ((T a).currentChart Qσ).coordinates))
                    (iteratedFDeriv ℝ m
                      (sourcePhase (phase ((T a).currentChart (Q a)).coordinates) σ)) (T a).target) ∧
                  (let S := fun p : Euclidean n × Euclidean (n - 1) ↦
                      phase ((T a).currentChart (Q a)).coordinates (p.1, (0, p.2))
                   let ζ := fun z ↦ (T a).reference.spatialPatch (CanonicalCarrier.parameter z)
                   let B := ball (0 : Euclidean n) (T a).physicalRadius ×ˢ
                     (CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * (D₀.patches a.1 a.2).radius))
                   EqOn (CanonicalCarrier.transportPosition (T a) Qσ)
                     (sourceTransportPosition S ζ σ) B ∧
                   ∀ m : ℕ, EqOn (iteratedFDeriv ℝ m (CanonicalCarrier.transportPosition (T a) Qσ))
                     (iteratedFDeriv ℝ m (sourceTransportPosition S ζ σ)) B) ∧
                  ∀ x ∈ ball (0 : Euclidean n) (T a).physicalRadius,
                    ∀ z ∈ parameterCube (2 * (D₀.patches a.1 a.2).radius),
                      (T a).carrier Qσ x z =
                        sourcePhase (fun p ↦ (T a).carrier (Q a) p.1 p.2) σ (x, z) ∧
                      (T a).carrierGradient Qσ x z = (T a).carrierGradient (Q a) (σ • x) z ∧
                      ∀ col, carrierNullvector (T a) Qσ col (x, z) =
                        carrierNullvector (T a) (Q a) col (σ • x, z) ) ∧
            let S := fun (j : I) (p : Euclidean n × Euclidean 3) ↦ (T j.1).carrier (Q j.1) p.1 p.2
            let ξ := fun (j : I) (p : Euclidean n × Euclidean 3) ↦
              (T j.1).carrierGradient (Q j.1) p.1 p.2
            let V := fun j : I ↦ ball j.2.1.1 (radius j.1 j.2 / 2)
            let Kc := fun j : I ↦ closedBall j.2.1.1 (radius j.1 j.2 / 4)
            ∃ b : I → Euclidean n × Euclidean 3 → Euclidean n,
            (∀ j : I,
            let T := T j.1
            let P := D₀.patches j.1.1 j.1.2
            let Q := Q j.1
            let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
            let z := j.2.1.1
            let r := radius j.1 j.2
            ∃ row col : Fin n, ∃ τ R : ℝ, 0 < τ ∧ 0 < R ∧
            ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
            ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
              b j = (fun w ↦ carrierScalarAmplitude T Q G.map row col Φ Y (fun _ ↦ 1) w •
                carrierNullvector T Q col w) ∧
              (ball (0 : Euclidean n) (2 * ε) ×ˢ ball z (r / 2) ⊆ C ⁻¹' D) ∧
              IsOpen D ∧
              Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 32) ⊆ D ∧
              C ⁻¹' D ⊆ (ball (0 : Euclidean n) Rsource) ×ˢ parameterInterior (3 * P.radius / 2) ∧
              D ⊆ Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4) ∧
              ContDiffOn ℝ ∞ Φ (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
              ContDiffOn ℝ ∞ Y D ∧
              MapsTo (fun q ↦ (q.1, Φ q))
                (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) D ∧
              MapsTo (fun q ↦ (q.1, Y q)) D
                (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
              (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), Φ (0, p) = p) ∧
              (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), ∀ t ∈ Ioo (-τ) τ,
                Y (t, Φ (t, p)) = p) ∧
              (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
              (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), ∀ t ∈ Ioo (-τ) τ,
                (Φ (t, p)).2 = p.2) ∧
              (∀ q ∈ D, (Y q).2 = q.2.2) ∧
              (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), ∀ t ∈ Ioo (-τ) τ,
                HasDerivAt (fun s ↦ Φ (s, p))
                  ((adaptedCoordinates T.data.adapted
                    (carrierTransportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
              let α := carrierScalarAmplitude T Q G.map row col Φ Y (fun _ ↦ 1)
              ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
              ContDiffOn ℝ ∞ (fun w ↦ α w • carrierNullvector T Q col w) (C ⁻¹' D) ∧
              (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8),
                α (T.data.adapted.embedding p.1, p.2) = 1) ∧
              (∀ w ∈ C ⁻¹' D, 0 < α w ∧ α w • carrierNullvector T Q col w ≠ 0) ∧
              (∀ w ∈ C ⁻¹' D,
                fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) +
                  carrierTransportPotential T Q G.map row col w * α w = 0) ∧
              (∀ w ∈ C ⁻¹' D,
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                  (fun j ↦ (α w • carrierNullvector T Q col w) j) = 0) ∧
              (∀ w ∈ C ⁻¹' D, carrierConullvector T Q row w ⬝ᵥ reducedOperator G.map Q.1
                (fun x ↦ α (x, w.2) • carrierNullvector T Q col (x, w.2)) w.1 = 0) ∧
              ContDiffOn ℝ ∞ (carrierNullvector T Q col) (C ⁻¹' D) ∧
              ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) (C ⁻¹' D) ∧
              ContDiffOn ℝ ∞ (carrierTransportPotential T Q G.map row col) (C ⁻¹' D) ∧
              (∀ w ∈ C ⁻¹' D, carrierAdaptedDenominator T Q row col w ≠ 0) ∧
              (∀ z₀ ∈ V j, ∃ R' τ' : ℝ, 0 < R' ∧ 0 < τ' ∧
                let I' := Ioo (-τ') τ'
                let L' := ball ((0 : Euclidean (n - 1)), z₀) (R' / 8)
                let W' := I' ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (R' / 32)
                ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
                  ∃ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) Rsource) ∧
                      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
                        (Q - fun _ ↦ cubeStress n) < T.family.threshold},
                    Qσ.1 = projectedStress (sourceDilation G.map σ) ∧
                    ∃ Dσ : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
                    ∃ Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
                      IsOpen Dσ ∧ W' ⊆ Dσ ∧ C ⁻¹' Dσ ⊆ C ⁻¹' D ∧
                      ContDiffOn ℝ ∞ Φσ (I' ×ˢ L') ∧ ContDiffOn ℝ ∞ Yσ Dσ ∧
                      MapsTo (fun q ↦ (q.1, Φσ q)) (I' ×ˢ L') Dσ ∧
                      MapsTo (fun q ↦ (q.1, Yσ q)) Dσ (I' ×ˢ L') ∧
                      (∀ p ∈ L', Φσ (0, p) = p) ∧
                      (∀ p ∈ L', ∀ t ∈ I', Yσ (t, Φσ (t, p)) = p) ∧
                      (∀ q ∈ Dσ, Φσ (q.1, Yσ q) = q.2) ∧
                      (∀ p ∈ L', ∀ t ∈ I', HasDerivAt (fun s ↦ Φσ (s, p))
                        ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Qσ row col
                          (C.symm (t, Φσ (t, p))))).2, 0) t) ∧
                      EqOn (carrierScalarAmplitude T Qσ (sourceDilation G.map σ) row col Φσ Yσ (fun _ ↦ σ))
                        (sourceAmplitude α σ) (C ⁻¹' Dσ) ∧
                      EqOn (fun w ↦ carrierScalarAmplitude T Qσ (sourceDilation G.map σ)
                        row col Φσ Yσ (fun _ ↦ σ) w • carrierNullvector T Qσ col w)
                        (sourceAmplitude (b j) σ) (C ⁻¹' Dσ)) ∧
              (∃ δ > (0 : ℝ), ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
                ∀ x ∈ ball (0 : Euclidean n) δ, ∀ z' ∈ Kc j,
                  ∃ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) Rsource) ∧
                      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
                        (Q - fun _ ↦ cubeStress n) < T.family.threshold},
                    Qσ.1 = projectedStress (sourceDilation G.map σ) ∧
                    ∃ Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
                      carrierScalarAmplitude T Qσ (sourceDilation G.map σ) row col Φσ Yσ (fun _ ↦ σ) (x, z') =
                        sourceAmplitude α σ (x, z') ∧
                      carrierScalarAmplitude T Qσ (sourceDilation G.map σ) row col Φσ Yσ (fun _ ↦ σ) (x, z') •
                        carrierNullvector T Qσ col (x, z') = sourceAmplitude (b j) σ (x, z')) ∧
              ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
                ∃ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) Rsource) ∧
                    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
                      (Q - fun _ ↦ cubeStress n) < T.family.threshold},
                  Qσ.1 = projectedStress (sourceDilation G.map σ) ∧
                  (∀ u z', (σ • u, z') ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8) →
                    sourceAmplitude α σ (T.data.adapted.embedding u, z') = σ) ∧
                  ∀ x ∈ ball (0 : Euclidean n) (2 * ε), ∀ z' ∈ V j,
                    sourceAmplitude (b j) σ (x, z') =
                      sourceAmplitude α σ (x, z') • carrierNullvector T Qσ col (x, z') ∧
                    0 < sourceAmplitude α σ (x, z') ∧
                    sourceAmplitude (b j) σ (x, z') ≠ 0 ∧
                    reducedSymbol (Qσ.1 x) (T.carrierGradient Qσ x z') *ᵥ
                      (fun k ↦ sourceAmplitude (b j) σ (x, z') k) = 0 ∧
                    carrierConullvector T Qσ row (x, z') ⬝ᵥ
                      reducedOperator (sourceDilation G.map σ) Qσ.1
                        (fun y ↦ sourceAmplitude (b j) σ (y, z')) x = 0) ∧
            ∀ (w : I → Euclidean 3 → ℝ),
              (∀ j, ContDiffOn ℝ ∞ (w j) (V j)) → (∀ j z, 0 ≤ w j z) →
              (∀ j z, z ∉ Kc j → w j z = 0) →
              ∀ (D : Set (Euclidean n)), IsCompact D →
              let μ := fun _ : I ↦ (volume : Measure (Euclidean 3))
              let ν := fun j p ↦ LeadingWave.principalNormal
                (AmbientResponse.canonicalNormalCompletion G.map p.1) (ξ j p) (b j p)
              let J := fun j q ↦ (normalizedPullback (b j) q,
                normalizedPullback (ξ j) q, normalizedPullback (ν j) q)
              ∃ B : Set (Euclidean n), IsOpen B ∧ D ⊆ B ∧ ∃ ρ₀ > 0, ρ₀ ≤ 1 ∧
                (∀ j, ContDiffOn ℝ ∞ (J j) (Ioo (-2 * ρ₀) (2 * ρ₀) ×ˢ B ×ˢ V j) ∧
                  ContDiffOn ℝ ∞ (sourcePhaseExtension (S j))
                    (Ioo (-2 * ρ₀) (2 * ρ₀) ×ˢ B ×ˢ V j)) ∧
                (∃ c > 0, ∀ j, ∀ ρ ∈ Icc (0 : ℝ) ρ₀, ∀ x ∈ D, ∀ z ∈ Kc j,
                  c ≤ ‖normalizedPullback (ν j) (ρ, (x, z))‖) ∧
                (carrierMean μ w ν ξ 0).PosSemidef ∧
                (∀ ρ ∈ Ioc (0 : ℝ) ρ₀, ∀ x ∈ B,
                  sourcePrincipalMean G.map μ w S b ρ x = normalizedCarrierMean μ w ν ξ ρ x ∧
                  PositiveBackground.referenceMeanResidual (sourceDilation G.map ρ)
                    (carrierMean μ w ν ξ 0) (sourcePrincipalMean G.map μ w S b ρ) x =
                    sourcePrincipalMean G.map μ w S b ρ x - carrierMean μ w ν ξ 0 ∧
                  ∀ j z, z ∈ V j → sourcePhase (S j) ρ (x, z) =
                    sourcePhaseExtension (S j) (ρ, (x, z))) ∧
                ∀ s : ℕ, ∃ C > 0, ∀ ρ ∈ Ioc (0 : ℝ) ρ₀,
                  cNorm D s (fun x ↦ sourcePrincipalMean G.map μ w S b ρ x -
                    carrierMean μ w ν ξ 0) ≤ C * ρ ∧
                  ∀ j x, x ∈ D → ∀ z ∈ Kc j,
                    ‖iteratedFDeriv ℝ s (J j) (ρ, (x, z))‖ ≤ C := by
  obtain ⟨κ, hκ, _, hmatch⟩ := exists_finite_retained_source_matching_scale G₀ T
    (Metric.isBounded_ball) (fun i ↦ (hball i).trans hKU) hγ hgap
  obtain ⟨θ, hθ, hθcap, hθ1, G, hdomain, hmap, hQ, hlow, centers, radius,
    hradius, hcover, ε, hε, hεG, hεT, hmean⟩ :=
    exists_flat_seed_normalized_mean hn G₀ hsource
      (fun i : (j : Fin D₀.chartCount) × Fin (D₀.patchCount j) ↦
        (hD.2.2.2.2.1 i.1 i.2).1) T hK hKU hball (lt_min hcap hκ)
  let Q := fun a ↦ (⟨projectedStress G.map, hQ, hlow a⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) Rsource) ∧
      cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T a).family.threshold})
  have hconnection a := hmatch θ hθ (hθcap.le.trans (min_le_right _ _)) a (Q a)
    (congrArg projectedStress hmap)
  simp only [← hmap] at hconnection
  refine ⟨θ, hθ,
    hθcap.trans_le (min_le_left _ _), hθ1, G, hdomain, hmap, hQ, hlow,
    centers, radius, hradius, hcover, ε, hε, hεG, hεT, hconnection, ?_⟩
  obtain ⟨b, hlocal, hmean⟩ := hmean
  refine ⟨b, ?_, hmean⟩
  intro j
  obtain ⟨row, col, τ, R, hτ, hR, Dflow, Φ, Y, hbdef, hbuffer,
    hDflow, hsmall, hdom, hbig, hΦ, hY, hΦD, hYU, hinit, hYΦ, hΦY,
    hΦz, hYz, hvelocity, hα, hb, hinitα, hpos, hscalar, hnull, hreduce, hk, hd, hc, hden⟩ := hlocal j
  let Tj := T j.1
  let Qj := Q j.1
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates Tj.data.adapted)
  let α := carrierScalarAmplitude Tj Qj G.map row col Φ Y (fun _ ↦ 1)
  have hUG : ball (0 : Euclidean n) Rsource ⊆ G.domain.chart n := by
    rw [hdomain]
    exact hsource
  have hrank : HasFullNormalRankOn G.map (ball (0 : Euclidean n) Rsource) :=
    fun x hx ↦ G.fullNormalRank x (hUG hx)
  have hflows : (∀ z₀ ∈ ball j.2.1.1 (radius j.1 j.2 / 2), ∃ R' τ' : ℝ, 0 < R' ∧ 0 < τ' ∧
                let I' := Ioo (-τ') τ'
                let L' := ball ((0 : Euclidean (n - 1)), z₀) (R' / 8)
                let W' := I' ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (R' / 32)
                ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
                  ∃ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) Rsource) ∧
                      cNorm (closedBall (0 : Euclidean n) Tj.data.localReference.stateRadius) 6
                        (Q - fun _ ↦ cubeStress n) < Tj.family.threshold},
                    Qσ.1 = projectedStress (sourceDilation G.map σ) ∧
                    ∃ Dσ : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
                    ∃ Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
                      IsOpen Dσ ∧ W' ⊆ Dσ ∧ C ⁻¹' Dσ ⊆ C ⁻¹' Dflow ∧
                      ContDiffOn ℝ ∞ Φσ (I' ×ˢ L') ∧ ContDiffOn ℝ ∞ Yσ Dσ ∧
                      MapsTo (fun q ↦ (q.1, Φσ q)) (I' ×ˢ L') Dσ ∧
                      MapsTo (fun q ↦ (q.1, Yσ q)) Dσ (I' ×ˢ L') ∧
                      (∀ p ∈ L', Φσ (0, p) = p) ∧
                      (∀ p ∈ L', ∀ t ∈ I', Yσ (t, Φσ (t, p)) = p) ∧
                      (∀ q ∈ Dσ, Φσ (q.1, Yσ q) = q.2) ∧
                      (∀ p ∈ L', ∀ t ∈ I', HasDerivAt (fun s ↦ Φσ (s, p))
                        ((adaptedCoordinates Tj.data.adapted (carrierTransportDirection Tj Qσ row col
                          (C.symm (t, Φσ (t, p))))).2, 0) t) ∧
                      EqOn (carrierScalarAmplitude Tj Qσ (sourceDilation G.map σ) row col Φσ Yσ (fun _ ↦ σ))
                        (sourceAmplitude α σ) (C ⁻¹' Dσ) ∧
                      EqOn (fun w ↦ carrierScalarAmplitude Tj Qσ (sourceDilation G.map σ)
                        row col Φσ Yσ (fun _ ↦ σ) w • carrierNullvector Tj Qσ col w)
                        (sourceAmplitude (b j) σ) (C ⁻¹' Dσ)) := by
    intro z₀ hz₀
    have hΩ : IsOpen (ball (0 : Euclidean n) (2 * ε) ×ˢ
        ball j.2.1.1 (radius j.1 j.2 / 2)) := isOpen_ball.prod isOpen_ball
    obtain ⟨r', hr', hball'⟩ := Metric.isOpen_iff.mp hΩ (0, z₀)
      ⟨mem_ball_self (by positivity), hz₀⟩
    have hsub := hball'.trans hbuffer
    have hpatch : ball ((0 : Euclidean n), z₀) r' ⊆ ball 0 Tj.physicalRadius ×ˢ
        parameterCube (2 * (D₀.patches j.1.1 j.1.2).radius) := by
      intro w hw
      exact ⟨ball_subset_ball (hεT j.1).le (hball' hw).1,
        fun k ↦ ((hdom (hsub hw)).2 k).le.trans
          (by linarith [(hD.2.2.2.2.1 j.1.1 j.1.2).1.1])⟩
    obtain ⟨R', τ', hR', hτ', hflow⟩ := exists_retained_scalar_source_flows
      Tj Qj G.contDiff hrank ((hball j.1).trans hKU) rfl (hconnection j.1).1
      (fun x _ ↦ G.inducedMetric_eq_one x) row col hr' hpatch
      (hd.mono hsub) (hk.mono hsub) (hc.mono hsub) (fun w hw ↦ hden w (hsub hw))
      (hα.mono hsub) (fun w hw ↦ hscalar w (hsub hw))
      (fun p _ ↦ by
        change carrierScalarAmplitude Tj Qj G.map row col Φ Y (fun _ ↦ 1)
          (Tj.data.adapted.embedding p.1, p.2) = 1
        rw [← show (adaptedCoordinates Tj.data.adapted).symm (0, p.1) =
          Tj.data.adapted.embedding p.1 by simp]
        simp only [carrierScalarAmplitude, coordinates_apply,
          ContinuousLinearEquiv.apply_symm_apply, transportFromFootpoint,
          characteristicTransport, scalarTransport, transportFactor,
          intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one])
    refine ⟨R', τ', hR', hτ', ?_⟩
    dsimp only
    intro σ hσ hσ1
    obtain ⟨Qσ, hscaled, _⟩ := (hconnection j.1).2 σ hσ hσ1
    obtain ⟨Dσ, Φσ, Yσ, hDσ, hsmallσ, hdomainσ, hΦσ, hYσ, hΦDσ, hYUσ,
      hiσ, hYΦσ, hΦYσ, hvσ, hαmatch⟩ := hflow σ hσ hσ1 Qσ hscaled
    refine ⟨Qσ, hscaled, Dσ, Φσ, Yσ, hDσ, hsmallσ, hdomainσ.trans hsub,
      hΦσ, hYσ, hΦDσ, hYUσ, hiσ, hYΦσ, hΦYσ, hvσ, hαmatch, ?_⟩
    intro w hw
    change carrierScalarAmplitude Tj Qσ (sourceDilation G.map σ) row col Φσ Yσ (fun _ ↦ σ) w •
      carrierNullvector Tj Qσ col w = sourceAmplitude (b j) σ w
    rw [hbdef, sourceAmplitude_smul, hαmatch hw,
      ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.current_carrierNullvector_source_dilation
        Tj Qj Qσ G.contDiff hrank ((hball j.1).trans hKU) rfl (hconnection j.1).1
        hσ hσ1 hscaled col (hpatch (hdomainσ hw)).1 (hpatch (hdomainσ hw)).2]
  have hcommon : (∃ δ > (0 : ℝ), ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
                ∀ x ∈ ball (0 : Euclidean n) δ, ∀ z' ∈ closedBall j.2.1.1 (radius j.1 j.2 / 4),
                  ∃ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) Rsource) ∧
                      cNorm (closedBall (0 : Euclidean n) Tj.data.localReference.stateRadius) 6
                        (Q - fun _ ↦ cubeStress n) < Tj.family.threshold},
                    Qσ.1 = projectedStress (sourceDilation G.map σ) ∧
                    ∃ Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
                      carrierScalarAmplitude Tj Qσ (sourceDilation G.map σ) row col Φσ Yσ (fun _ ↦ σ) (x, z') =
                        sourceAmplitude α σ (x, z') ∧
                      carrierScalarAmplitude Tj Qσ (sourceDilation G.map σ) row col Φσ Yσ (fun _ ↦ σ) (x, z') •
                        carrierNullvector Tj Qσ col (x, z') = sourceAmplitude (b j) σ (x, z')) := by
    classical
    let Kc := closedBall j.2.1.1 (radius j.1 j.2 / 4)
    have hKV : Kc ⊆ ball j.2.1.1 (radius j.1 j.2 / 2) :=
      closedBall_subset_ball (by have := hradius j.1 j.2; linarith)
    choose R' τ' hR' hτ' hf using fun z : Kc ↦ hflows z.1 (hKV z.2)
    let W := fun z : Kc ↦ C ⁻¹' (Ioo (-(τ' z)) (τ' z) ×ˢ
      ball ((0 : Euclidean (n - 1)), z.1) (R' z / 32))
    have hW (z : Kc) : IsOpen (W z) := (isOpen_Ioo.prod isOpen_ball).preimage C.continuous
    have h0W (z : Kc) : ((0 : Euclidean n), z.1) ∈ W z := by
      change C (0, z.1) ∈ Ioo (-(τ' z)) (τ' z) ×ˢ
        ball ((0 : Euclidean (n - 1)), z.1) (R' z / 32)
      simp only [C, coordinates_apply, map_zero, Prod.fst_zero, Prod.snd_zero]
      exact ⟨⟨neg_neg_of_pos (hτ' z), hτ' z⟩, mem_ball_self (div_pos (hR' z) (by norm_num))⟩
    obtain ⟨A, B, hA, _, h0A, hKB, hAB⟩ := generalized_tube_lemma
      (isCompact_singleton (x := (0 : Euclidean n))) (isCompact_closedBall _ _)
      (isOpen_iUnion hW) (show {(0 : Euclidean n)} ×ˢ Kc ⊆ ⋃ z, W z from by
        rintro ⟨x, z⟩ ⟨hx, hz⟩
        obtain rfl : x = 0 := mem_singleton_iff.mp hx
        exact mem_iUnion.mpr ⟨⟨z, hz⟩, h0W ⟨z, hz⟩⟩)
    obtain ⟨δ, hδ, hδA⟩ := Metric.isOpen_iff.mp hA 0 (h0A (mem_singleton 0))
    refine ⟨δ, hδ, ?_⟩
    intro σ hσ hσ1 x hx z hz
    obtain ⟨z₀, hw⟩ := mem_iUnion.mp (hAB (show (x, z) ∈ A ×ˢ B from ⟨hδA hx, hKB hz⟩))
    obtain ⟨Qσ, hscaled, Dσ, Φσ, Yσ, _, hsmallσ, _, _, _, _, _, _, _, _, _, hαmatch, hbmatch⟩ :=
      hf z₀ σ hσ hσ1
    exact ⟨Qσ, hscaled, Φσ, Yσ, hαmatch (hsmallσ hw), hbmatch (hsmallσ hw)⟩
  refine ⟨row, col, τ, R, hτ, hR, Dflow, Φ, Y, hbdef, hbuffer,
    hDflow, hsmall, hdom, hbig, hΦ, hY, hΦD, hYU, hinit, hYΦ, hΦY,
    hΦz, hYz, hvelocity, hα, hb, hinitα, hpos, hscalar, hnull, hreduce, hk, hd, hc, hden, hflows, hcommon, ?_⟩
  intro σ hσ hσ1
  obtain ⟨Qσ, hscaled, _⟩ := (hconnection j.1).2 σ hσ hσ1
  refine ⟨Qσ, hscaled, ?_, ?_⟩
  · intro u z hz
    exact sourceAmplitude_initial_scalar (T j.1).data.adapted.embedding.toContinuousLinearMap
      (hinitα (σ • u, z) hz)
  · intro x hx z hz
    have hsx : σ • x ∈ ball (0 : Euclidean n) (2 * ε) := (convex_ball (0 : Euclidean n) (2 * ε)).smul_mem_of_zero_mem
      (mem_ball_self (by positivity)) hx ⟨hσ.le, hσ1⟩
    have hmem : coordinates (Z := Euclidean 3) (adaptedCoordinates (T j.1).data.adapted)
        (σ • x, z) ∈ Dflow :=
      hbuffer (show (σ • x, z) ∈ ball (0 : Euclidean n) (2 * ε) ×ˢ
        ball j.2.1.1 (radius j.1 j.2 / 2) from ⟨hsx, hz⟩)
    have hxT := ball_subset_ball (hεT j.1).le hx
    have hzP : z ∈ parameterCube (2 * (D₀.patches j.1.1 j.1.2).radius) := by
      intro k
      exact ((hdom hmem).2 k).le.trans (by linarith [(hD.2.2.2.2.1 j.1.1 j.1.2).1.1])
    have hbreg : ContDiffAt ℝ ∞ (b j) (σ • x, z) := by
      rw [hbdef]
      exact hb.contDiffAt ((hDflow.preimage
        (coordinates (Z := Euclidean 3) (adaptedCoordinates (T j.1).data.adapted)).continuous).mem_nhds hmem)
    have hne : b j (σ • x, z) ≠ 0 := by
      rw [hbdef]
      exact (hpos (σ • x, z) hmem).2
    have hnp : reducedSymbol ((Q j.1).1 (σ • x))
        ((T j.1).carrierGradient (Q j.1) (σ • x) z) *ᵥ (fun k ↦ b j (σ • x, z) k) = 0 := by
      rw [hbdef]
      exact hnull (σ • x, z) hmem
    have htr : carrierConullvector (T j.1) (Q j.1) row (σ • x, z) ⬝ᵥ
        reducedOperator G.map (Q j.1).1 (fun y ↦ b j (y, z)) (σ • x) = 0 := by
      rw [hbdef]
      exact hreduce (σ • x, z) hmem
    refine ⟨?_, sourceAmplitude_pos hσ (hpos (σ • x, z) hmem).1,
      retained_sourceAmplitude_transport G hUG (T j.1) (Q j.1) Qσ
        ((hball j.1).trans hKU) rfl (hconnection j.1).1 hσ hσ1 hscaled row
        hxT hzP hbreg hne hnp htr⟩
    rw [hbdef, sourceAmplitude_smul,
      ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.current_carrierNullvector_source_dilation
        (T j.1) (Q j.1) Qσ G.contDiff hrank ((hball j.1).trans hKU)
        rfl (hconnection j.1).1 hσ hσ1 hscaled col hxT hzP]

end JanetCartan.ReferenceInitialization.NormalizedHistory
