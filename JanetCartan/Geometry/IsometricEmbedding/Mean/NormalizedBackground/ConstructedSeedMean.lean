module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedFamily
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedMean

/-!
# Actual finite normalized seed mean from the dimension hypothesis

This final geometric assembly supplies the analytic flat reference, retained
finite Hamilton family, primitive compact coefficient domain and selected unit
transports. No seed phase, null solution, normal nonvanishing or mean estimate
is a hypothesis. The continuum row and inverse are not constructed here
(`app:ch_background:prop:bg-normalized`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff Matrix Matrix.Norms.Frobenius JanetCartan.TensorFrobenius InnerProductSpace

namespace JanetCartan.NormalizedBackground
open ActualCarriers FrozenMenu FrozenPhaseReference CurrentFullPhase ProjectedStressFrame
open NullTransport ActualFlow FlowAmplitude SourceGeometry

/-- The constructed geometric and fixed-Lebesgue-mean part of
`app:ch_background:prop:bg-normalized`, from `5 ≤ n` alone and an arbitrary
positive seed cap. The actual retained family supplies every input of
`exists_flat_seed_normalized_mean`; one frozen transverse gap is preserved
for its later identification with the continuum source family. The seed family
and transport buffers precede weights; the source scale interval precedes
derivative orders, targets and histories. This does not assert continuum
coercivity, inverse or density estimates. -/
theorem exists_constructed_flat_seed_normalized_mean {n : ℕ} (hn : 5 ≤ n)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ (G₀ : FlatReference n) (D₀ : CoverData n) (c₀ C₀ : ℝ), D₀.IsValid c₀ C₀ ∧
      ∃ T : (i : (j : Fin D₀.chartCount) × Fin (D₀.patchCount j)) →
          PatchQuantitativeFamily (D₀.patches i.1 i.2) (G₀.domain.chart n) isOpen_ball,
        ∃ γ > 0, (∀ i, ∀ q ∈ closedBall (0, (T i).data.center)
            (T i).data.localReference.stateRadius,
          γ ≤ |⟪(frozenSymbol n).hp q, (T i).data.adapted.normal⟫_ℝ|) ∧
        let A := (j : Fin D₀.chartCount) × Fin (D₀.patchCount j)
        let P : A → Patch n := fun i ↦ D₀.patches i.1 i.2
        let U := G₀.domain.chart n
        ∃ θ : ℝ, 0 < θ ∧ θ < cap ∧ θ ≤ 1 ∧
          ∃ G : FlatReference n, G.domain = G₀.domain ∧ G.map = sourceDilation G₀.map θ ∧
          ∃ hQ : ContDiffOn ℝ ∞ (projectedStress G.map) U,
          ∃ hlow : ∀ a, cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
            (projectedStress G.map - fun _ ↦ cubeStress n) < (T a).family.threshold,
          ∃ centers : (a : A) → Finset (parameterCube (P a).radius),
          ∃ radius : (a : A) → centers a → ℝ,
            (∀ a j, 0 < radius a j) ∧
            (∀ a, parameterCube (P a).radius ⊆ ⋃ j : centers a,
              ball j.1.1 (radius a j / 4)) ∧
            ∃ ε : ℝ, 0 < ε ∧ ball (0 : Euclidean n) (2 * ε) ⊆ G.domain.chart n ∧
            (∀ a, 2 * ε < (T a).physicalRadius) ∧
            let I := (a : A) × centers a
            let Q := fun a ↦ (⟨projectedStress G.map, hQ, hlow a⟩ :
              {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
                cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
                  (Q - fun _ ↦ cubeStress n) < (T a).family.threshold})
            let S := fun (j : I) (p : Euclidean n × Euclidean 3) ↦ (T j.1).carrier (Q j.1) p.1 p.2
            let ξ := fun (j : I) (p : Euclidean n × Euclidean 3) ↦
              (T j.1).carrierGradient (Q j.1) p.1 p.2
            let V := fun j : I ↦ ball j.2.1.1 (radius j.1 j.2 / 2)
            let Kc := fun j : I ↦ closedBall j.2.1.1 (radius j.1 j.2 / 4)
            ∃ b : I → Euclidean n × Euclidean 3 → Euclidean n,
            (∀ j : I,
            let T := T j.1
            let P := P j.1
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
              C ⁻¹' D ⊆ U ×ˢ parameterInterior (3 * P.radius / 2) ∧
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
              (∀ w ∈ C ⁻¹' D, carrierAdaptedDenominator T Q row col w ≠ 0)) ∧
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
  obtain ⟨G₀, D₀, c₀, C₀, hD, T, hK, hKU, hball, γ, hγ, hgap⟩ :=
    exists_flat_seed_family hn
  refine ⟨G₀, D₀, c₀, C₀, hD, T, γ, hγ, hgap, ?_⟩
  exact exists_flat_seed_normalized_mean hn G₀ (Subset.refl _)
    (fun i : (j : Fin D₀.chartCount) × Fin (D₀.patchCount j) ↦
      (hD.2.2.2.2.1 i.1 i.2).1) T hK hKU hball hcap

end JanetCartan.NormalizedBackground
