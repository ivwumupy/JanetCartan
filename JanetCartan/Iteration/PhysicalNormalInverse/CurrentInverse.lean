module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.CommonHistoryRegularity.LeadingCarrier
public import JanetCartan.Iteration.PhysicalNormalInverse.Regularity
public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationAuxiliary
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.Adjoint
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedRow.Estimates
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCorrectedRegularity.SuppliedRawGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartNormal
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.DensityScalar
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.InitialScalar
public meta import JanetCartan.Iteration.PhysicalNormalInverse.CurrentInverseTemplate

/-!
# Current physical normal inverse from the original full leading fields

For `app:ch_background:prop:bg-inverse` and `app:ch_background:prop:bg-adjoint`,
combine the actual physical history geometry with the original leading carrier
amplitude/normal producer and the physical prescribed-row gap.  The inverse is
that of the CURRENT augmented normal, not the frozen/source reference inverse.
All constants precede the physical prefix, density and Sobolev order, and one
high coefficient size occurs with fixed shift `2*(n+1)+14`.

The exact carrier continuation is produced by task19's
`PhysicalNormalInverse.OriginalSource.source_continuation`.  The remaining full
leading fields and scalar solution certificates are the original same-current
leading producer's outputs.  The parent must actually instantiate both on the
same row; this assembly is not an unconditional inverse/embedding theorem until
that original-data application is supplied.  No inverse regularity or tame
inverse success is taken as an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius InnerProductSpace

namespace JanetCartan.PhysicalNormalInverse
open ContinuumInverse
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open NullTransport ActualFlow FlowAmplitude LeadingWave.FullModulation ProjectedStressFrame
open ContinuumRow LeadingPrimitive CanonicalCarrier CanonicalConic TransportKernel CarrierNormalRealization
open ContinuumNormalReduction.TransportSymbol ContinuumNormal.RetainedFrozen
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction RetainedRowGeometry
open Pseudodifferential AmplitudeBound PeriodicLocalL2
open ContinuumAdjoint ContinuumAdjoint.Canonical CarrierSobolev
open ContinuumCommutator
open ContinuumAdjoint.Canonical.AmplitudeProfiles AmbientResponse LeadingWave


private theorem cNorm_union_for_original_history
    {n N : ℕ} {K K' : Set (Euclidean n)} (hK : IsCompact K) (hK' : IsCompact K')
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F) (m : ℕ) :
    cNorm (K ∪ K') m F ≤ cNorm K m F + cNorm K' m F := by
  unfold cNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  apply Real.sSup_le _ (add_nonneg (sSup_norm_iteratedFDeriv_nonneg K j F)
    (sSup_norm_iteratedFDeriv_nonneg K' j F))
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with hx | hx
  · exact (le_csSup (bddAbove_norm_iteratedFDeriv hK (hF.of_le (by simp)) (le_refl j))
      (mem_image_of_mem _ hx)).trans
        (le_add_of_nonneg_right (sSup_norm_iteratedFDeriv_nonneg K' j F))
  · exact (le_csSup (bddAbove_norm_iteratedFDeriv hK' (hF.of_le (by simp)) (le_refl j))
      (mem_image_of_mem _ hx)).trans
        (le_add_of_nonneg_left (sSup_norm_iteratedFDeriv_nonneg K j F))

/-- The actual original leading solution and the prescribed history carriers
supply every analytic field of the same inverse and augmented raw adjoint.
The cap precedes σ; all constants and the admission threshold precede history,
density and Sobolev order. The original maps and scalar norm domains appear
once in the high coefficient size (`app:ch_background:eq:bg-r-inverse`,
`app:ch_background:eq:bg-derivative-trade`). -/
theorem exists_capped_source_history_inverse_with_scalar_admission
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι]
    (Href : FlatReference n) {bRadius Rwork : ℝ}
    (hb : 0 < bRadius) (hbR : bRadius < Rwork) (hR : Rwork < Href.domain.chartRadius)
    {P : ι → Patch n}
    (T : (i : ι) → PatchQuantitativeFamily (P i) (ball 0 Rwork) isOpen_ball)
    {c C : ι → ℝ}
    (hP : (i : ι) → (P i).IsValid (c i) (C i))
    (hball : (i : ι) → closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ (closedBall (0 : Euclidean n) bRadius))
    (D : ι → CoefficientNormCharts n)
    (zCell : ι → Euclidean 3)
    {L : ι → ℝ}
    (hL : (i : ι) → 0 < (L i))
    {Jfull : ι → Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hJfull : (i : ι) → IsCompact (Jfull i))
    (zFull : ι → Euclidean 3 × Euclidean (n - 1))
    {σfull : ι → ℝ}
    (hσfull : (i : ι) → 0 < (σfull i))
    (hJfullEq : (i : ι) → (Jfull i) = closedBall ((0 : Euclidean n), (zFull i)) (σfull i))
    (hJphysical : (i : ι) → closedBall (0 : Euclidean n) (2 * (σfull i)) ⊆ (closedBall (0 : Euclidean n) bRadius))
    (hJphase : (i : ι) → closedBall ((0 : Euclidean n), (zFull i)) (2 * (σfull i)) ⊆ domain (T i))
    (Wfull : ι → Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
    (hWfull : (i : ι) → IsCompact (Wfull i))
    (hJfullW : (i : ι) → (Jfull i) ⊆ (Wfull i))
    (E : ι → Set (Euclidean n × CarrierParameter))
    (hE : (i : ι) → IsOpen (E i))
    (hgraph : (i : ι) → MapsTo (carrierGraph (T i)) (E i) (Jfull i))
    (hDE : (i : ι) → (D i).field.region ⊆ (E i))
    (hfield : (i : ι) → (E i) ⊆ ((ball (0 : Euclidean n) Rwork) ∩ ball (0 : Euclidean n) (T i).physicalRadius) ×ˢ
      (parameter ⁻¹' parameterInterior (2 * (P i).radius)))
    (hphase : (i : ι) → (E i) ⊆ ball (0 : Euclidean n) (T i).family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * (P i).radius / 2)))
    (adet : ι → Euclidean n × Euclidean 3)
    {ρdet : ι → ℝ}
    (hρdet : (i : ι) → 0 < (ρdet i))
    (hxdet : (i : ι) → MapsTo Prod.fst (closedBall (adet i) (ρdet i))
      (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius))
    (hdet : (i : ι) → closedBall (adet i) (ρdet i) ⊆
      ball (0 : Euclidean n) (T i).physicalRadius ×ˢ parameterInterior (2 * (P i).radius))
    (hmaps : (i : ι) → MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      (D i).field.carrier (closedBall (adet i) (ρdet i)))
    (z₀ : ι → Euclidean 3)
    (hz₀ : (i : ι) → (z₀ i) ∈ parameterInterior (P i).radius)
    (hcenter : (i : ι) → chartCenter (z₀ i) ∈ (E i))
    {ηb : ι → Euclidean (n - 1)}
    (hηb : (i : ι) → (ηb i) ≠ 0)
    {r a r' a' : ι → ℝ}
    (hr : (i : ι) → 0 < (r i))
    (hr' : (i : ι) → 0 < (r' i))
    (ha' : (i : ι) → 0 < (a' i))
    (hcell : (i : ι) → 4 * (a' i) < 1 / 2)
    (hcap : (i : ι) → (a' i) ≤ (exists_current_rawAdjoint_cap_on_supplied_geometry
      (N := embeddingDimension n) hn (hP i) (T i) (isCompact_closedBall _ _) (closedBall_subset_ball hbR) (hball i)
      (closedBall ((0 : Euclidean (n - 1)), (zCell i)) ((L i) / 8)) (hJfull i) (E i) (hE i) (hgraph i) (hz₀ i) (hcenter i)).choose)
    (ha : (i : ι) → 0 < (a i))
    (har : (i : ι) → 6 * (a i) ≤ (r i))
    (haR : (i : ι) → 6 * (a i) < (T i).family.radius)
    (hrr : (i : ι) → (r' i) ≤ (r i))
    (haa : (i : ι) → (a' i) ≤ (a i))
    (har' : (i : ι) → (a' i) ≤ (r' i))
    (hcarrier : (i : ι) → closedBall (spectatorCenter (z₀ i)) (3 * (r i)) ×ˢ closedBall ((z₀ i) 0) (3 * (r i)) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * (P i).radius / 2))
    (houter : (i : ι) → coefficientDomain (z₀ i) (r i) (6 * (a i)) ⊆ (E i))
    (hsupport : (i : ι) → tsupport (FixedCutoffs.physical (n := n) (ha' i) 1) ×ˢ
      carrierSupport (z₀ i) (r := (a' i)) ⊆ (D i).field.carrier)
    (p₀ : ι → InputVariables n)
    (hp₀ : (i : ι) → (p₀ i) = (((0, 0), ((z₀ i) 0, spectatorCenter (z₀ i)), (ηb i)) : InputVariables n))
    (q₀ : ι → Variables n × Euclidean 2)
    {ρ τ : ι → ℝ}
    (hρ : (i : ι) → 0 < (ρ i))
    (hτ : (i : ι) → 0 < (τ i))
    (haρ : (i : ι) → 4 * (a' i) < (ρ i))
    (hrρ : (i : ι) → (r' i) ≤ (ρ i))
    {W Bi : ι → Set (InputVariables n)}
    (hW : (i : ι) → IsOpen (W i))
    (hKiW : (i : ι) → closedBall (p₀ i) (ρ i) ⊆ (W i))
    (hBi : (i : ι) → IsCompact (Bi i))
    (hWBi : (i : ι) → (W i) ⊆ (Bi i))
    (hBiDom : (i : ι) → (Bi i) ⊆ symbolInputDomain (z₀ i) (ηb i) (r i) (6 * (a i)))
    (hfoot : (i : ι) → ∀ p ∈ closedBall (p₀ i) (ρ i), (D i).Contains p)
    {It : ι → Set ℝ}
    (hIt : (i : ι) → IsOpen (It i))
    (hIIt : (i : ι) → Icc (0 : ℝ) 1 ⊆ (It i))
    (hsegT : (i : ι) → ∀ t ∈ (It i), MapsTo (transportSegmentInput n t) (W i) (D i).field.region)
    (hseg : (i : ι) → ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) (W i) (D i).field.carrier)
    (A : (i : ι) → InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {ε gap δgeometry : ι → ℝ}
    (hε : (i : ι) → 0 < (ε i))
    (hgap : (i : ι) → 0 < (gap i))
    (hδgeometry : (i : ι) → 0 < (δgeometry i))
    (hfreq : (i : ι) → ∀ p ∈ (Bi i), (ε i) ≤ ‖p.2.2‖)
    {β cJ : ι → ℝ}
    (hcJ : (i : ι) → 0 < (cJ i))
    {Vinv Linv : ι → Set (ℝ × Euclidean (n - 1))}
    (hVinv : (i : ι) → IsOpen (Vinv i))
    (hLVinv : (i : ι) → (Linv i) ⊆ (Vinv i))
    (Ginv : (i : ι) → (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)))
    (hgeometry : (i : ι) → ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F (ball (0 : Euclidean n) Rwork))
      (hi : IsImmersionOn F (ball (0 : Euclidean n) Rwork)) (hrank : HasFullNormalRankOn F (ball (0 : Euclidean n) Rwork)),
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < (δgeometry i) →
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF hi hrank), hlow⟩
      RetainedSpectralGeometry (T i) Q (z₀ i) (ηb i) (r i) (a i) ∧
      closedBall (q₀ i) (2 * (τ i)) ⊆ symbolDomain (T i) Q (z₀ i) (ηb i) (r i) (6 * (a i)) ∧
      MapsTo (inverseCoordinates (symbolInverse (T i) Q (z₀ i) (ηb i) (r i) (6 * (a i))))
        (closedBall (q₀ i) (2 * (τ i))) (closedBall (p₀ i) (ρ i)) ∧
      (∀ p ∈ closedBall (p₀ i) (ρ i), ‖(A i).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition (T i) Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ (Bi i), (gap i) ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
        (transportPosition (T i) Q) p) ∧
      (closure (augmentedTransportGradient (transportPosition (T i) Q) ''
        conicMaskSupport (z₀ i) (ηb i) (r' i) (a' i)) ∩ {p | p.1.2.2 ≠ 0} ⊆
          symbolDomain (T i) Q (z₀ i) (ηb i) (r i) (6 * (a i))) ∧
      (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
        (x, v) ∈ closure (augmentedTransportGradient (transportPosition (T i) Q) ''
          conicMaskSupport (z₀ i) (ηb i) (r' i) (a' i)) → (x, v) ∈ closedBall (q₀ i) (τ i)) ∧
      (∀ p ∈ symbolDomain (T i) Q (z₀ i) (ηb i) (r i) (6 * (a i)),
        ‖(symbolInverse (T i) Q (z₀ i) (ηb i) (r i) (6 * (a i)) p).2‖ ≤ 2 * ‖p.1.2.2‖) ∧
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart (T i) Q))
        (physicalParameterSet (z₀ i) (6 * (a i)) ×ˢ dataSet (z₀ i) (ηb i) (3 * (r i))) ∧
      BufferedPhaseInverse (adaptedTransportChart (T i) Q) (physicalParameterSet (z₀ i) (6 * (a i)))
        (dataBox (z₀ i) (ηb i) (r i)) (dataSet (z₀ i) (ηb i) (2 * (r i))) (dataBox (z₀ i) (ηb i) (2 * (r i)))
        (Vinv i) (Linv i) (β i) (cJ i) (Ginv i) ∧
      (∀ p ∈ physicalParameterSet (z₀ i) (6 * (a i)),
        ∀ u ∈ supportedCone (z₀ i) (NormedSpace.normalize (ηb i)) (r i) (angularWidth (ηb i) (r i)),
          ‖(adaptedTransportChart (T i) Q p u).2 - u.2‖ ≤ (angularWidth (ηb i) (r i) / 4) * ‖u.2‖))
    {Ωflow Kflow : ι → Set (Euclidean n × Euclidean 3)}
    {Rc Bflow τflow Mc : ι → ℝ}
    (hRc : (i : ι) → 0 < (Rc i))
    (hτflow : (i : ι) → 0 < (τflow i))
    (hMc : (i : ι) → 0 < (Mc i))
    (hEcylinder : (i : ι) → MapsTo (densityCoordinates (T i)) (E i)
      (outputCylinder ((0 : Euclidean (n - 1)), (zCell i)) (Rc i) (τflow i)))
    (hElabel : (i : ι) → ∀ p ∈ (E i), (densityCoordinates (T i) p).2 ∈
      closedBall ((0 : Euclidean (n - 1)), (zCell i)) ((L i) / 64))
    (hEtime : (i : ι) → ∀ p ∈ (E i), |(densityCoordinates (T i) p).1| < (L i) / (64 * (Mc i)))
    (hDouter : (i : ι) → (D i).field.region ⊆ coefficientDomain (z₀ i) (r i) (6 * (a i)))
    (row col : ι → Fin n)
    (hforward : ∀ i (F : Euclidean n → Euclidean (embeddingDimension n))
      (current : Chart (T i) (Ωflow i) (Kflow i) ((0 : Euclidean (n - 1)), zCell i)
        (Rc i) (Bflow i) (τflow i) (row i) (col i) F),
      cNorm (Icc (-τflow i) (τflow i) ×ˢ
        closedBall ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8)) 1 current.forward ≤ Mc i) :
    ∃ cap > (0 : ℝ), cap ≤ 1 ∧ ∃ Cscalar > (0 : ℝ),
      1 ≤ Cscalar ∧
      (∀ (p : Euclidean (n-1) × Euclidean 3) {R : ℝ}, 0 < R →
        ∀ {σ : ℝ}, 0 < σ → ∀ v : Euclidean (n-1) × Euclidean 3 → ℝ,
          ContDiffOn ℝ ∞ v (ball p (R/4)) →
          (∀ q ∈ ball p (R/4), 0 < 1 + v q) →
          (∀ q ∈ closedBall p (R/8), 1 + v q ∈ Icc (1/2 : ℝ) (3/2)) →
          cNorm (closedBall p (R/8)) 15 v ≤ 1 →
          let initial := fun q ↦ positiveDensityAmplitude σ (v q)
          ContDiffOn ℝ ∞ initial (ball p (R/4)) ∧
            cNorm (closedBall p (R/8)) 15 initial ≤ σ*Cscalar ∧
            ∀ q ∈ ball p (R/8), σ*Real.sqrt (1/2) ≤ initial q) ∧
    ∀ σ ∈ Ioc (0 : ℝ) cap, ∀ {Bband : ℝ}, 1 ≤ Bband →
    ∀ {rStar kMin : ℕ}, canonicalCarrierLowOrder n ≤ rStar →
      RevisedScales.displacementLoss n +
        bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ) →
    ∀ Bfull Bnull : ι → ℕ → ℝ, (∀ i j, 0 < Bfull i j) →
    ∀ {μ rInner : ℝ} (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2)
      (hrInner : 0 < rInner) (hInnerCell : rInner < 1 / 2),
      6 * μ < Href.domain.chartRadius → 6 * μ < 1 / 2 →
    ∀ (χcoeff : Euclidean n → ℝ), ContDiff ℝ ∞ χcoeff →
      tsupport χcoeff ⊆ ball 0 (5 * μ) →
    ∀ {g Mlimit : ℝ}, 0 < NormalAugmentation.globalGap g Mlimit →
    ∀ Mphysical Sgap : ℝ, 2 ≤ Sgap →
    ∀ coeffHistory : (R₀ : ℝ) → Sgap ≤ R₀ → (stage : ℕ) →
      (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n))) → (ell : Fin stage → ℕ) →
      RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell → GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ),
      (∀ R₀ hR₀ stage u ell hu j x, coeffHistory R₀ hR₀ stage u ell hu j x =
        χcoeff (centeredTorusRepresentative x) *
          GeometricProfile.geometricReducedCoefficients
            (RevisedGlobal.finiteMap (sourceDilation Href.map σ) u) (centeredTorusRepresentative x) j) →
    let χ := FixedCutoffs.periodic (n := n) hμ hμcell 1
    let χsrc := FixedCutoffs.periodic (n := n) hμ hμcell 2
    let ψ := ContinuumNormal.innerCutoff (n := n) hrInner hInnerCell
    let γ := (NormalAugmentation.globalGap g Mlimit / 2) / 2
    let angular := fun i ↦ angularMask (z₀ i) (NormedSpace.normalize (ηb i)) (ha' i)
      (angularWidth_spec (hηb i) (hr' i)).1
    (∀ R₀ (hR₀ : Sgap ≤ R₀) stage
      (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n))) (ell : Fin stage → ℕ)
      (hu : RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell),
      let F := RevisedGlobal.finiteMap (sourceDilation Href.map σ) u
      ∀ current : ∀ i, Chart (T i) (Ωflow i) (Kflow i) ((0 : Euclidean (n - 1)), zCell i)
        (Rc i) (Bflow i) (τflow i) (row i) (col i) F,
      ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
        (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), zCell i) (L i / 4))) →
        (∀ i p, p ∈ ball ((0 : Euclidean (n - 1)), zCell i) (L i / 4) → 0 < 1 + v i p) →
        (∀ i p, p ∈ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8) →
          1 + v i p ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
        (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8))
          (2 * (n + 1) + 14) (v i) ≤ 1) →
      let initial := fun i p ↦ positiveDensityAmplitude σ (v i p)
      let e := fun i ↦ data (T i) (current i).Q F (row i) (col i)
        (current i).forward (current i).inverse (initial i) (ha' i) (hcell i) (angular i)
        FixedCutoffs.highFrequency
      ∃ Vop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ i, (∀ f : carrierInitialTestSpace n,
          Vop i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (e i) f.val) ∧
          ∀ w : ComplexOutputL2 n, MemLp (carrierAdjointIntegral (e i) w) 2 (carrierMeasure n) ∧
            (Vop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
        let image := imageChannel (coeffHistory R₀ hR₀ stage u ell hu) χ χsrc
        let V := fun i ↦ CommonMeasurement.restrictCarrier χ (Vop i)
        ‖physicalRow image V‖ ≤ Mphysical ∧
        ∀ w : OutputL2 n, γ * ‖w‖ ^ 2 ≤ ‖(augmentedRow image V ψ).adjoint w‖ ^ 2) →
    ∃ Cinv Cadj Cpair Czero : ℕ → ℝ,
      (∀ s, 0 ≤ Cinv s) ∧ (∀ s, 0 ≤ Cadj s) ∧ (∀ s, 0 ≤ Cpair s) ∧
      (∀ s, 0 ≤ Czero s) ∧
    ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ stage (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n))) (ell : Fin stage → ℕ),
      RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap (sourceDilation Href.map σ) u
      ∀ current : ∀ i, Chart (T i) (Ωflow i) (Kflow i) ((0 : Euclidean (n - 1)), zCell i)
        (Rc i) (Bflow i) (τflow i) (row i) (col i) F,
      ∀ (Φ Y : ι → ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (O : ι → Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
        (Vcomp : ι → Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
      (∀ i, IsOpen (O i) ∧ MapsTo Prod.fst (O i) (ball 0 Rwork) ∧ (O i) ⊆ domain (T i) ∧
        closedBall ((0 : Euclidean n), zFull i) (2 * σfull i) ⊆ O i ∧ Wfull i ⊆ O i ∧
        MapsTo (carrierGraph (T i)) (E i) (O i) ∧
        MapsTo (fun p : Euclidean n × CarrierParameter ↦
          coordinates (adaptedCoordinates (T i).data.adapted) (p.1, parameter p.2)) (E i) (Vcomp i)) →
      (∀ i (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) q, q ∈ Vcomp i →
        let w := (coordinates (adaptedCoordinates (T i).data.adapted)).symm q
        scalarAmplitude (T i) (current i).Q F (row i) (col i) (Φ i) (Y i) initial
            (w.1, (w.2, (T i).reference.spatialPatch w.2)) =
          carrierScalarAmplitude (T i) (current i).Q F (row i) (col i)
            (current i).forward (current i).inverse initial w) →
      (∀ i (initial : Euclidean (n - 1) × Euclidean 3 → ℝ),
        ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), zCell i) (L i / 4)) →
        cNorm (closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8)) 14 initial ≤ σ * Cscalar →
        (∀ p ∈ ball ((0 : Euclidean (n - 1)), zCell i) (L i / 8), σ * Real.sqrt (1 / 2) ≤ initial p) →
        let α := scalarAmplitude (T i) (current i).Q F (row i) (col i) (Φ i) (Y i) initial
        let b₀ := fun w ↦ α w • nullvector (T i) (current i).Q (col i) w
        let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
          phaseGradient (T i) (current i).Q w.1 w.2.2
        let ν := fun w ↦ LeadingWave.principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        ContDiffOn ℝ ∞ b₀ (O i) ∧
        (∀ j, cNorm (Wfull i) j α + cNorm (Wfull i) j b₀ ≤
          Bnull i j * (1 + cNorm (closedBall 0 bRadius) (j + 13) F +
            cNorm (closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8)) (j + 13) initial)) ∧
        (∀ j, cNorm (Jfull i) j (fun w ↦ phase (T i) (current i).Q w.1 w.2.2) +
          cNorm (Jfull i) j b₀ + cNorm (Jfull i) j ν + cNorm (Jfull i) j V +
            cNorm (Jfull i) j (fun w ↦ LeadingWave.principalMatrix (ν w) (ξ w)) ≤
          Bfull i j * (1 + cNorm (closedBall 0 bRadius) (j + 14) F +
            cNorm (closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8)) (j + 14) initial))) →
      ∀ coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ j x, coeff j x = χcoeff (centeredTorusRepresentative x) *
          GeometricProfile.geometricReducedCoefficients F (centeredTorusRepresentative x) j) →
      ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
        (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), zCell i) (L i / 4))) →
        (∀ i p, p ∈ ball ((0 : Euclidean (n - 1)), zCell i) (L i / 4) → 0 < 1 + v i p) →
        (∀ i p, p ∈ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8) →
          1 + v i p ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
        (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8))
          (2 * (n + 1) + 14) (v i) ≤ 1) →
      let initial := fun i p ↦ positiveDensityAmplitude σ (v i p)
      let e := fun i ↦ data (T i) (current i).Q F (row i) (col i)
        (current i).forward (current i).inverse (initial i) (ha' i) (hcell i) (angular i)
        FixedCutoffs.highFrequency
      ∃ Vop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ i, (∀ f : carrierInitialTestSpace n,
          Vop i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (e i) f.val) ∧
          ∀ w : ComplexOutputL2 n, MemLp (carrierAdjointIntegral (e i) w) 2 (carrierMeasure n) ∧
            (Vop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
      let V := fun i ↦ CommonMeasurement.restrictCarrier χ (Vop i)
      let image := imageChannel coeff χ χsrc
      let Arow := augmentedRow image V ψ
      let Nop := augmentedNormal image V ψ
      let S := periodicSobolevScale n (Euclidean n)
      let X := augmentedInputSobolevScale n ι
      let Hcoef := retainedCoefficientProfile (closedBall 0 bRadius) (closedBall 0 (6 * μ))
        (fun i ↦ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8)) F initial
      (∀ a, IsSmoothPeriodic (coeff a)) ∧
      ‖physicalRow image V‖ ≤ Mphysical ∧
      (∀ w : OutputL2 n, γ * ‖w‖ ^ 2 ≤ ‖Arow.adjoint w‖ ^ 2) ∧
      ‖Nop.inverse‖ ≤ γ⁻¹ ∧
      (∀ s w, w ∈ S.level s → Nop w ∈ S.level (s + 1) → w ∈ S.level (s + 1)) ∧
      (∀ s w, w ∈ S.level s → Nop.inverse w ∈ S.level s ∧
        S.gradeNorm s (Nop.inverse w) ≤ Cinv s *
          (S.gradeNorm s w + (1 + Hcoef (s + (2 * (n + 1) + 14))) * ‖w‖)) ∧
      (∀ s w, w ∈ S.level s → Arow.adjoint w ∈ X.level s ∧
        X.gradeNorm s (Arow.adjoint w) ≤ Cadj s *
          (S.gradeNorm s w + (1 + Hcoef (s + (2 * (n + 1) + 14))) * ‖w‖)) ∧
      (∀ w, Arow (CoerciveInverse.rightInverse Arow w) = w) ∧
      (∀ s w, w ∈ S.level s → CoerciveInverse.rightInverse Arow w ∈ X.level s ∧
        S.gradeNorm s (Nop.inverse w) + X.gradeNorm s (CoerciveInverse.rightInverse Arow w) ≤
          Cpair s * (S.gradeNorm s w + (1 + Hcoef (s + (2 * (n + 1) + 14))) * ‖w‖)) ∧
      Nop ∘L Nop.inverse = ContinuousLinearMap.id ℝ (OutputL2 n) ∧
      Nop.inverse ∘L Nop = ContinuousLinearMap.id ℝ (OutputL2 n) ∧
      (∀ (residual : CurrentMean.SmoothResidual n) (s : ℕ),
        Arow.adjoint (Nop.inverse (CurrentMean.smoothResidualToL2 n residual)) ∈
          augmentedInputLevel n ι s) ∧
      (v = 0 → ∀ s w, w ∈ S.level s →
        S.gradeNorm s (Nop.inverse w) + X.gradeNorm s (CoerciveInverse.rightInverse Arow w) ≤
          Czero s * (S.gradeNorm s w +
            (currentCoefficientScale R₀ stage) ^ (s - (rStar - canonicalCarrierLowOrder n)) * ‖w‖)) := by
  classical
  let Kin := fun i ↦ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8)
  have hlocal (i : ι) :=
    exists_original_leading_carrier_profiles_on_capped_row
      (n := n) (hn := hn) (P := (P i)) (U := (ball (0 : Euclidean n) Rwork))
      (hU := isOpen_ball) (T := (T i)) (c := (c i)) (C := (C i))
      (hP := (hP i)) (K := (closedBall (0 : Euclidean n) bRadius)) (hK := (isCompact_closedBall _ _)) (hKU := (closedBall_subset_ball hbR))
      (hball := (hball i)) (D := (D i)) (zCell := (zCell i)) (L := (L i))
      (hL := (hL i)) (Jfull := (Jfull i)) (hJfull := (hJfull i)) (zFull := (zFull i))
      (σfull := (σfull i)) (hσfull := (hσfull i)) (hJfullEq := (hJfullEq i)) (hJphysical := (hJphysical i))
      (hJphase := (hJphase i)) (Wfull := (Wfull i)) (hWfull := (hWfull i)) (hJfullW := (hJfullW i))
      (E := (E i)) (hE := (hE i)) (hgraph := (hgraph i)) (hDE := (hDE i))
      (hfield := (hfield i)) (hphase := (hphase i)) (adet := (adet i)) (ρdet := (ρdet i))
      (hρdet := (hρdet i)) (hxdet := (hxdet i)) (hdet := (hdet i)) (hmaps := (hmaps i))
      (z₀ := (z₀ i)) (hz₀ := (hz₀ i)) (hcenter := (hcenter i)) (ηb := (ηb i))
      (hηb := (hηb i)) (r := (r i)) (a := (a i)) (r' := (r' i))
      (a' := (a' i)) (hr := (hr i)) (hr' := (hr' i)) (ha' := (ha' i))
      (hcell := (hcell i)) (hcap := (hcap i)) (ha := (ha i)) (har := (har i))
      (haR := (haR i)) (hrr := (hrr i)) (haa := (haa i)) (har' := (har' i))
      (hcarrier := (hcarrier i)) (houter := (houter i)) (hsupport := (hsupport i)) (p₀ := (p₀ i))
      (hp₀ := (hp₀ i)) (q₀ := (q₀ i)) (ρ := (ρ i)) (τ := (τ i))
      (hρ := (hρ i)) (hτ := (hτ i)) (haρ := (haρ i)) (hrρ := (hrρ i))
      (W := (W i)) (Bi := (Bi i)) (hW := (hW i)) (hKiW := (hKiW i))
      (hBi := (hBi i)) (hWBi := (hWBi i)) (hBiDom := (hBiDom i)) (hfoot := (hfoot i))
      (It := (It i)) (hIt := (hIt i)) (hIIt := (hIIt i)) (hsegT := (hsegT i))
      (hseg := (hseg i)) (A := (A i)) (ε := (ε i)) (gap := (gap i))
      (δgeometry := (δgeometry i)) (hε := (hε i)) (hgap := (hgap i)) (hδgeometry := (hδgeometry i))
      (hfreq := (hfreq i)) (β := (β i)) (cJ := (cJ i)) (hcJ := (hcJ i))
      (Vinv := (Vinv i)) (Linv := (Linv i)) (hVinv := (hVinv i)) (hLVinv := (hLVinv i))
      (Ginv := (Ginv i)) (hgeometry := (hgeometry i)) (Ωflow := (Ωflow i)) (Kflow := (Kflow i))
      (Rc := (Rc i)) (Bflow := (Bflow i)) (τflow := (τflow i)) (Mc := (Mc i))
      (hRc := (hRc i)) (hτflow := (hτflow i)) (hMc := (hMc i)) (hEcylinder := (hEcylinder i))
      (hElabel := (hElabel i)) (hEtime := (hEtime i)) (hDouter := (hDouter i))
  choose δlocal hδlocal CscalarLocal hCscalarLocal hlocal using hlocal
  obtain ⟨δframe, hδframe, hδall⟩ := Pi.exists_forall_pos_add_lt hδlocal
  obtain ⟨C₁₅, hC₁₅, hscalar₁₅⟩ := DensityScalar.exists_initial_leading_bounds n
  let Cscalar := 1 + C₁₅ + ∑ i, CscalarLocal i
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ (hCscalarLocal i).le)
  have hCscalarOne : 1 ≤ Cscalar := by
    dsimp [Cscalar]
    linarith only [hsum, hC₁₅]
  have hCscalar : 0 < Cscalar := zero_lt_one.trans_le hCscalarOne
  have hC₁₅Le : C₁₅ ≤ Cscalar := by
    dsimp [Cscalar]
    linarith only [hsum]
  have hCscalarLe (i : ι) : CscalarLocal i ≤ Cscalar := by
    have hs := Finset.single_le_sum (s := Finset.univ)
      (fun j _ ↦ (hCscalarLocal j).le) (Finset.mem_univ i)
    dsimp [Cscalar]
    linarith only [hs, hC₁₅]
  obtain ⟨cap, hcap, hcapone, hadmission⟩ := exists_source_history_row_geometry Href hb hbR hR hδframe
  refine ⟨cap, hcap, hcapone, Cscalar, hCscalar, hCscalarOne, ?_, ?_⟩
  · intro p R hR σ hσ v hv hpos hinterval hnorm
    obtain ⟨_, _, hreg, hbound, hlower, _⟩ := hscalar₁₅ p hR hσ v hv hpos hinterval hnorm
    exact ⟨hreg, hbound.trans (mul_le_mul_of_nonneg_left hC₁₅Le hσ.le), hlower⟩
  intro σ hσ Bband hBband rStar kMin hStar horder Bfull Bnull hBfull μ rInner hμ hμcell hrInner hInnerCell
    hRimage hImageCell χcoeff hχcoeff hsCoeff g Mlimit hglobalGap Mphysical Sgap _hSgap
    coeffHistory hcoeffHistory χ χsrc ψ γ angular hcarriers
  let Gref := sourceDilationReference Href hσ.1 (hσ.2.trans hcapone)
  have hγ : 0 < γ := half_pos (half_pos hglobalGap)
  have h8 : 8 ≤ rStar := by unfold canonicalCarrierLowOrder at hStar; omega
  obtain ⟨κ, hκ, Sgeom, hSgeom, hhistoryGeometry⟩ := hadmission σ hσ hBband hStar horder (δimage := 1) zero_lt_one
  let MF := cNorm (closedBall (0 : Euclidean n) bRadius) (2 * (n + 1) + 14)
    (sourceDilation Href.map σ) + 1
  have hMF : 0 ≤ MF := by
    exact add_nonneg (cNorm_nonneg ..) zero_le_one
  choose Cbaseline hCbaseline Cprofile Craw hCprofile hCraw hlocal using
    fun i ↦ hlocal i (Bfull i) (hBfull i) (Bnull i)
      (σ := σ) (MF := MF) (κmet := 1 / 4) (κ := κ) hσ.1 hMF (by norm_num) hκ
  obtain ⟨Pimage, hPimage, Timage, _hTimage, himage⟩ :=
    exists_prescribed_history_image_coefficient_profiles Gref
      (r := 5 * μ) (R := 6 * μ) (by positivity) (by linarith only [hμ])
      hRimage (by linarith only [hImageCell, hμ]) hχcoeff hsCoeff hBband h8 horder
  obtain ⟨Cell, hCell, Telliptic, _hTelliptic, helliptic⟩ :=
    exists_prescribed_history_elliptic_estimates_with_exterior hn hμ hμcell ψ
      (ContinuumNormal.innerCutoff_smooth hrInner hInnerCell) Gref (closedBall 0 bRadius) Kin
      (rCoeff := 5 * μ) (Rimage := 6 * μ) (by positivity) (by linarith only [hμ])
      hRimage (by linarith only [hImageCell, hμ]) hχcoeff hsCoeff Cprofile (fun i p ↦ (hCprofile i p).le)
      Cbaseline (fun i ↦ (hCbaseline i).le) hBband h8 horder hγ
  obtain ⟨Cadj, hCadj, hadjoint⟩ := exists_measured_retained_augmented_bounds Gref
    (isCompact_closedBall (0 : Euclidean n) bRadius) (6 * μ) Kin (δ := 1) zero_le_one
    χ χsrc ψ (FixedCutoffs.periodic_smooth hμ hμcell 1)
    (FixedCutoffs.periodic_smooth hμ hμcell 2)
    (ContinuumNormal.innerCutoff_smooth hrInner hInnerCell)
    Pimage (fun j ↦ (hPimage j).le) Craw hCraw
  let Cinv := bootstrapConstant γ Cell
  have hCinv (s : ℕ) : 0 ≤ Cinv s := bootstrapConstant_nonneg hγ hCell s
  let Cpair := fun s ↦ Cinv s + Cadj s * (Cinv s + γ⁻¹)
  have hCpair (s : ℕ) : 0 ≤ Cpair s :=
    add_nonneg (hCinv s) (mul_nonneg (hCadj s) (add_nonneg (hCinv s) (inv_nonneg.mpr hγ.le)))
  obtain ⟨Ccoef, hCcoef, hcoefficient⟩ := exists_uncorrected_physical_coefficient_profile
    Gref bRadius (6 * μ) Kin σ hBband hStar horder
  let Czero := fun s ↦ Cpair s * (1 + Ccoef s)
  have hCzero (s : ℕ) : 0 ≤ Czero s :=
    mul_nonneg (hCpair s) (add_nonneg zero_le_one (hCcoef s))
  let S := max Sgeom (max Sgap (max Timage Telliptic))
  refine ⟨Cinv, Cadj, Cpair, Czero, hCinv, hCadj, hCpair, hCzero, S,
    hSgeom.trans (le_max_left _ _), ?_⟩
  intro R₀ hR₀ stage u ell hu F current Φ Y O Vcomp hdata hcomp hsolution
    coeff hformula v hv hpos hinterval hvnorm initial e
  have hRgeom : Sgeom ≤ R₀ := (le_max_left _ _).trans hR₀
  have hRgap : Sgap ≤ R₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hR₀
  have hRimage' : Timage ≤ R₀ :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hR₀
  have hRelliptic : Telliptic ≤ R₀ :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hR₀
  obtain ⟨hF, hi, hrank, hFM, hmet, hnormal, hframe, hnear⟩ :=
    hhistoryGeometry R₀ hRgeom stage u ell hu
  obtain ⟨Vop, hVop, hphysical, hgapActual⟩ :=
    hcarriers R₀ hRgap stage u ell hu current v hv hpos hinterval hvnorm
  have hcoeffEq : coeffHistory R₀ hRgap stage u ell hu = coeff := by
    funext j
    apply ContinuousMap.ext
    intro x
    exact (hcoeffHistory R₀ hRgap stage u ell hu j x).trans (hformula j x).symm
  rw [hcoeffEq] at hphysical hgapActual
  let bamp := fun i ↦ fullReflectedMatrixAmplitude
    (coefficientsOfCarrier (e i) (FixedCutoffs.physical (ha' i) 1)) (symbolJacobian (T i) (current i).Q)
    (symbolInverse (T i) (current i).Q (z₀ i) (ηb i) (r i) (6 * a i))
    (symbolDomain (T i) (current i).Q (z₀ i) (ηb i) (r i) (6 * a i))
    (closedBall (spectatorCenter (z₀ i)) (a' i / 2))
  have hprofile (i : ι) := by
    obtain ⟨hO, hOU, hOphase, hJ₂O, hWO, hgraphO, hcompE⟩ := hdata i
    have hframei : cNorm (closedBall (0 : Euclidean n) bRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < δlocal i :=
      hframe.trans (by simpa only [zero_add] using hδall i)
    exact hlocal i F hF.contDiffOn hi hrank
      (by simpa only [canonicalCarrierLowOrder, MF] using hFM)
      hmet hnormal hframei (row i) (col i) (current i) (hforward i F (current i))
      (Φ i) (Y i) (O i) (Vcomp i) hO hOU hOphase hJ₂O hWO hgraphO hcompE (hcomp i)
      (fun initial hsm hnorm hlower ↦ hsolution i initial hsm
        (hnorm.trans (mul_le_mul_of_nonneg_left (hCscalarLe i) hσ.1.le)) hlower)
      (v i) (hv i) (hpos i) (hinterval i) (hvnorm i) (Vop i) (hVop i).1
      (fun w ↦ ((hVop i).2 w).2)
  choose hb hs hB hbase hhigh hnormalOp hraw using hprofile
  obtain ⟨hcsmooth, hcjets⟩ := himage R₀ hRimage' stage u ell hu coeff hformula
  let V := fun i ↦ CommonMeasurement.restrictCarrier χ (Vop i)
  let image := imageChannel coeff χ χsrc
  let Arow := augmentedRow image V ψ
  let Nop := augmentedNormal image V ψ
  let Slevel := periodicSobolevScale n (Euclidean n)
  let X := augmentedInputSobolevScale n ι
  let Hcoef := retainedCoefficientProfile (closedBall 0 bRadius) (closedBall 0 (6 * μ)) Kin F initial
  have hgap : ∀ w : OutputL2 n, γ * ‖w‖ ^ 2 ≤ ‖Arow.adjoint w‖ ^ 2 := hgapActual
  have hnormalGap := CoerciveInverse.normalOperator_gap Arow hgap
  obtain ⟨hreg, _hstep, hinv⟩ := helliptic R₀ hRelliptic stage u ell hu coeff hformula
    initial bamp hb (fun i p hp l j ↦ hhigh i p (by omega) l j) hbase
    (fun i ↦ 4 * a' i) Cbaseline hs hB Vop hnormalOp hnormalGap
  have hrawActual := hadjoint F hF (hnear μ) coeff hcsmooth hcjets initial e Vop
    (fun i w ↦ ((hVop i).2 w).2) hraw
  have hrawBound (s : ℕ) (w : OutputL2 n) (hw : w ∈ Slevel.level s) :
      Arow.adjoint w ∈ X.level s ∧ X.gradeNorm s (Arow.adjoint w) ≤ Cadj s *
        (Slevel.gradeNorm s w + (1 + Hcoef (s + (2 * (n + 1) + 14))) * ‖w‖) := by
    obtain ⟨hm, hbnd⟩ := hrawActual s w hw
    refine ⟨hm, hbnd.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (hCadj s)
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
    have hdom := cNorm_union_for_original_history (isCompact_closedBall 0 bRadius)
      (isCompact_closedBall 0 (6 * μ)) hF (s + (2 * (n + 1) + 14))
    dsimp only [Hcoef, retainedCoefficientProfile]
    simp only [Nat.add_assoc] at hdom ⊢
    linarith only [hdom]
  have hpair (s : ℕ) (w : OutputL2 n) (hw : w ∈ Slevel.level s) :
      CoerciveInverse.rightInverse Arow w ∈ X.level s ∧
      Slevel.gradeNorm s (Nop.inverse w) + X.gradeNorm s (CoerciveInverse.rightInverse Arow w) ≤
        Cpair s * (Slevel.gradeNorm s w + (1 + Hcoef (s + (2 * (n + 1) + 14))) * ‖w‖) := by
    have hinvw := hinv s w hw
    refine ⟨(hrawBound s _ hinvw.1).1, ?_⟩
    exact inverse_add_rightInverse_gradeNorm_le Slevel X Arow hγ hgap (hCadj s)
      (add_nonneg zero_le_one (retainedCoefficientProfile_nonneg _ _ _ _ _ _))
      hinvw.1 hinvw.2 (fun v hv ↦ (hrawBound s v hv).2)
  refine ⟨Vop, hVop, hcsmooth, hphysical, hgap, CoerciveInverse.norm_inverse_le Nop hγ hnormalGap,
    hreg, hinv, hrawBound, CoerciveInverse.apply_rightInverse Arow hγ hgap,
    hpair, ?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro w
    exact CoerciveInverse.apply_inverse Nop hγ hnormalGap w
  · apply ContinuousLinearMap.ext
    intro w
    exact CoerciveInverse.inverse_apply Nop hγ hnormalGap w
  · intro residual s
    exact (hrawBound s _ (hinv s _ (CurrentMean.smoothResidualToL2_mem residual s)).1).1
  · intro hvzero s w hw
    have hRtwo : 2 ≤ R₀ := hSgeom.trans hRgeom
    have hc := hcoefficient R₀ hRtwo stage u ell hu s
    have hhighZero : 1 + Hcoef (s + (2 * (n + 1) + 14)) ≤
        Ccoef s * (currentCoefficientScale R₀ stage) ^
          (s - (rStar - canonicalCarrierLowOrder n)) := by
      simpa only [Hcoef, F, Gref, sourceDilationReference_map, initial, hvzero,
        Pi.zero_apply, positiveDensityAmplitude_zero, canonicalCarrierLowOrder] using hc
    apply (hpair s w hw).2.trans
    apply (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hhighZero (norm_nonneg w))) (hCpair s)).trans
    have hpow : 0 ≤ (currentCoefficientScale R₀ stage) ^
        (s - (rStar - canonicalCarrierLowOrder n)) :=
      pow_nonneg (zero_le_one.trans (one_le_currentCoefficientScale (by linarith) stage)) _
    have hdom : Slevel.gradeNorm s w + Ccoef s *
        (currentCoefficientScale R₀ stage) ^ (s - (rStar - canonicalCarrierLowOrder n)) * ‖w‖ ≤
        (1 + Ccoef s) * (Slevel.gradeNorm s w +
          (currentCoefficientScale R₀ stage) ^ (s - (rStar - canonicalCarrierLowOrder n)) * ‖w‖) := by
      nlinarith only [mul_nonneg (hCcoef s) (Slevel.gradeNorm_nonneg s w),
        mul_nonneg hpow (norm_nonneg w)]
    exact (mul_le_mul_of_nonneg_left hdom (hCpair s)).trans_eq (by
      dsimp only [Czero]
      ring)

/-- Compatibility erases only additional scalar certificates, never changes
any inverse conclusion. The strong current keeps them on its one chosen budget. -/
theorem discard_extra_scalar_admission {Admission : ℝ → Prop}
    {Tail : ℝ → ℝ → Prop}
    (h : ∃ cap > (0 : ℝ), cap ≤ 1 ∧ ∃ C > (0 : ℝ),
      1 ≤ C ∧ Admission C ∧ Tail cap C) :
    ∃ cap > (0 : ℝ), cap ≤ 1 ∧ ∃ C > (0 : ℝ), Tail cap C := by
  obtain ⟨cap, hcap, hone, C, hC, _, _, htail⟩ := h
  exact ⟨cap, hcap, hone, C, hC, htail⟩

end JanetCartan.PhysicalNormalInverse

retain_original_inverse_cap_interface
