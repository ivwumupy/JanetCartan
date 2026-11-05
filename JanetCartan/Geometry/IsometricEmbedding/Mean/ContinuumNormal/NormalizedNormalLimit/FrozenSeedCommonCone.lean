module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.FrozenSourceMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.CommonCone

/-!
# Original seed zero amplitude on the selected common cone

The positive anchor proves geometry only. The original seed coefficients and
both density factors remain fixed while its canonical zero inverse and full
mask image transfer to the selected cone. This supplies exact normal-witness
matching for the genuine zero-density realization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic FrozenModel RetainedFrozen NullTransport
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation.FamilyInputs NormalizedBackground.SourceGeometry NormalizedSelection CarrierVariation

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
include hF hrank hphysical hseed htrans hσ hσ1 hscaled

variable {c C : ℝ} (hP : P.IsValid c C)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hgeometry : RetainedSpectralGeometry T Qσ zRoot ηb r a)

include hP hηb hr hgeometry

/-- The original seed's spatially weighted full amplitude is unchanged on
the SAME selected common cone. A positive source supplies the frozen geometry;
no inverse, phase, normal or reduced coefficient of the unscaled seed is
replaced. The weight is arbitrary, so the genuine divided-footpoint weight
and the distinct origin weight both satisfy this exact identity. Consumer:
the zero branch of `exists_selected_source_family_normal_control`, through
`SourceDensityLimitRealization.realized_normal_eq_of_amplitude_witnesses`
(`app:ch_background:prop:bg-normalized`, `bg-Nsigma`,
`bg-full-complex-amplitude`, `bg-real-symbol`). -/
theorem seed_zero_weighted_fullAmplitudes_eq_common_cone_of_source
    (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r' a' : ℝ} (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell : 4 * a' < 1 / 2)
    {Ωcommon : Set (Variables n × Euclidean 2)}
    (hcommon : Ωcommon ⊆ frozenSymbolDomain T Qσ zRoot ηb r (6 * a))
    (hbuffer : closure (augmentedTransportGradient (normalizedTransportPosition T Qσ 0) ''
      conicMaskSupport zRoot ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆ Ωcommon)
    (w : Euclidean n × CarrierParameter → ℝ) (S : Set (Euclidean 2)) :
    let e := normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) ha' hcell
      (angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
      FixedCutoffs.highFrequency 0
    let a₀ := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
    let d := {a₀ with normal := fun p ↦ w p • a₀.normal p}
    let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q₀ 0)
    let u := frozenSymbolInverse T Q₀ zRoot ηb r (6 * a)
    let Ω := frozenSymbolDomain T Q₀ zRoot ηb r (6 * a)
    extendedDensity d J u Ω = extendedDensity d J u Ωcommon ∧
      fullComplexMatrixAmplitude d J u Ω S = fullComplexMatrixAmplitude d J u Ωcommon S ∧
      fullReflectedMatrixAmplitude d J u Ω S = fullReflectedMatrixAmplitude d J u Ωcommon S := by
  intro e a₀ d J u Ω
  have hinv := frozenSymbolInverse_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans
    hσ hσ1 hscaled hP hηb hr hgeometry
  obtain ⟨har, hcarrier, G, β, cJ, Vi, Li, _hcJ, _hVi, _hLi, _hf, hInv, htransverse, _hslice⟩ := hgeometry
  have hdom := frozenSymbolDomain_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans
    hσ hσ1 hscaled hP (ηb := ηb) hr har hcarrier
  have haug := (source_frozen_transport_geometry_eq T Q₀ Qσ hF hrank hphysical hseed htrans
    hσ hσ1 hscaled hP (ηb := ηb) hr har hcarrier).1
  have hmap : MapsTo (inverseCoordinates u) Ω (frozenInputDomain zRoot ηb r (6 * a)) := by
    dsimp only [u, Ω]
    rw [← hinv, ← hdom]
    exact frozenSymbolInverse_maps T Qσ hηb hr hInv htransverse
  have hright : ∀ p ∈ Ω, augmentedTransportGradient (normalizedTransportPosition T Q₀ 0)
      (inverseCoordinates u p) = p := by
    intro p hp
    calc
      _ = augmentedTransportGradient (normalizedTransportPosition T Qσ 0)
          (inverseCoordinates u p) := (haug (hmap hp)).symm
      _ = p := by
        dsimp only [u] at *
        rw [← hinv]
        exact augmentedFrozenGradient_inverse T Qσ hP hηb hr har hcarrier hInv htransverse
          (by rwa [hdom])
  have hsub : Ωcommon ⊆ Ω := by
    dsimp only [Ω]
    rwa [← hdom]
  have hinput : conicMaskSupport zRoot ηb r' a' ⊆ frozenInputDomain zRoot ηb r (6 * a) := by
    intro p hp
    have hi := (conicMaskSupport_subset hηb hr' ha' har').trans
      (symbolInputDomain_mono zRoot ηb hrr (mul_le_mul_of_nonneg_left haa (by norm_num)))
      (originInput_mem_conicMaskSupport ha'.le hp)
    exact hi
  have hbuffer' : augmentedTransportGradient (normalizedTransportPosition T Q₀ 0) ''
      conicMaskSupport zRoot ηb r' a' ⊆ Ωcommon := by
    rintro _ ⟨p, hp, rfl⟩
    rw [← haug (hinput hp)]
    refine hbuffer ⟨subset_closure ⟨p, hp, rfl⟩, ?_⟩
    change transportAveragedGradient (normalizedTransportPosition T Qσ 0) p ≠ 0
    rw [frozenForward_eq_origin T Qσ hP hr har hcarrier (hinput hp)]
    exact transportGradient_ne_zero T Qσ hηb hr htransverse (hinput hp)
  have hext : extendedDensity d J u Ω = extendedDensity d J u Ωcommon := by
    apply extendedDensity_common_conic_target d J J u u
      (augmentedTransportGradient (normalizedTransportPosition T Q₀ 0))
      hsub hmap hright _ hbuffer' (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    intro p hp hx hy hang _
    exact primitive_masks_mem_conicMaskSupport hηb hr' ha' hp.2.2.1 hx hy hang
  have hamp : amplitude d J u Ω S = amplitude d J u Ωcommon S := by
    funext p
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ congrFun hext (p, z)))
  refine ⟨hext, ?_, ?_⟩
  · funext ξ z i j
    simp only [fullComplexMatrixAmplitude, hamp]
  · funext ξ z i j
    simp only [fullReflectedMatrixAmplitude, reflectedSymbolAmplitude, hamp]

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
