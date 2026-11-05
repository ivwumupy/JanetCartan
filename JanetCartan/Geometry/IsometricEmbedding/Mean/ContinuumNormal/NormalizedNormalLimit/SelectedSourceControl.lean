module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.CanonicalSourceFamily
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.SeedAdmission

/-!
# Source normal comparison on the supplied selected chart family

Apply the actual source-stress admission theorem to the fixed finite selector's
current and frozen geometric projections. The actual source charts are supplied
once; no chart, conic inverse or mask family is selected here. Admission supplies
both branches of the canonical reflected-normal comparison on a common cap.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic NormalizedSelection FrozenModel RetainedFrozen
open ContinuumNormalReduction.TransportSymbol ContinuumRow.CarrierNormalRealization
open CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.RetainedRowGeometry
open CarrierVariation.FamilyInputs.PositiveReference CarrierVariation.FamilyInputs.WideDensity
open PositiveReference.FlowConstruction
open NullTransport ActualFlow FlowAmplitude NormalizedBackground.SourceGeometry
open Pseudodifferential AmplitudeBound PeriodicLocalL2

/-- Apply the normalized full-amplitude comparison to the SAME supplied
finite source chart family. The original finite selector's `hgeometry` is
used only through its current/frozen containment, inverse-range, differential,
Jacobian and normalized-mask-image projections. Its concrete producer is
`NormalizedSelection.exists_finite_incidence_comparison_inputs`; the Jacobian
bound on its outer buffer restricts to `K`. No amplitude or operator difference
is assumed.

`SourceMatching.exists_joint_stress_scale_interval` admits every supplied
source chart on a single cap. Its positive midpoint supplies the frozen
geometry, transferred to the original seed by exact source matching. The
original density domains, masks, spectator measures and chart choices remain
fixed. Absolute budgets precede the requested gap, and the final common cap
precedes source scale and all original `μ+14` densities. Consumers:
`exists_initialized_source_family_coercivity` and `SourceInverse`
(`app:ch_background:prop:bg-normalized`, `bg-Nsigma`,
`bg-full-complex-amplitude`, `bg-real-symbol`, `bg-uniform-normalized`). -/
theorem exists_selected_source_family_quarter_gap
    {n : ℕ} {ι : Type} [Fintype ι] (hn : 0 < n) (H : FlatReference n)
    {P : ι → Patch n} {c C : ℝ} (hP : ∀ i, (P i).IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (hUG : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    (T : (i : ι) → PatchQuantitativeFamily (P i) U hU)
    {Ωflow : ι → Set (Euclidean n × Euclidean 3)} (hΩflow : ∀ i, IsOpen (Ωflow i))
    {zCell : ι → Euclidean 3} {ρc Rc Bflow τflow : ι → ℝ} {row col : ι → Fin n}
    (hKΩ : ∀ i, closedBall ((0 : Euclidean n), zCell i) (ρc i) ⊆ Ωflow i)
    (hΩpatch : ∀ i, Ωflow i ⊆ (U ∩ ball 0 (T i).physicalRadius) ×ˢ
      parameterInterior (3 * (P i).radius / 2))
    (hRc : ∀ i, 0 < Rc i) (hτ : ∀ i, 0 < τflow i) (hτR : ∀ i, τflow i ≤ Rc i / 16)
    (hbuffer : ∀ i, MapsTo (coordinates (adaptedCoordinates (T i).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell i)) (Rc i))
      (closedBall ((0 : Euclidean n), zCell i) (ρc i)))
    (hphysical : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ U)
    (seed : (i : ι) → Chart (T i) (Ωflow i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
      ((0 : Euclidean (n - 1)), zCell i) (Rc i) (Bflow i) (τflow i) (row i) (col i) H.map)
    (htrans : ∀ i q, q ∈ closedBall (0, (T i).data.center) (T i).data.localReference.stateRadius →
      ⟪(normalizedHomogeneousSymbol hU (seed i).Q.1 (seed i).Q.2.1).hp q,
        (T i).data.adapted.normal⟫_ℝ ≠ 0)
    {L Mc R : ι → ℝ} (hL : ∀ i, 0 < L i) (hMc : ∀ i, 0 < Mc i) (hR : ∀ i, 0 < R i)
    (hforward : ∀ i, cNorm (Icc (-τflow i) (τflow i) ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8)) 1 (seed i).forward ≤ Mc i)
    (hRT : ∀ i, R i ≤ (T i).physicalRadius) (hRU : ∀ i, ball (0 : Euclidean n) (R i) ⊆ U)
    (hRtime : ∀ i, R i ≤ L i / (64 * Mc i))
    {V : ι → Set CarrierParameter} (hV : ∀ i, IsOpen (V i))
    (hVP : ∀ i, V i ⊆ parameter ⁻¹' parameterInterior (3 * (P i).radius / 2))
    (hflow : ∀ i, MapsTo (densityCoordinates (T i)) (ball (0 : Euclidean n) (R i) ×ˢ V i)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell i) (Rc i) (τflow i)))
    (hlabel : ∀ i p, p ∈ ball (0 : Euclidean n) (R i) ×ˢ V i →
      (densityCoordinates (T i) p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 64))
    (D : ι → CoefficientNormCharts n)
    (hD : ∀ i, (D i).field.region ⊆ ball (0 : Euclidean n) (R i) ×ˢ V i)
    {zRoot : ι → Euclidean 3} {ηb : ι → Euclidean (n - 1)} {r a r' a' : ι → ℝ}
    (hηb : ∀ i, ηb i ≠ 0) (hr : ∀ i, 0 < r i) (hr' : ∀ i, 0 < r' i) (ha' : ∀ i, 0 < a' i)
    (hrr : ∀ i, r' i ≤ r i) (haa : ∀ i, a' i ≤ a i) (har' : ∀ i, a' i ≤ r' i)
    (hcell : ∀ i, 4 * a' i < 1 / 2)
    (houter : ∀ i, coefficientDomain (zRoot i) (r i) (6 * a i) ⊆
      ball (0 : Euclidean n) (R i) ×ˢ V i)
    {K W : ι → Set (InputVariables n)} {Q Ω : ι → Set (Variables n × Euclidean 2)}
    (hK : ∀ i, IsCompact (K i)) (hconv : ∀ i, Convex ℝ (K i))
    (hW : ∀ i, IsOpen (W i)) (hKW : ∀ i, K i ⊆ W i)
    (hWinput : ∀ i, W i ⊆ symbolInputDomain (zRoot i) (ηb i) (r i) (6 * a i))
    (hQ : ∀ i, IsCompact (Q i)) (hΩ : ∀ i, IsOpen (Ω i)) (hQΩ : ∀ i, Q i ⊆ Ω i)
    (hne : ∀ i q, q ∈ Ω i → q.1.2.2 ≠ 0)
    (hcone : ∀ i t, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ω i ↔ q ∈ Ω i)
    (hcontains : ∀ i p, p ∈ K i → (D i).Contains p)
    {It : ι → Set ℝ} (hIt : ∀ i, IsOpen (It i)) (hIIt : ∀ i, Icc (0 : ℝ) 1 ⊆ It i)
    (hseg : ∀ i t, t ∈ It i → MapsTo (transportSegmentInput n t) (W i) (D i).field.region)
    (hend : ∀ i side, MapsTo (densityEndpoint side) (W i) (D i).field.region)
    {η jacobianGap : ι → ℝ} {sourceCap : ℝ}
    (hη : ∀ i, 0 < η i) (hjacobianGap : ∀ i, 0 < jacobianGap i)
    (hsourceCap : 0 < sourceCap) (hcap1 : sourceCap ≤ 1)
    (hfreq : ∀ i p, p ∈ K i → η i ≤ ‖p.2.2‖)
    (A : ι → InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (current : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) sourceCap → (i : ι) →
      Chart (T i) (Ωflow i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
        ((0 : Euclidean (n - 1)), zCell i) (Rc i) (Bflow i) (τflow i) (row i) (col i)
        (sourceDilation H.map σ))
    (δgeometry : ι → ℝ) (hδgeometry : ∀ i, 0 < δgeometry i)
    (hgeometry : ∀ i (F : Euclidean n → Euclidean (embeddingDimension n))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < δgeometry i →
      let QF := ⟨ProjectedStressFrame.projectedStress F,
        contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      RetainedSpectralGeometry (T i) QF (zRoot i) (ηb i) (r i) (a i) ∧
      (Ω i ⊆ symbolDomain (T i) QF (zRoot i) (ηb i) (r i) (6 * a i) ∧
      MapsTo (inverseCoordinates (symbolInverse (T i) QF (zRoot i) (ηb i) (r i) (6 * a i)))
        (Q i) (K i) ∧
      MapsTo (fun q ↦ inverseCoordinates (symbolInverse (T i) QF (zRoot i) (ηb i) (r i) (6 * a i))
        (normalizeOutputRadius (1 / 4) q)) (Ω i) (K i) ∧
      (∀ p ∈ K i, ‖(A i).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition (T i) QF)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K i, jacobianGap i ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
        (transportPosition (T i) QF) p) ∧
      (∀ p ∈ conicMaskSupport (zRoot i) (ηb i) (r' i) (a' i), normalizeOutputRadius (1 / 4)
        (augmentedTransportGradient (transportPosition (T i) QF) p) ∈ Q i)) ∧
      (Ω i ⊆ frozenSymbolDomain (T i) QF (zRoot i) (ηb i) (r i) (6 * a i) ∧
      MapsTo (inverseCoordinates (frozenSymbolInverse (T i) QF (zRoot i) (ηb i) (r i) (6 * a i)))
        (Q i) (K i) ∧
      MapsTo (fun q ↦ inverseCoordinates
        (frozenSymbolInverse (T i) QF (zRoot i) (ηb i) (r i) (6 * a i))
        (normalizeOutputRadius (1 / 4) q)) (Ω i) (K i) ∧
      (∀ p ∈ K i, ‖(A i).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition (T i) QF 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K i, jacobianGap i ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
        (normalizedTransportPosition (T i) QF 0) p) ∧
      (∀ p ∈ conicMaskSupport (zRoot i) (ηb i) (r' i) (a' i), normalizeOutputRadius (1 / 4)
        (augmentedTransportGradient (normalizedTransportPosition (T i) QF 0) p) ∈ Q i))) :
    let Qcurrent := fun i σ ↦ if hσ : σ ∈ Ioc (0 : ℝ) sourceCap
      then (current σ hσ i).Q else (seed i).Q
    let μ := 2 * (n + 1)
    let angular := fun i ↦ angularMask (zRoot i) (NormedSpace.normalize (ηb i)) (ha' i)
      (angularWidth_spec (hηb i) (hr' i)).1
    let d := fun i σ ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData (T i) (seed i).Q H.map (row i) (col i) (seed i).forward (seed i).inverse (fun _ ↦ 1)
        (ha' i) (hcell i) (angular i) FixedCutoffs.highFrequency σ) (FixedCutoffs.physical (ha' i) 1)
    let J := fun i σ ↦ transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
      (normalizedTransportPosition (T i) (seed i).Q σ)
    let u := fun i σ ↦ if σ = 0 then frozenSymbolInverse (T i) (seed i).Q (zRoot i) (ηb i) (r i) (6 * a i)
      else symbolInverse (T i) (Qcurrent i σ) (zRoot i) (ηb i) (r i) (6 * a i)
    let S := fun i ↦ closedBall (spectatorCenter (zRoot i)) (a' i / 2)
    let b := fun i σ (v : Euclidean (n - 1) × Euclidean 3 → ℝ) ↦
      fullReflectedMatrixAmplitude
        {d i σ with normal := fun p ↦ Real.sqrt (1 + v
          (sourceDensityFootpointExtension (T i) (seed i).inverse (σ, p))) • (d i σ).normal p}
        (J i σ) (u i σ) (Ω i) (S i)
    ∃ B : ι → ℝ, (∀ i, 0 < B i) ∧ ∀ gap > (0 : ℝ),
    let tol := gap / (4 * ((Fintype.card ι : ℝ) + 1))
    ∃ cap > (0 : ℝ), cap ≤ sourceCap ∧ cap ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) cap, ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ i y, y ∈ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8) → ContDiffAt ℝ ∞ (v i) y) →
      (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8)) (μ + 14) (v i) ≤ 1) →
      (∀ i y, y ∈ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8) → (1 / 2 : ℝ) ≤ 1 + v i y) →
      let pair := fun (t : Fin 2) i ↦ b i (![σ, 0] t) (v i)
      (∀ i j k, HasAmplitudeDerivativeBound (fun ξ z ↦ pair 0 i ξ z j k - pair 1 i ξ z j k) μ tol) ∧
      ∃ hb : ∀ t i, ContDiff ℝ ∞ (Function.uncurry (pair t i)),
      ∃ hs : ∀ t i ξ j k, SupportedInCenteredBox (4 * a' i) (fun z ↦ pair t i ξ z j k),
      ∃ hB : ∀ t i j k, HasAmplitudeDerivativeBound (fun ξ z ↦ pair t i ξ z j k) μ (B i),
      let Aop := fun t i ↦ vectorTwoPositionL2Operator hn (4 * a' i) (pair t i) (hb t i) (hs t i) (B i) (hB t i)
      let Nop := fun t i ↦ realOutputCompression (transferOperator (Aop t i))
      (∀ i, ‖Aop 0 i - Aop 1 i‖ ≤ tol ∧
        ‖transferOperator (Aop 0 i) - transferOperator (Aop 1 i)‖ ≤ tol ∧
        ‖Nop 0 i - Nop 1 i‖ ≤ tol) ∧
      (∑ i, ‖Nop 0 i - Nop 1 i‖) ≤ gap / 4 ∧
      ∀ χ : C(Torus n, ℝ), ‖χ‖ ≤ 1 →
        ‖∑ i, (cutoffMultiplier χ ∘L Nop 0 i ∘L cutoffMultiplier χ -
          cutoffMultiplier χ ∘L Nop 1 i ∘L cutoffMultiplier χ)‖ ≤ gap / 4 := by
  classical
  intro Qcurrent μ angular d J u S b
  obtain ⟨εgeometry, hεgeometry, hεgeometry_le⟩ :=
    (finite_range δgeometry).isCompact.exists_forall_le' continuousOn_id
      (by rintro x ⟨i, rfl⟩; exact hδgeometry i)
  obtain ⟨cap₀, hcap₀, _hcap₀one, hadmit⟩ :=
    SourceMatching.exists_joint_stress_scale_interval H hbounded hεgeometry
  let admittedCap := min cap₀ sourceCap
  have hadmittedCap : 0 < admittedCap := lt_min hcap₀ hsourceCap
  have hadmittedSource : admittedCap ≤ sourceCap := min_le_right _ _
  have hadmittedOne : admittedCap ≤ 1 := hadmittedSource.trans hcap1
  have hframe (i : ι) (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) admittedCap) :
      (Qcurrent i σ).1 = ProjectedStressFrame.projectedStress (sourceDilation H.map σ) := by
    have hσsource : σ ∈ Ioc (0 : ℝ) sourceCap := ⟨hσ.1, hσ.2.trans hadmittedSource⟩
    simpa only [Qcurrent, dite_eq_left hσsource] using (current σ hσsource i).frame_eq
  have hgeom (i : ι) (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) admittedCap) := by
    obtain ⟨hiσ, hrankσ, hframeSmooth, hsmall⟩ :=
      hadmit σ hσ.1 (hσ.2.trans (min_le_left _ _))
    have hsmallCell : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (ProjectedStressFrame.projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) <
        δgeometry i := by
      apply ((cNorm_mono_set_of_contDiffAt ((hphysical i).trans subset_closure)
        hbounded.isCompact_closure ?_).trans_lt hsmall).trans_le (hεgeometry_le _ ⟨i, rfl⟩)
      exact fun x hx ↦ ((hframeSmooth x hx).sub contDiffAt_const).of_le (by simp)
    have hFσ : ContDiffOn ℝ ∞ (sourceDilation H.map σ) U :=
      (contDiff_sourceDilation H.contDiff).contDiffOn
    have hlow : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (ProjectedStressFrame.projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) <
        (T i).family.threshold := by
      rw [← hframe i σ hσ]
      exact (Qcurrent i σ).2.2
    have hg := hgeometry i (sourceDilation H.map σ) hFσ hiσ hrankσ hlow hsmallCell
    have hQ : (⟨ProjectedStressFrame.projectedStress (sourceDilation H.map σ),
        contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hFσ hiσ hrankσ),
        hlow⟩ : {QF : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ QF U ∧
          cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
            (QF - fun _ ↦ cubeStress n) < (T i).family.threshold}) = Qcurrent i σ :=
      Subtype.ext (hframe i σ hσ).symm
    dsimp only at hg
    rw [hQ] at hg
    exact hg
  have hanchor : 0 < admittedCap / 2 := half_pos hadmittedCap
  have hanchorMem : admittedCap / 2 ∈ Ioc (0 : ℝ) admittedCap :=
    ⟨hanchor, half_le_self hadmittedCap.le⟩
  have hi : IsImmersionOn H.map U := isImmersionOn_of_isIsometricOn
    (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one) (fun x _ ↦ H.inducedMetric_eq_one x)
  have hrank : HasFullNormalRankOn H.map U := fun x hx ↦ H.fullNormalRank x (hUG hx)
  obtain ⟨B, hB, hcontrols⟩ :=
    exists_retained_canonical_source_family_quarter_gap_of_frozen_source hn hP T
      hΩflow hKΩ hΩpatch hRc hτ hτR hbuffer H.contDiff hi hrank hphysical seed htrans
      (fun x _ ↦ H.inducedMetric_eq_one x) hL hMc hR hforward hRT hRU hRtime hV hVP hflow hlabel
      D hD hηb hr hr' ha' hrr haa har' hcell houter hK hconv hW hKW hWinput hQ hΩ hQΩ
      hne hcone hcontains hIt hIIt hseg hend hη hjacobianGap hadmittedCap hadmittedOne hfreq A
      Qcurrent hframe (fun i ↦ Qcurrent i (admittedCap / 2)) hanchor
      (hanchorMem.2.trans hadmittedOne) (fun i ↦ hframe i _ hanchorMem)
      (fun i ↦ ⟨(hgeom i _ hanchorMem).1, (hgeom i _ hanchorMem).2.2⟩)
      (fun i σ hσ ↦ ⟨(hgeom i σ hσ).1, (hgeom i σ hσ).2.1⟩)
  refine ⟨B, hB, ?_⟩
  intro gap hgap tol
  obtain ⟨cap, hcap, hcapAdmitted, hcapOne, hcontrol⟩ := hcontrols gap hgap
  exact ⟨cap, hcap, hcapAdmitted.trans hadmittedSource, hcapOne, hcontrol⟩

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
