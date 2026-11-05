module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.CommonTarget
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.CoefficientBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.Canonical

/-!
# One retained geometry for the frozen and variation comparisons

The coefficient cap precedes a single application of the joint current/frozen
local construction. Its outer inverse, inner masks, doubled output balls and
supported shells then supply both comparisons on one compact input buffer and
one common open conic target. No second mask family or finite cover is chosen.

Consumers: `RetainedFrozen.UnitRealization.exists_joint_carrier_normal_geometry_with_spectral_geometry`,
`RetainedFrozen.exists_covering_retained_frozen_row_before_geometry`,
`FamilyInputs.exists_retained_conic_weighted_comparison`, and
`SourceWeighted.exists_actual_source_weighted_comparison`. Their parents must
retain these witnesses through one finite incidence selection and instantiate
the actual source, flow, scalar and history inputs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.RetainedJointGeometry
open ContinuumRow UniformConic CanonicalConic FlowConic FrozenModel RetainedFrozen
open CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol
open ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Construct the current and frozen comparison geometry inside the supplied
retained cell from primitive incidence data. The coefficient cap is fixed
before the joint local producer, and every conclusion uses its SAME radii,
outer inverse and full punctured mask image. The lower Jacobian constant,
coefficient domains and common targets precede every admitted projected frame.
Admission is precisely the original C⁶ bound; its source/perturbation producer
is `RetainedRowGeometry.exists_source_cap_and_perturbation_admission`.

The frequency section is `‖k‖`, with no unit normalization: applying this
construction to the positive representative `t • k` selected by
`exists_small_incidence_representative` keeps `‖t • k‖ = 1 / 4` literally.
The parent still owes the primitive supported-constructor application, its
arbitrary reserve and budgets, and one enriched finite cover.
Sources: `app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-jacobian`,
`app:ch_background:prop:bg-frame`, and `new:lem:scaling`. -/
theorem exists_retained_joint_comparison_geometry {c C : ℝ} (hP : P.IsValid c C)
    {zRoot : Euclidean 3} (hzRoot : zRoot ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun zRoot) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) zRoot
      (EuclideanSpace.single 0 1) ≠ 0)
    {N : ℕ}
    {cap : ℝ} (hcap : 0 < cap)
    (E : Set (Euclidean n × CarrierParameter)) (hE : IsOpen E)
    (hcenter : ((0 : Euclidean n), (zRoot 0, spectatorCenter zRoot)) ∈ E) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let p₀ := augmentedInputCenter T (z₀ := zRoot) (k := k)
    let q₀ := frozenAugmentedChart T p₀
    let A := augmentedReferenceEquiv T hP hzRoot hinc hd
    let G := FrozenIncidence.referenceEquiv T hP hzRoot hinc hd
    ∃ r > (0 : ℝ), ∃ a > (0 : ℝ), 6 * a < cap ∧
      coefficientDomain zRoot r (6 * a) ⊆ E ∧ 6 * a ≤ r ∧
      6 * a < T.family.radius ∧ 4 * a < 1 / 2 ∧
      (closedBall (spectatorCenter zRoot) (3 * r) ×ˢ closedBall (zRoot 0) (3 * r) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ ρ > (0 : ℝ), ρ < cap ∧ closedBall p₀ ρ ⊆ symbolInputDomain zRoot ηb r (6 * a) ∧
    ∃ τ > (0 : ℝ), ∃ r' > (0 : ℝ), r' ≤ r ∧ r' ≤ ρ ∧
    ∃ a' : ℝ, ∃ ha' : 0 < a', a' ≤ a ∧ a' ≤ r' ∧ 4 * a' < ρ ∧ 4 * a' < 1 / 2 ∧
    ∃ δ > (0 : ℝ), ∃ cJ > (0 : ℝ), ∃ b > (0 : ℝ),
    ∃ V L : Set (ℝ × Euclidean (n - 1)),
      IsOpen V ∧ IsCompact (closure V) ∧ IsCompact L ∧ L ⊆ V ∧
    ∃ (D : CoefficientNormCharts n) (Ki W Bi : Set (InputVariables n)) (It : Set ℝ)
      (Vphase Lphase : Set (Euclidean n × CarrierParameter)),
      Ki = closedBall p₀ ρ ∧
      IsOpen Vphase ∧ IsCompact Lphase ∧ Lphase ⊆ Vphase ∧
      D.field.region = Vphase ∧ D.field.carrier = Lphase ∧
      (∃ l u : ℝ, It = Ioo l u) ∧
      IsCompact Ki ∧ Convex ℝ Ki ∧ p₀ ∈ interior Ki ∧
      IsOpen W ∧ Ki ⊆ W ∧ IsCompact Bi ∧ W ⊆ Bi ∧
      Bi ⊆ symbolInputDomain zRoot ηb r (6 * a) ∧
      D.field.region ⊆ E ∩ coefficientDomain zRoot r (6 * a) ∧
      (∀ p ∈ Ki, D.Contains p) ∧
      (tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
        carrierSupport zRoot (r := a') ⊆ D.field.carrier) ∧
      IsOpen It ∧ Icc (0 : ℝ) 1 ⊆ It ∧
      (∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier) ∧
      (∀ side, MapsTo (WideDensity.densityEndpoint side) W D.field.carrier) ∧
    ∃ η > (0 : ℝ), (∀ p ∈ Bi, η ≤ ‖p.2.2‖) ∧
    ∃ radialUpper > (0 : ℝ), (∀ p ∈ Bi, ‖p.2.2‖ < radialUpper) ∧
    ∃ Qc Ωi : Set (Variables n × Euclidean 2),
      Qc = compactTarget ‖k‖ q₀ τ ∧ Ωi = conicTarget ‖k‖ q₀ τ ∧
      IsCompact Qc ∧ IsOpen Ωi ∧ Qc ⊆ Ωi ∧
      (∀ q ∈ Qc, ‖q.1.2.2‖ = ‖k‖) ∧ (∀ q ∈ Ωi, q.1.2.2 ≠ 0) ∧
      (∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ωi ↔ q ∈ Ωi) ∧
    ∃ gap > (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < δ →
        let Q := ⟨ProjectedStressFrame.projectedStress F,
          contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        (ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
          (physicalParameterSet zRoot (6 * a) ×ˢ dataSet zRoot ηb (3 * r)) ∧
        (∀ p ∈ physicalParameterSet zRoot (6 * a), ∀ u ∈ dataBox zRoot ηb (2 * r),
          ‖G.symm.toContinuousLinearMap.comp
            (fderiv ℝ (adaptedTransportChart T Q p) u) -
            ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
        BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet zRoot (6 * a))
          (dataBox zRoot ηb r) (dataSet zRoot ηb (2 * r)) (dataBox zRoot ηb (2 * r)) V L b cJ G ∧
        (∀ p ∈ physicalParameterSet zRoot (6 * a),
          ∀ u ∈ supportedCone zRoot (NormedSpace.normalize ηb) r (angularWidth ηb r),
            ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) ∧
        closedBall q₀ (2 * τ) ⊆ symbolDomain T Q zRoot ηb r (6 * a) ∧
        MapsTo (inverseCoordinates (symbolInverse T Q zRoot ηb r (6 * a)))
          (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
        (∀ p ∈ closedBall p₀ ρ,
          ‖(augmentedReferenceEquiv T hP hzRoot hinc hd).symm.toContinuousLinearMap.comp
            (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (closure (augmentedTransportGradient (transportPosition T Q) '' conicMaskSupport zRoot ηb r' a') ∩
          {p | p.1.2.2 ≠ 0} ⊆ symbolDomain T Q zRoot ηb r (6 * a)) ∧
        (∀ x : Variables n, ‖x.2.2‖ = ‖k‖ → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
            conicMaskSupport zRoot ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
        (∀ p ∈ symbolDomain T Q zRoot ηb r (6 * a),
          ‖(symbolInverse T Q zRoot ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖) ∧
        (closedBall q₀ (2 * τ) ⊆ frozenSymbolDomain T Q zRoot ηb r (6 * a) ∧
        MapsTo (inverseCoordinates (frozenSymbolInverse T Q zRoot ηb r (6 * a)))
          (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
        (∀ p ∈ closedBall p₀ ρ,
          ‖(augmentedReferenceEquiv T hP hzRoot hinc hd).symm.toContinuousLinearMap.comp
            (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q 0)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ x : Variables n, ‖x.2.2‖ = ‖k‖ → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
            conicMaskSupport zRoot ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
        (closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
          conicMaskSupport zRoot ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
          frozenSymbolDomain T Q zRoot ηb r (6 * a)))) ∧
        RetainedSpectralGeometry T Q zRoot ηb r a ∧
      (let u := symbolInverse T Q zRoot ηb r (6 * a)
      Ωi ⊆ symbolDomain T Q zRoot ηb r (6 * a) ∧
      ContDiffOn ℝ ∞ u Ωi ∧ MapsTo (inverseCoordinates u) Qc Ki ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius ‖k‖ q)) Ωi Ki ∧
      (∀ q ∈ Ωi, transportAveragedGradient (transportPosition T Q)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ Ki, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q)) W ∧
      EqOn (symbolJacobian T Q)
        (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q)) W ∧
      InjOn (augmentedTransportGradient (transportPosition T Q)) Ki ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport zRoot ηb r' a',
        scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ Ki ∧
        transportAveragedGradient (transportPosition T Q) p ≠ 0 ∧
        normalizeOutputRadius ‖k‖ (augmentedTransportGradient (transportPosition T Q) p) ∈ Qc ∧
        scaleInput (‖k‖ / ‖transportAveragedGradient (transportPosition T Q) p‖) p ∈ Ki ∧
        inverseCoordinates u (augmentedTransportGradient (transportPosition T Q) p) = p) ∧
      (closure (augmentedTransportGradient (transportPosition T Q) ''
        conicMaskSupport zRoot ηb r' a') ∩ {q | q.1.2.2 ≠ 0} ⊆ Ωi)) ∧
      (let u := frozenSymbolInverse T Q zRoot ηb r (6 * a)
      Ωi ⊆ frozenSymbolDomain T Q zRoot ηb r (6 * a) ∧
      ContDiffOn ℝ ∞ u Ωi ∧ MapsTo (inverseCoordinates u) Qc Ki ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius ‖k‖ q)) Ωi Ki ∧
      (∀ q ∈ Ωi, transportAveragedGradient (normalizedTransportPosition T Q 0)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ Ki, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0)) W ∧
      EqOn (frozenKernelJacobian T Q)
        (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0)) W ∧
      InjOn (augmentedTransportGradient (normalizedTransportPosition T Q 0)) Ki ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport zRoot ηb r' a',
        scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ Ki ∧
        transportAveragedGradient (normalizedTransportPosition T Q 0) p ≠ 0 ∧
        normalizeOutputRadius ‖k‖ (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) ∈ Qc ∧
        scaleInput (‖k‖ / ‖transportAveragedGradient (normalizedTransportPosition T Q 0) p‖) p ∈ Ki ∧
        inverseCoordinates u (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) = p) ∧
      (closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
        conicMaskSupport zRoot ηb r' a') ∩ {q | q.1.2.2 ≠ 0} ⊆ Ωi)) := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  let p₀ := augmentedInputCenter T (z₀ := zRoot) (k := k)
  let q₀ := frozenAugmentedChart T p₀
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hzRoot hk hinc
  obtain ⟨capD, hcapD, hbuffers⟩ := exists_coefficient_buffers_cap zRoot ηb hηb E hE hcenter
  obtain ⟨r, hr, a, ha, hacap, houter, har, haR, hcell, hcarrier,
    ρ, hρ, hρcap, hinput, τ, hτ, r', hr', hrr, hrρ, a', ha', haa, har', haρ,
    δ, hδ, cJ, hcJ, β, hβ, V, L, hV, hVc, hL, hLV, hfamily⟩ :=
    RetainedFrozen.UnitRealization.exists_retained_joint_supported_geometry
      (N := N) T hP hzRoot hk hinc hd (lt_min hcap hcapD) E hE hcenter
  obtain ⟨W, Bi, Vphase, Lphase, It, D, ε, hW, hBi, hKiW, hWBi, hBiDom,
    hVphase, hLphase, hLVphase, hIt, hinterval, hIIt, hsegT, hseg,
    hDcar, hDreg, hDdom, hcontains, hsupport, hε, hfreq⟩ :=
    hbuffers hρ (hρcap.trans_le (min_le_right _ _)) hinput
  let Ki := closedBall p₀ ρ
  have hKiDom : Ki ⊆ symbolInputDomain zRoot ηb r (6 * a) := hinput
  obtain ⟨η, hη, hηBi⟩ := hBi.exists_forall_le'
    (continuous_snd.snd.norm.continuousOn : ContinuousOn (fun p : InputVariables n ↦ ‖p.2.2‖) Bi)
    (fun p hp ↦ norm_pos_iff.mpr (hBiDom hp).2.2.1)
  obtain ⟨radialUpper, hradialUpper, hradial⟩ :=
    (hBi.image (continuous_snd.snd : Continuous (fun p : InputVariables n ↦ p.2.2))).isBounded.exists_pos_norm_lt
  let gap := (cJ / ‖ηb‖) * η
  have hgap : 0 < gap := mul_pos (div_pos hcJ (norm_pos_iff.mpr hηb)) hη
  have hb : 0 < ‖k‖ := norm_pos_iff.mpr hk
  obtain ⟨hQc, hΩi, hQcΩi, hΩne, hΩrad⟩ := target_geometry hb hτ q₀
  have hsegD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      MapsTo (transportSegmentInput n t) W D.field.carrier := by
    rw [hDcar]
    exact hseg t ht
  have hend : ∀ side, MapsTo (WideDensity.densityEndpoint side) W D.field.carrier := by
    intro side p hp
    cases side
    · simpa only [WideDensity.densityEndpoint, Bool.false_eq_true, ↓reduceIte,
        transportSegmentInput_apply, one_smul, add_sub_cancel] using
        hsegD 1 ⟨by norm_num, le_rfl⟩ hp
    · simpa only [WideDensity.densityEndpoint, ↓reduceIte, transportSegmentInput_apply,
        zero_smul, add_zero] using hsegD 0 ⟨le_rfl, by norm_num⟩ hp
  refine ⟨r, hr, a, ha, hacap.trans_le (min_le_left _ _), houter,
    har, haR, hcell, hcarrier, ρ, hρ, hρcap.trans_le (min_le_left _ _), hinput,
    τ, hτ, r', hr', hrr, hrρ, a', ha', haa, har', haρ, by linarith,
    δ, hδ, cJ, hcJ, β, hβ, V, L, hV, hVc, hL, hLV,
    D, Ki, W, Bi, It, Vphase, Lphase, rfl,
    hVphase, hLphase, hLVphase, hDreg, hDcar, hinterval,
    isCompact_closedBall _ _, convex_closedBall _ _, ?_, hW, hKiW, hBi, hWBi,
    hBiDom, by simpa only [hDreg] using hDdom, hcontains,
    by simpa only [hDcar] using hsupport ha' haρ, hIt, hIIt,
    (fun t ht ↦ by rw [hDreg]; exact hsegT t ht), hsegD, hend,
    η, hη, hηBi, radialUpper, hradialUpper,
    (fun p hp ↦ hradial _ ⟨p, hp, rfl⟩),
    compactTarget ‖k‖ q₀ τ, conicTarget ‖k‖ q₀ τ,
    rfl, rfl, hQc, hΩi, hQcΩi, (fun _ hq ↦ hq.2), hΩne, hΩrad,
    gap, hgap, ?_⟩
  · exact mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ hρ)
  · intro F hF hi hrank hlow hsmall
    let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
      ⟨projectedStress F, contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    have hgeometry := hfamily F hF hi hrank hlow hsmall
    obtain ⟨hf, hsliceGap, hInv, htrans, houtput, hrange, hgapA, hpunct, hshell, hnorm,
      houtput0, hrange0, hgapA0, hshell0, hpunct0⟩ := hgeometry
    have harFrozen : 6 * a ≤ 3 * r := by linarith
    have htoFrozen := symbolInputDomain_subset_frozenInputDomain zRoot ηb r
      (by positivity : 0 < 6 * a)
    obtain ⟨Cupper, hCupper, hupper⟩ := exists_reference_differential_upper
      (FrozenIncidence.referenceEquiv T hP hzRoot hinc hd)
    have hJacLower : ∀ p ∈ symbolInputDomain zRoot ηb r (6 * a),
        (cJ / ‖ηb‖) * ‖p.2.2‖ ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
          (transportPosition T Q) p := by
      intro p hp
      have hl := (adaptedJacobian_bounds T Q hηb hr hf hInv htrans hsliceGap
        (fun D hD ↦ (hupper D hD).2) hp.1 hp.2).1
      rw [transportAbsoluteJacobian_eq_adaptedJacobian T Q p
        (adaptedTransportChart_differentiableAt_on_cone T Q hηb hr hf hp.1 hp.2)]
      exact hl
    have hmaskDom : conicMaskSupport zRoot ηb r' a' ⊆
        symbolInputDomain zRoot ηb r (6 * a) :=
      (conicMaskSupport_mono zRoot ηb hrr haa).trans
        (conicMaskSupport_subset hηb hr ha (by linarith))
    refine ⟨hfamily F hF hi hrank hlow hsmall, ⟨harFrozen, hcarrier,
      FrozenIncidence.referenceEquiv T hP hzRoot hinc hd,
      β, cJ, V, L, hcJ, hV, hLV, hf, hInv, htrans, hsliceGap⟩, ?_, ?_⟩
    · obtain ⟨hu, huRange, huNormRange, heq, hhom⟩ :=
        symbolInverse_on_common_target T Q hηb hr hInv htrans hLV hb hτ houtput hrange
      have hne : ∀ p ∈ conicMaskSupport zRoot ηb r' a',
          transportAveragedGradient (transportPosition T Q) p ≠ 0 :=
        fun p hp ↦ transportGradient_ne_zero T Q hηb hr htrans (hmaskDom hp)
      have hmaskTarget := mask_image_mem_compactTarget hb q₀ hne hshell
      refine ⟨conicTarget_subset_symbolDomain T Q hb houtput,
        hu, huRange, huNormRange, heq, hgapA, ?_,
        (transportAbsoluteJacobian_smooth T Q hηb hr hf hInv htrans hcJ).mono
          (hWBi.trans hBiDom),
        (symbolJacobian_eq_actual T Q hηb hr hf).mono (hWBi.trans hBiDom),
        ?_, symbolInverse_scale_all T Q hηb hr hInv htrans, ?_,
        mask_image_punctured_subset_conicTarget hb hτ q₀ hne hshell⟩
      · intro p hp
        exact (mul_le_mul_of_nonneg_left (hηBi p hp)
          (div_pos hcJ (norm_pos_iff.mpr hηb)).le).trans (hJacLower p (hBiDom hp))
      · intro p hp q hq hpq
        have hpLeft := symbolInverse_augmentedTransportGradient T Q hηb hr hInv htrans (hKiDom hp)
        have hqLeft := symbolInverse_augmentedTransportGradient T Q hηb hr hInv htrans (hKiDom hq)
        rw [hpq] at hpLeft
        exact hpLeft.symm.trans hqLeft
      · intro p hp
        have ht : 0 < ‖k‖ / ‖transportAveragedGradient (transportPosition T Q) p‖ :=
          div_pos hb (norm_pos_iff.mpr (hne p hp))
        have hpScaled : scaleInput (‖k‖ / ‖transportAveragedGradient (transportPosition T Q) p‖) p ∈
            symbolInputDomain zRoot ηb r (6 * a) :=
          hmaskDom (maskSupport_scaleInput ht hp)
        have hleftScaled := symbolInverse_augmentedTransportGradient T Q hηb hr hInv htrans hpScaled
        have hnormRange := huRange (hmaskTarget p hp)
        rw [augmentedTransportGradient_scaleInput] at hleftScaled
        refine ⟨ball_subset_closedBall
          (conicMaskSupport_radial_section_mem_ball hηb hr' ha' haρ hrρ hp),
          hne p hp, hmaskTarget p hp, ?_,
          symbolInverse_augmentedTransportGradient T Q hηb hr hInv htrans (hmaskDom hp)⟩
        exact hleftScaled ▸ hnormRange
    · have hsub0 : conicTarget ‖k‖ q₀ τ ⊆ frozenSymbolDomain T Q zRoot ηb r (6 * a) := by
        intro q hq
        exact (frozenSymbolDomain_smul_iff T Q zRoot ηb r (6 * a)
          (div_pos hb (norm_pos_iff.mpr hq.1)) q).mp
          (houtput0 (ball_subset_closedBall hq.2))
      have huRange0 : MapsTo (inverseCoordinates (frozenSymbolInverse T Q zRoot ηb r (6 * a)))
          (compactTarget ‖k‖ q₀ τ) Ki :=
        fun _ hq ↦ hrange0 ((closedBall_subset_closedBall (by linarith : τ ≤ 2 * τ)) hq.1)
      have hne0 : ∀ p ∈ conicMaskSupport zRoot ηb r' a',
          transportAveragedGradient (normalizedTransportPosition T Q 0) p ≠ 0 := by
        intro p hp
        rw [frozenForward_eq_origin T Q hP hr harFrozen hcarrier (htoFrozen (hmaskDom hp))]
        exact transportGradient_ne_zero T Q hηb hr htrans (htoFrozen (hmaskDom hp))
      have hmaskTarget0 := mask_image_mem_compactTarget hb q₀ hne0 hshell0
      refine ⟨hsub0, (frozenSymbolInverse_smooth T Q hηb hr hInv htrans hLV).mono hsub0,
        huRange0, (fun _ hq ↦ hrange0 (ball_subset_closedBall hq.2)),
        (fun _ hq ↦ frozenTransportGradient_inverse T Q hP hηb hr harFrozen hcarrier
          hInv htrans (hsub0 hq)), hgapA0, ?_,
        (frozenJacobian_smooth T Q hP hηb hr harFrozen hcarrier hInv htrans hf hcJ).mono
          ((hWBi.trans hBiDom).trans htoFrozen),
        (frozenKernelJacobian_eq_actual T Q hP hηb hr harFrozen hcarrier hf).mono
          ((hWBi.trans hBiDom).trans htoFrozen), ?_, ?_, ?_,
        mask_image_punctured_subset_conicTarget hb hτ q₀ hne0 hshell0⟩
      · intro p hp
        rw [frozenJacobian_eq_origin T Q hP hr harFrozen hcarrier _ (htoFrozen (hBiDom hp))]
        exact (mul_le_mul_of_nonneg_left (hηBi p hp)
          (div_pos hcJ (norm_pos_iff.mpr hηb)).le).trans
          (hJacLower (originInput p) (htoFrozen (hBiDom hp)))
      · intro p hp q hq hpq
        have hpLeft := frozenInverse_augmentedGradient T Q hP hηb hr harFrozen hcarrier
          hInv htrans (htoFrozen (hKiDom hp))
        have hqLeft := frozenInverse_augmentedGradient T Q hP hηb hr harFrozen hcarrier
          hInv htrans (htoFrozen (hKiDom hq))
        rw [hpq] at hpLeft
        exact hpLeft.symm.trans hqLeft
      · intro t ht q
        exact symbolInverse_scale_all T Q hηb hr hInv htrans t ht (originOutput q)
      · intro p hp
        have ht : 0 < ‖k‖ / ‖transportAveragedGradient (normalizedTransportPosition T Q 0) p‖ :=
          div_pos hb (norm_pos_iff.mpr (hne0 p hp))
        have hpScaled := htoFrozen (hmaskDom (maskSupport_scaleInput ht hp))
        have hleftScaled := frozenInverse_augmentedGradient T Q hP hηb hr harFrozen hcarrier
          hInv htrans hpScaled
        have hnormRange := huRange0 (hmaskTarget0 p hp)
        rw [augmentedTransportGradient_scaleInput] at hleftScaled
        refine ⟨ball_subset_closedBall
          (conicMaskSupport_radial_section_mem_ball hηb hr' ha' haρ hrρ hp),
          hne0 p hp, hmaskTarget0 p hp, ?_,
          frozenInverse_augmentedGradient T Q hP hηb hr harFrozen hcarrier
            hInv htrans (htoFrozen (hmaskDom hp))⟩
        exact hleftScaled ▸ hnormRange

end JanetCartan.ContinuumNormal.RetainedJointGeometry
