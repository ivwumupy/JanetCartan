module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.CanonicalSourceControl
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Restriction

/-!
# One source cap for the retained canonical normal family

Apply the actual canonical-inverse source estimate cell by cell, then choose
one finite minimum before varying source scale or any permitted density. The
local physical radii and every detector mask remain the supplied ones. The
result gives the quarter-gap budget for the sum of the reflected PDOs and
for the same sum after a common measurement restriction.
-/

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic NormalizedSelection FrozenModel RetainedFrozen
open ContinuumNormalReduction.TransportSymbol ContinuumRow.CarrierNormalRealization
open CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.RetainedRowGeometry
open CarrierVariation.FamilyInputs.PositiveReference CarrierVariation.FamilyInputs.WideDensity
open PositiveReference.FlowConstruction
open NullTransport ActualFlow FlowAmplitude NormalizedBackground.SourceGeometry
open Pseudodifferential AmplitudeBound PeriodicLocalL2

/-- The finite carrier quarter-gap follows from frozen geometry of ONE
admitted positive source on the SAME supplied family. Source matching transfers
that geometry to the original seed at zero; neither an additional seed
threshold nor a different reference or mask is chosen. In the selected family
one may take `Qanchor i = Qcurrent i anchor` at any admitted positive `anchor`.

All absolute budgets precede the gap, and the common source cap precedes sigma
and the original permitted densities. The full reflected amplitudes, physical
PDOs and common measurement restriction have the same quarter-gap conclusion
as `exists_retained_canonical_source_family_quarter_gap`. Consumer: actual
normalized normal coercivity and SourceInverse
(`app:ch_background:prop:bg-normalized`, `bg-Psi`, `bg-full-complex-amplitude`,
`bg-uniform-normalized`). -/
theorem exists_retained_canonical_source_family_quarter_gap_of_frozen_source
    {n N : ℕ} {ι : Type} [Fintype ι] (hn : 0 < n)
    {P : ι → Patch n} {c C : ℝ} (hP : ∀ i, (P i).IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
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
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hphysical : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ U)
    (seed : (i : ι) → Chart (T i) (Ωflow i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
      ((0 : Euclidean (n - 1)), zCell i) (Rc i) (Bflow i) (τflow i) (row i) (col i) F)
    (htrans : ∀ i q, q ∈ closedBall (0, (T i).data.center) (T i).data.localReference.stateRadius →
      ⟪(normalizedHomogeneousSymbol hU (seed i).Q.1 (seed i).Q.2.1).hp q,
        (T i).data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
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
    (Qcurrent : (i : ι) → ℝ → {Q : Euclidean n → Fin n → MetricTensor n //
      ContDiffOn ℝ ∞ Q U ∧ cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T i).family.threshold})
    (hframe : ∀ i σ, σ ∈ Ioc (0 : ℝ) sourceCap →
      (Qcurrent i σ).1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
    (Qanchor : (i : ι) → {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T i).family.threshold})
    {anchor : ℝ} (hanchor : 0 < anchor) (hanchor1 : anchor ≤ 1)
    (hanchorFrame : ∀ i, (Qanchor i).1 = ProjectedStressFrame.projectedStress (sourceDilation F anchor))
    (hfrozen : ∀ i,
      RetainedSpectralGeometry (T i) (Qanchor i) (zRoot i) (ηb i) (r i) (a i) ∧
      Ω i ⊆ frozenSymbolDomain (T i) (Qanchor i) (zRoot i) (ηb i) (r i) (6 * a i) ∧
      MapsTo (inverseCoordinates (frozenSymbolInverse (T i) (Qanchor i) (zRoot i) (ηb i) (r i) (6 * a i)))
        (Q i) (K i) ∧
      MapsTo (fun q ↦ inverseCoordinates
        (frozenSymbolInverse (T i) (Qanchor i) (zRoot i) (ηb i) (r i) (6 * a i))
        (normalizeOutputRadius (1 / 4) q)) (Ω i) (K i) ∧
      (∀ p ∈ K i, ‖(A i).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition (T i) (Qanchor i) 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K i, jacobianGap i ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
        (normalizedTransportPosition (T i) (Qanchor i) 0) p) ∧
      (∀ p ∈ conicMaskSupport (zRoot i) (ηb i) (r' i) (a' i), normalizeOutputRadius (1 / 4)
        (augmentedTransportGradient (normalizedTransportPosition (T i) (Qanchor i) 0) p) ∈ Q i))
    (hcurrent : ∀ i σ, σ ∈ Ioc (0 : ℝ) sourceCap →
      RetainedSpectralGeometry (T i) (Qcurrent i σ) (zRoot i) (ηb i) (r i) (a i) ∧
      Ω i ⊆ symbolDomain (T i) (Qcurrent i σ) (zRoot i) (ηb i) (r i) (6 * a i) ∧
      MapsTo (inverseCoordinates (symbolInverse (T i) (Qcurrent i σ) (zRoot i) (ηb i) (r i) (6 * a i)))
        (Q i) (K i) ∧
      MapsTo (fun q ↦ inverseCoordinates (symbolInverse (T i) (Qcurrent i σ) (zRoot i) (ηb i) (r i) (6 * a i))
        (normalizeOutputRadius (1 / 4) q)) (Ω i) (K i) ∧
      (∀ p ∈ K i, ‖(A i).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition (T i) (Qcurrent i σ))) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K i, jacobianGap i ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
        (transportPosition (T i) (Qcurrent i σ)) p) ∧
      (∀ p ∈ conicMaskSupport (zRoot i) (ηb i) (r' i) (a' i), normalizeOutputRadius (1 / 4)
        (augmentedTransportGradient (transportPosition (T i) (Qcurrent i σ)) p) ∈ Q i)) :
    let μ := 2 * (n + 1)
    let angular := fun i ↦ angularMask (zRoot i) (NormedSpace.normalize (ηb i)) (ha' i)
      (angularWidth_spec (hηb i) (hr' i)).1
    let d := fun i σ ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData (T i) (seed i).Q F (row i) (col i) (seed i).forward (seed i).inverse (fun _ ↦ 1)
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
  intro μ angular d J u S b
  have hlocal := fun i ↦ exists_retained_canonical_source_reflectedPdo_control_of_frozen_source
    (hP i) (T i) (hΩflow i) (hKΩ i) (hΩpatch i) (hRc i) (hτ i) (hτR i) (hbuffer i)
    hF hi hrank (hphysical i) (seed i) (htrans i) hflat (hL i) (hMc i) (hR i) (hforward i)
    (hRT i) (hRU i) (hRtime i) (hV i) (hVP i) (hflow i) (hlabel i) (D i) (hD i)
    (hηb i) (hr i) (hr' i) (ha' i) (hrr i) (haa i) (har' i) (hcell i) (houter i)
    (hK i) (hconv i) (hW i) (hKW i) (hWinput i) (hQ i) (hΩ i) (hQΩ i)
    (hne i) (hcone i) (hcontains i) (hIt i) (hIIt i) (hseg i) (hend i)
    (hη i) (hjacobianGap i) hsourceCap hcap1 (hfreq i) (A i) (Qcurrent i)
    (hframe i) (Qanchor i) hanchor hanchor1 (hanchorFrame i) (hfrozen i) (hcurrent i)
  choose B hBpos hcontrols using hlocal
  refine ⟨B, hBpos, ?_⟩
  intro gap hgap tol
  have htol : 0 < tol := div_pos hgap (by positivity)
  have hbudget : (Fintype.card ι : ℝ) * tol ≤ gap / 4 := by
    have hcancel : (4 * ((Fintype.card ι : ℝ) + 1)) * tol = gap :=
      mul_div_cancel₀ gap (by positivity)
    nlinarith
  choose caps hcaps hcapsSource hcapsOne hcontrols using fun i ↦ hcontrols i tol htol
  obtain ⟨cap₀, hcap₀, hcap₀s⟩ := (finite_range caps).isCompact.exists_forall_le' continuousOn_id
    (by rintro x ⟨i, rfl⟩; exact hcaps i)
  refine ⟨min cap₀ sourceCap, lt_min hcap₀ hsourceCap,
    min_le_right _ _, (min_le_right _ _).trans hcap1, ?_⟩
  intro σ hσ v hv hvm hpos pair
  have hdata := fun i ↦ hcontrols i σ
    ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans (hcap₀s _ ⟨i, rfl⟩))⟩
    (v i) (hv i) (hvm i) (hpos i)
  have hamp := fun i ↦ (hdata i).1
  choose hb hs hB hnorms using fun i ↦ (hdata i).2
  refine ⟨hamp, (fun t i ↦ hb i t), (fun t i ↦ hs i t), (fun t i ↦ hB i t), ?_⟩
  intro Aop Nop
  have hsum : (∑ i, ‖Nop 0 i - Nop 1 i‖) ≤ gap / 4 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ (hnorms i).2.2
    have hsum' : (∑ i, ‖Nop 0 i - Nop 1 i‖) ≤ (Fintype.card ι : ℝ) * tol := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hh
    exact hsum'.trans hbudget
  refine ⟨hnorms, hsum, ?_⟩
  intro χ hχ
  have hm : ‖cutoffMultiplier χ‖ ≤ 1 := (cutoffMultiplier_norm_le χ).trans hχ
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun i _ ↦ ?_)).trans hsum
  rw [← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp,
    ← ContinuousLinearMap.comp_assoc]
  calc
    _ ≤ ‖cutoffMultiplier χ‖ * ‖Nop 0 i - Nop 1 i‖ * ‖cutoffMultiplier χ‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖Nop 0 i - Nop 1 i‖ * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hm (norm_nonneg _)) hm (norm_nonneg _) (by positivity)
    _ = ‖Nop 0 i - Nop 1 i‖ := by ring


/-- The SAME supplied finite family of canonical current/frozen inverses gives
one positive source cap and the carrier quarter of the existing half-gap
comparison. Each local absolute budget precedes the gap, scale and every density in
the original `L/8`, `μ+14` class. The local measurement radii can differ;
all original angular masks and spectator measures remain fixed. A common
measurement restriction of norm at most one retains this quarter-gap without
changing the amplitudes or imposing another derivative bound on the cutoff.
The PDOs are the literal normalized reflected amplitudes, whose current
carrier identities are proved by
`retained_source_normal_eq_normalized_on_common_cone`; the zero carrier is
constructed by `SourceDensityLimitRealization` on these same inputs.

The conic projections and original chart buffers are supplied by normalized
selection and normal variation. This theorem derives the analytic estimates
from them and leaves their actual finite-family assembly to those producers.
Consumer: the carrier sum in actual normal coercivity, then SourceInverse
(`app:ch_background:prop:bg-normalized`, `bg-full-complex-amplitude`,
`bg-real-symbol`, `bg-uniform-normalized`). -/
theorem exists_retained_canonical_source_family_quarter_gap
    {n N : ℕ} {ι : Type} [Fintype ι] (hn : 0 < n)
    {P : ι → Patch n} {c C : ℝ} (hP : ∀ i, (P i).IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
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
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hphysical : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ U)
    (seed : (i : ι) → Chart (T i) (Ωflow i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
      ((0 : Euclidean (n - 1)), zCell i) (Rc i) (Bflow i) (τflow i) (row i) (col i) F)
    (htrans : ∀ i q, q ∈ closedBall (0, (T i).data.center) (T i).data.localReference.stateRadius →
      ⟪(normalizedHomogeneousSymbol hU (seed i).Q.1 (seed i).Q.2.1).hp q,
        (T i).data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
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
    (Qcurrent : (i : ι) → ℝ → {Q : Euclidean n → Fin n → MetricTensor n //
      ContDiffOn ℝ ∞ Q U ∧ cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T i).family.threshold})
    (hframe : ∀ i σ, σ ∈ Ioc (0 : ℝ) sourceCap →
      (Qcurrent i σ).1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
    (hfrozen : ∀ i,
      RetainedSpectralGeometry (T i) (seed i).Q (zRoot i) (ηb i) (r i) (a i) ∧
      Ω i ⊆ frozenSymbolDomain (T i) (seed i).Q (zRoot i) (ηb i) (r i) (6 * a i) ∧
      MapsTo (inverseCoordinates (frozenSymbolInverse (T i) (seed i).Q (zRoot i) (ηb i) (r i) (6 * a i)))
        (Q i) (K i) ∧
      MapsTo (fun q ↦ inverseCoordinates
        (frozenSymbolInverse (T i) (seed i).Q (zRoot i) (ηb i) (r i) (6 * a i))
        (normalizeOutputRadius (1 / 4) q)) (Ω i) (K i) ∧
      (∀ p ∈ K i, ‖(A i).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition (T i) (seed i).Q 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K i, jacobianGap i ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
        (normalizedTransportPosition (T i) (seed i).Q 0) p) ∧
      (∀ p ∈ conicMaskSupport (zRoot i) (ηb i) (r' i) (a' i), normalizeOutputRadius (1 / 4)
        (augmentedTransportGradient (normalizedTransportPosition (T i) (seed i).Q 0) p) ∈ Q i))
    (hcurrent : ∀ i σ, σ ∈ Ioc (0 : ℝ) sourceCap →
      RetainedSpectralGeometry (T i) (Qcurrent i σ) (zRoot i) (ηb i) (r i) (a i) ∧
      Ω i ⊆ symbolDomain (T i) (Qcurrent i σ) (zRoot i) (ηb i) (r i) (6 * a i) ∧
      MapsTo (inverseCoordinates (symbolInverse (T i) (Qcurrent i σ) (zRoot i) (ηb i) (r i) (6 * a i)))
        (Q i) (K i) ∧
      MapsTo (fun q ↦ inverseCoordinates (symbolInverse (T i) (Qcurrent i σ) (zRoot i) (ηb i) (r i) (6 * a i))
        (normalizeOutputRadius (1 / 4) q)) (Ω i) (K i) ∧
      (∀ p ∈ K i, ‖(A i).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition (T i) (Qcurrent i σ))) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K i, jacobianGap i ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
        (transportPosition (T i) (Qcurrent i σ)) p) ∧
      (∀ p ∈ conicMaskSupport (zRoot i) (ηb i) (r' i) (a' i), normalizeOutputRadius (1 / 4)
        (augmentedTransportGradient (transportPosition (T i) (Qcurrent i σ)) p) ∈ Q i)) :
    let μ := 2 * (n + 1)
    let angular := fun i ↦ angularMask (zRoot i) (NormedSpace.normalize (ηb i)) (ha' i)
      (angularWidth_spec (hηb i) (hr' i)).1
    let d := fun i σ ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData (T i) (seed i).Q F (row i) (col i) (seed i).forward (seed i).inverse (fun _ ↦ 1)
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
  have hunit : sourceDilation F 1 = F := by
    funext x
    simp only [sourceDilation, inv_one, one_smul]
  have hanchorFrame : ∀ i, (seed i).Q.1 = ProjectedStressFrame.projectedStress (sourceDilation F 1) :=
    fun i ↦ hunit.symm ▸ (seed i).frame_eq
  exact exists_retained_canonical_source_family_quarter_gap_of_frozen_source hn hP T
    hΩflow hKΩ hΩpatch hRc hτ hτR hbuffer hF hi hrank hphysical seed htrans hflat
    hL hMc hR hforward hRT hRU hRtime hV hVP hflow hlabel D hD hηb hr hr' ha'
    hrr haa har' hcell houter hK hconv hW hKW hWinput hQ hΩ hQΩ hne hcone hcontains
    hIt hIIt hseg hend hη hjacobianGap hsourceCap hcap1 hfreq A Qcurrent hframe
    (fun i ↦ (seed i).Q) zero_lt_one le_rfl hanchorFrame hfrozen hcurrent

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
