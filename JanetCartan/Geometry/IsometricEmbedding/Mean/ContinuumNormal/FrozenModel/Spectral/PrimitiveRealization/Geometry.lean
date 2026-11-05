module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Buffers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Geometry.Balls
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Geometry.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Geometry.Refinement
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Geometry.SupportedInputs

/-!
# Actual primitive geometry for the frozen supported carrier

`exists_frozen_primitive_buffers` constructs the common balls and instantiates
the coefficient-buffer producer on that actual input ball.
It also applies `exists_frozen_supported_refinement` to construct the smaller
masks and their own canonical inverse, with all radius inequalities and the
supported shell, discharging its differential premise on the same ball. `exists_frozen_primitive_jacobian_lower_bound` supplies the uniform
positive determinant bound on the same ball; `exists_frozen_geometry_norms`
supplies the finite geometric budgets on the same phase buffer.

The only local analytic inputs retained by these constructions are the outer
smoothness, buffered inverse and transverse comparison produced by
`exists_frozen_conic_inputs`. The displayed primitive frame thresholds must be
met by the parent's fixed seed. The parent applies the supported carrier
constructor and the kernel adapter; no operator conclusion is assumed here.
Sources: `new:lem:scaling`, `app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol TransportKernel

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Construct the frozen common balls and all finite coefficient/segment
buffers together. In particular the input-ball premise of
`exists_frozenMeasured_coefficient_buffers` is discharged by the actual
common-ball construction. The coefficient budgets are proved for every fixed
seed and every subsequent smaller mask; they are not assumed.

The same construction chooses the smaller canonical inverse and original
masks and proves their supported shell and punctured image buffer. Its
original half-gap discharges the refinement's differential premise internally.
Consumer: `exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`
(`new:lem:scaling`, `app:ch_background:eq:bg-mixed-input`). -/
theorem exists_frozen_primitive_buffers {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
    let q₀ := frozenAugmentedChart T p₀
    ∃ ρ > (0 : ℝ), closedBall p₀ ρ ⊆ symbolInputDomain z₀ ηb r (6 * a) ∧
    ∃ τ > (0 : ℝ), 2 * τ ≤ ρ ∧ closedBall q₀ τ ⊆ ball q₀ (2 * τ) ∧
    ∃ (W K : Set (InputVariables n))
      (Vphase Lphase : Set (Euclidean n × CarrierParameter))
      (I : Set ℝ) (D : CoefficientNormCharts n) (ε : ℝ),
      IsOpen W ∧ IsCompact K ∧ closedBall p₀ ρ ⊆ W ∧ W ⊆ K ∧
      K ⊆ symbolInputDomain z₀ ηb r (6 * a) ∧
      IsOpen Vphase ∧ IsCompact Lphase ∧ Lphase ⊆ Vphase ∧
      IsOpen I ∧ (∃ l u : ℝ, I = Ioo l u) ∧ Icc (0 : ℝ) 1 ⊆ I ∧
      (∀ t ∈ I, MapsTo (transportSegmentInput n t) W Vphase) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W Lphase) ∧
      D.field.carrier = Lphase ∧ D.field.region = Vphase ∧
      Vphase ⊆ coefficientDomain z₀ r (6 * a) ∧
      MapsTo (fun p : Euclidean n × CarrierParameter ↦ p.2) D.field.region
        (parameter ⁻¹' parameterInterior (2 * P.radius)) ∧
      (∀ p ∈ closedBall p₀ ρ, D.Contains p) ∧
      (∀ {a' : ℝ} (ha' : 0 < a'), 4 * a' < ρ →
        tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
          carrierSupport z₀ (r := a') ⊆ D.field.carrier) ∧
      0 < ε ∧ (∀ p ∈ closedBall p₀ ρ, ε ≤ ‖p.2.2‖) ∧
      (∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        {N : ℕ} (F : Euclidean n → Euclidean N) (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        {r' a' : ℝ} (hr' : 0 < r') (ha' : 0 < a') (hcell : 4 * a' < 1 / 2),
        ∃ M ≥ 0, ∃ B : ℕ → ℝ, (∀ s, 1 ≤ B s) ∧ ∀ s H, 1 ≤ H →
          D.Controls s M (B s) H
            (coefficientsOfCarrier
              (normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) ha' hcell
                (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec
                  (FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc) hr').1)
                FixedCutoffs.highFrequency 0) (FixedCutoffs.physical ha' 1))) ∧
    ∃ r' > (0 : ℝ), r' ≤ r ∧ r' ≤ ρ ∧
    ∃ a' > (0 : ℝ), a' ≤ a ∧ 6 * a' ≤ r' ∧ 4 * a' < ρ ∧
      4 * a' < τ ∧ 4 * a' < 1 / 2 ∧
      (closedBall (spectatorCenter z₀) (3 * r') ×ˢ closedBall (z₀ 0) (3 * r') ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ cJ' > (0 : ℝ), ∃ b' > (0 : ℝ), ∃ V' L' : Set (ℝ × Euclidean (n - 1)),
      IsOpen V' ∧ IsCompact (closure V') ∧ IsCompact L' ∧ L' ⊆ V' ∧
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
        (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) →
      ∀ {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
        {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))},
      BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
        (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G →
      (∀ p ∈ physicalParameterSet z₀ (6 * a),
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) →
      ball q₀ (2 * τ) ⊆ frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
      MapsTo (inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r (6 * a)))
        (closedBall q₀ τ) (closedBall p₀ ρ) ∧
      (∀ p ∈ closedBall p₀ ρ,
        ‖(augmentedReferenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ closedBall p₀ ρ,
        ‖(augmentedReferenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
        (physicalParameterSet z₀ (6 * a') ×ˢ dataSet z₀ ηb (3 * r')) ∧
      (∀ p ∈ physicalParameterSet z₀ (6 * a'), ∀ u ∈ dataBox z₀ ηb (2 * r'),
        ‖(FrozenIncidence.referenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
          (fderiv ℝ (adaptedTransportChart T Q p) u) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
      BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a'))
        (dataBox z₀ ηb r') (dataSet z₀ ηb (2 * r')) (dataBox z₀ ηb (2 * r')) V' L' b' cJ'
          (FrozenIncidence.referenceEquiv T hP hz₀ hinc hd) ∧
      (∀ p ∈ physicalParameterSet z₀ (6 * a'),
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r' (angularWidth ηb r'),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r' / 4) * ‖u.2‖) ∧
      (∀ x : Variables n, ‖x.2.2‖ = ‖k‖ → ∀ v : Euclidean 2,
        (x, v) ∈ closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
          conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
      (closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
        conicMaskSupport z₀ ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
          frozenSymbolDomain T Q z₀ ηb r (6 * a)) := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  obtain ⟨cap, hcap, hbuffers⟩ := exists_frozenMeasured_coefficient_buffers T hP z₀ hz₀ ηb hηb
  obtain ⟨ρ, hρ, hρcap, hinput, τ, hτ, htρ, δ, hδ, hballs⟩ :=
    exists_frozen_primitive_balls T hP hz₀ hk hinc hd hr ha hcap har hcarrier
  obtain ⟨W, K, Vphase, Lphase, I, D, ε, hW, hK, hball, hWK, hKdom,
    hV, hL, hLV, hI, hinterval, hIT, hsegT, hseg, hDcar, hDreg, hDom, hfield,
    hfoot, hsupport, hε, hη, hcontrols⟩ := hbuffers hρ hρcap hinput
  obtain ⟨r', hr', hrr, hrρ, a', ha', haa, har', haρ, haτ, hcell, hcarrier',
    δ₁, hδ₁, cJ', hcJ', b', hb', V', L', hV', hVc', hLc', hLV', hrefine⟩ :=
    exists_frozen_supported_refinement T hP hz₀ hk hinc hd hr ha hρ hτ
  refine ⟨ρ, hρ, hinput, τ, hτ, htρ, closedBall_subset_ball (by linarith),
    W, K, Vphase, Lphase, I, D, ε, hW, hK, hball, hWK, hKdom,
    hV, hL, hLV, hI, hinterval, hIT, hsegT, hseg, hDcar, hDreg, hDom, hfield,
    hfoot, hsupport, hε, hη, hcontrols, r', hr', hrr, hrρ, a', ha', haa, har', haρ, haτ,
    hcell, hcarrier', cJ', hcJ', b', hb', V', L', hV', hVc', hLc', hLV',
    min δ δ₁, lt_min hδ hδ₁, ?_⟩
  intro Q hQ hf b cJ V L G hInv htrans
  obtain ⟨houtput, hrange, hgap, horiginal⟩ :=
    hballs Q (hQ.trans_le (min_le_left _ _)) hf hInv htrans
  obtain ⟨hf', hgap', hInv', htrans', hshell⟩ :=
    hrefine Q (hQ.trans_le (min_le_right _ _)) horiginal
  exact ⟨ball_subset_closedBall.trans houtput,
    hrange.mono_left (closedBall_subset_closedBall (by linarith)), hgap, horiginal,
    hf', hgap', hInv', htrans', hshell,
    frozenRefinedMaskImage_punctured_buffer T Q hP hηb hr ha har hcarrier hf htrans hrr haa⟩

end JanetCartan.ContinuumNormal.FrozenModel
