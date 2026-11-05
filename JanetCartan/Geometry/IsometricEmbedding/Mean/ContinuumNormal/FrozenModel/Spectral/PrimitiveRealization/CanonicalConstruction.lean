module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.SupportedConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.InverseEnlargement

/-!
# The supported realization with the canonical smaller inverse

The literal carrier constructed with the outer inverse is identified with the
canonical smaller-inverse amplitude by a proved function equality. Smoothness,
derivative bounds and the global reflected PDO normal are transported together.
Consumer: `canonicalFrozenCarrierExtension_adjoint_norm_sq_eq_energy_unit`
(`new:lem:scaling`, `app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol TransportKernel
open Pseudodifferential AmplitudeBound PeriodicLocalL2

private theorem frozenVectorAmplitudeOperator_congr {n : ℕ} (hn : 0 < n) (R B : ℝ)
    (b₁ b₂ : Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (he : b₁ = b₂)
    (hb₁ : ContDiff ℝ ∞ (Function.uncurry b₁))
    (hb₂ : ContDiff ℝ ∞ (Function.uncurry b₂))
    (hs₁ : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b₁ ξ z i j))
    (hs₂ : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b₂ ξ z i j))
    (hB₁ : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b₁ ξ z i j) (2 * (n + 1)) B)
    (hB₂ : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b₂ ξ z i j) (2 * (n + 1)) B) :
    vectorTwoPositionL2Operator hn R b₁ hb₁ hs₁ B hB₁ =
      vectorTwoPositionL2Operator hn R b₂ hb₂ hs₂ B hB₂ := by
  subst b₂
  rfl

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The actual uncut unit-initial carrier has the global normal of the SAME
canonical smaller masks, inverse and original Lebesgue spectator ball. Its
test action, uniqueness and literal adjoint are retained. Every operator and
analytic estimate is constructed; the retained outer local conic hypotheses
are precisely the outputs of `exists_frozen_conic_inputs`.
Source: `new:lem:scaling`, `app:ch_background:prop:bg-frame`. -/
theorem exists_canonicalFrozen_supported_carrier_unit
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hksmall : ‖k‖ ≤ 1 / 2)
    (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let hηb := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
    let G' := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
    ∃ (r' a' : ℝ) (hr' : 0 < r') (ha' : 0 < a') (hcell : 4 * a' < 1 / 2),
      r' ≤ r ∧ a' ≤ a ∧ 6 * a' ≤ r' ∧
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
      (∀ p ∈ physicalParameterSet z₀ (6 * a), ∀ u ∈ dataBox z₀ ηb (2 * r),
        ‖G.symm.toContinuousLinearMap.comp (fderiv ℝ (adaptedTransportChart T Q p) u) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) →
      IsOpen V → L ⊆ V → 0 < cJ →
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
        (physicalParameterSet z₀ (6 * a') ×ˢ dataSet z₀ ηb (3 * r')) ∧
      (∀ p ∈ physicalParameterSet z₀ (6 * a'), ∀ u ∈ dataBox z₀ ηb (2 * r'),
        ‖G'.symm.toContinuousLinearMap.comp (fderiv ℝ (adaptedTransportChart T Q p) u) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
      BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a'))
        (dataBox z₀ ηb r') (dataSet z₀ ηb (2 * r')) (dataBox z₀ ηb (2 * r')) V' L' b' cJ' G' ∧
      (∀ p ∈ physicalParameterSet z₀ (6 * a'),
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r' (angularWidth ηb r'),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r' / 4) * ‖u.2‖) ∧
      ∀ (F : Euclidean n → Euclidean N) (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (s : ℕ) (hs : 2 * (n + 1) ≤ s),
      let e := normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) ha' hcell
        (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency 0
      let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
      let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0)
      let u := frozenSymbolInverse T Q z₀ ηb r' (6 * a')
      let Ω := frozenSymbolDomain T Q z₀ ηb r' (6 * a')
      let S := closedBall (spectatorCenter z₀) (a' / 2)
      ∃ hn : 0 < n,
      ∃ hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a',
      ∃ B > (0 : ℝ),
      ∃ (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude d J u Ω S)))
        (hA : ∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ fullReflectedMatrixAmplitude d J u Ω S ξ z i j) s B),
      ∃ Vcarrier : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ v : carrierInitialTestSpace n,
          Vcarrier (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) ∧
        (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → Vcarrier f x = 0) ∧
        (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ v : carrierInitialTestSpace n,
            W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) → W = Vcarrier) ∧
        (∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
          Vcarrier.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
        (realQuadratureChannel Vcarrier).comp (realQuadratureChannel Vcarrier).adjoint =
          realOutputCompression (transferOperator
            (vectorTwoPositionL2Operator hn (4 * a') (fullReflectedMatrixAmplitude d J u Ω S) hb
              (fullReflectedMatrixAmplitude_supportedInCenteredBox d J u Ω S (4 * a') hsupport)
              B (fun i j ξ is his ↦ hA i j ξ is (his.trans hs)))) := by
  classical
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  obtain ⟨r', a', hr', ha', hcell, hrr, haa, har', cJ', hcJ', b', hb',
    V', L', hV', hVc', hLc', hLV', δ, hδ, hconstruct⟩ :=
    exists_frozen_supported_carrier_unit (N := N) T hP hz₀ hk hksmall hinc hd hr ha har hcarrier
  refine ⟨r', a', hr', ha', hcell, hrr, haa, har', cJ', hcJ', b', hb',
    V', L', hV', hVc', hLc', hLV', δ, hδ, ?_⟩
  intro Q hQ hf b cJ V L G hInv htrans hslice hV hLV hcJ
  obtain ⟨hf', hgap', hInv', htrans', hrealize⟩ :=
    hconstruct Q hQ hf hInv htrans hslice hV hLV hcJ
  refine ⟨hf', hgap', hInv', htrans', ?_⟩
  intro F row col Φ Y s hs
  have he := frozenMeasured_fullReflectedMatrixAmplitude_eq_of_enlargement
    T Q F row col Φ Y (fun _ ↦ 1) hηb hr hr' ha' hrr haa har
      (by linarith : 6 * a' ≤ 3 * r') hP hcarrier hInv htrans hInv' htrans' hcell
  have hreal := hrealize F row col Φ Y s hs
  obtain ⟨hn, hsupport, B, hB, hb, hA, Vcarrier, htest, hsupp, hunique, hadjoint, hnormal⟩ := hreal
  refine ⟨hn, hsupport, B, hB, ?_, ?_, Vcarrier, htest, hsupp, hunique, hadjoint, ?_⟩
  · rw [← he]
    exact hb
  · rw [← he]
    exact hA
  · apply hnormal.trans
    apply congrArg realOutputCompression
    apply congrArg transferOperator
    exact frozenVectorAmplitudeOperator_congr hn (4 * a') B _ _ he _ _ _ _ _ _

end JanetCartan.ContinuumNormal.FrozenModel
