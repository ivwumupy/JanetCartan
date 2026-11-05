module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Geometry.Bounds

/-!
# Smaller original masks on the outer frozen input region

The actual normal and detector retain the outer carrier buffer; only the
original smooth masks shrink. This supplies primitive regularity and punctured
support containment for the same inverse used by the supported constructor.
Sources: `new:lem:scaling`, `app:ch_background:eq:bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol TransportKernel

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))
    {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hP hηb hr ha har hcarrier hf hInv htrans in
/-- The smaller measured unit-initial coefficients are primitive-regular on
the outer frozen region, not merely on their smaller inverse domain. Every
analytic field is proved for the original seed coefficients. Consumer: the
supported constructor with retained outer inverse (`bg-full-complex-amplitude`). -/
theorem frozenMeasured_refined_primitiveRegularity
    (hcJ : 0 < cJ) (hr' : 0 < r') (ha' : 0 < a') (hcell : 4 * a' < 1 / 2)
    {N : ℕ} (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3) :
    PrimitiveRegularity
      (coefficientsOfCarrier
        (normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) ha' hcell
          (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
          FixedCutoffs.highFrequency 0) (FixedCutoffs.physical ha' 1))
      (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0))
      (frozenInputDomain z₀ ηb r (6 * a)) := by
  rw [coefficientsOfCarrier_normalizedCarrierData_zero]
  have hreg := frozenPrimitiveRegularity_unit T Q hP hηb hr ha har hcarrier hf hInv htrans hcJ
    F row col Φ Y
  exact { hreg with
    leftMeasurement := (FixedCutoffs.physical ha' 1).contDiff.comp_contDiffOn contDiffOn_fst.fst
    rightMeasurement := (FixedCutoffs.physical ha' 1).contDiff.comp_contDiffOn contDiffOn_fst.snd
    angular := angularMask_smooth z₀ (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 }

include hP hηb hr ha har hcarrier hf htrans in
/-- The smaller frozen support has a punctured image buffer inside the
retained outer inverse domain. Its producer is the original support buffer
and the explicit radius inequalities in `exists_frozen_supported_refinement`
(`new:lem:scaling`, `app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenRefinedMaskImage_punctured_buffer (hrr : r' ≤ r) (haa : a' ≤ a) :
    closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
      conicMaskSupport z₀ ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
      frozenSymbolDomain T Q z₀ ηb r (6 * a) := by
  intro p hp
  exact frozenConicMaskImage_punctured_buffer T Q hP hηb hr ha har hcarrier hf htrans
    ⟨closure_mono (image_mono (conicMaskSupport_mono z₀ ηb hrr haa)) hp.1, hp.2⟩

end JanetCartan.ContinuumNormal.FrozenModel
