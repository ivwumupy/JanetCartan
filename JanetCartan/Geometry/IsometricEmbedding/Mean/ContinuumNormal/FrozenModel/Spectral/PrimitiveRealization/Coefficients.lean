module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity.Primitive
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Masks

/-!
# Primitive norms of the measured frozen carrier

These are coefficient inputs to
`exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`, for the
literal `normalizedCarrierData` at scale zero. The seed normal and detector
are the existing Hamilton coefficients. Their smoothness is proved, and
the constants are their finite norms on the supplied compact charts.
The constants may depend on the fixed seed `T`, `Q`, and `F`; this is not a
uniform estimate for varying immersions.

Sources: `new:lem:scaling`, `app:ch_background:eq:bg-full-complex-amplitude`,
and `app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol TransportKernel

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (hcell : 4 * a < 1 / 2)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) ha
  (And.left (angularWidth_spec hηb hr))
local notation "e₀" => normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1)
  ha hcell angular₀ FixedCutoffs.highFrequency 0
local notation "d₀" => coefficientsOfCarrier e₀ (FixedCutoffs.physical ha 1)

private theorem enlargePrimitiveControls
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {D : PrimitiveNormChart E} {s : ℕ} {M B H M' B' : ℝ} {f : E → G}
    (h : D.Controls s M B H f) (hM : M ≤ M') (hB : B ≤ B') (hH : 0 ≤ H) :
    D.Controls s M' B' H f :=
  ⟨h.smooth, h.low.trans hM, h.high.trans (mul_le_mul_of_nonneg_right hB hH)⟩

/-- Actual all-order finite coefficient budgets for the frozen unit-initial
carrier. The single low constant precedes the derivative order, and no bound
on the normal or detector is assumed. The field chart condition is geometric;
`exists_coefficient_buffers_cap` supplies it when its open region is the
preimage of `parameterInterior (2 * P.radius)`.
Consumer: the coefficient-controls field of the supported carrier realization
(`new:lem:scaling`, `app:ch_background:eq:bg-mixed-input`). -/
theorem exists_frozenMeasured_primitive_controls_unit
    {c C : ℝ} (hP : P.IsValid c C) (D : CoefficientNormCharts n)
    (hfield : MapsTo (fun p : Euclidean n × CarrierParameter ↦ p.2)
      D.field.region (parameter ⁻¹' parameterInterior (2 * P.radius))) :
    ∃ M ≥ 0, ∃ B : ℕ → ℝ, (∀ s, 1 ≤ B s) ∧
      ∀ s H, 1 ≤ H → D.Controls s M (B s) H d₀ := by
  obtain ⟨Mmask, hMmask, Bmask, hBmask, hmasks⟩ := exists_fixedMask_controls D ha angular₀
    (angularMask_smooth z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1).contDiffOn
  let ν : Euclidean n × CarrierParameter → Euclidean N :=
    fun p ↦ normalField T Q F row col Φ Y (fun _ ↦ 1) 0 p.2
  let q : Euclidean n × CarrierParameter → Fin n → ℝ :=
    fun p ↦ quadratic (Q.1 0) (T.carrierGradient Q 0 (parameter p.2))
  have hν : ContDiffOn ℝ ∞ ν D.field.region :=
    (frozenSeedNormal_unit_smooth T Q F row col Φ Y hP).comp contDiffOn_snd hfield
  have hq : ContDiffOn ℝ ∞ q D.field.region :=
    (PiLp.contDiff_ofLp.comp_contDiffOn (frozenSeedDetector_smooth T Q hP)).comp
      contDiffOn_snd hfield
  let M := Mmask + cNorm D.field.carrier 1 ν + cNorm D.field.carrier 1 q
  let B := fun s ↦ Bmask s + cNorm D.field.carrier s ν + cNorm D.field.carrier s q
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg (add_nonneg hMmask (cNorm_nonneg ..)) (cNorm_nonneg ..)
  have hB (s) : 1 ≤ B s := by
    dsimp [B]
    linarith [hBmask s, cNorm_nonneg D.field.carrier s ν, cNorm_nonneg D.field.carrier s q]
  refine ⟨M, hM, B, hB, ?_⟩
  intro s H hH
  rw [coefficientsOfCarrier_normalizedCarrierData_zero]
  obtain ⟨hm, ha', hh⟩ := hmasks s H hH
  have hMle : Mmask ≤ M := by
    dsimp [M]
    linarith [cNorm_nonneg D.field.carrier 1 ν, cNorm_nonneg D.field.carrier 1 q]
  have hBle : Bmask s ≤ B s := by
    dsimp [B]
    linarith [cNorm_nonneg D.field.carrier s ν, cNorm_nonneg D.field.carrier s q]
  have hBH : B s ≤ B s * H := le_mul_of_one_le_right (zero_le_one.trans (hB s)) hH
  refine ⟨enlargePrimitiveControls hm hMle hBle (zero_le_one.trans hH),
    enlargePrimitiveControls ha' hMle hBle (zero_le_one.trans hH),
    enlargePrimitiveControls hh hMle hBle (zero_le_one.trans hH),
    ⟨hν, ?_, ?_⟩, ⟨hq, ?_, ?_⟩⟩
  · change cNorm D.field.carrier 1 ν ≤ M
    dsimp [M]
    linarith [cNorm_nonneg D.field.carrier 1 q]
  · change 1 + cNorm D.field.carrier s ν ≤ B s * H
    apply le_trans _ hBH
    dsimp [B]
    linarith [hBmask s, cNorm_nonneg D.field.carrier s q]
  · change cNorm D.field.carrier 1 q ≤ M
    dsimp [M]
    linarith [cNorm_nonneg D.field.carrier 1 ν]
  · change 1 + cNorm D.field.carrier s q ≤ B s * H
    apply le_trans _ hBH
    dsimp [B]
    linarith [hBmask s, cNorm_nonneg D.field.carrier s ν]

variable {c C : ℝ} (hP : P.IsValid c C) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hcJ : 0 < cJ)

local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)

include hP har hcarrier hf hInv htrans hcJ in
/-- Primitive regularity for the measured carrier, with its literal frozen
Jacobian and input cone. All coefficient fields are proved from the seed,
and the geometric hypotheses are outputs of `exists_frozen_conic_inputs`.
Consumer: the supported carrier realization (`bg-full-complex-amplitude`). -/
theorem frozenMeasured_primitiveRegularity_unit :
    PrimitiveRegularity d₀ J₀ (frozenInputDomain z₀ ηb r (6 * a)) := by
  rw [coefficientsOfCarrier_normalizedCarrierData_zero]
  exact { frozenPrimitiveRegularity_unit T Q hP hηb hr ha har hcarrier hf hInv htrans hcJ
      F row col Φ Y with
    leftMeasurement := (FixedCutoffs.physical ha 1).contDiff.comp_contDiffOn contDiffOn_fst.fst
    rightMeasurement := (FixedCutoffs.physical ha 1).contDiff.comp_contDiffOn contDiffOn_fst.snd }

include hP har hcarrier hf hInv htrans hcJ in
/-- Every literal radial regularization has the same frozen Jacobian and
coefficient regularity. The regularization does not change the measurement,
normal or detector (`app:ch_background:eq:bg-full-complex-amplitude`).
Consumer: `TransportKernel.SymbolInputs.regularity`. -/
theorem frozenMeasured_regularized_primitiveRegularity_unit (R : ℝ) :
    PrimitiveRegularity (regularizedCoefficients d₀ FixedCutoffs.radialRegularization R)
      J₀ (frozenInputDomain z₀ ηb r (6 * a)) :=
  (frozenMeasured_primitiveRegularity_unit T Q F row col Φ Y hηb hr ha hcell
    hP har hcarrier hf hInv htrans hcJ).regularized FixedCutoffs.radialRegularization_smooth R

end JanetCartan.ContinuumNormal.FrozenModel
