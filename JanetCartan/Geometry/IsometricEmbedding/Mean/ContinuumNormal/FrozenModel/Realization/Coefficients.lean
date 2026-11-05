module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Realization.Primitives
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Realization.Support
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity.Primitive
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedShell

/-!
# Measured frozen coefficients on the original input cone

These are the literal `PrimitiveRegularity`, original-mask support and inverse
upper-bound inputs of the supported global carrier constructor. The normal
regularity is derived from the retained initial datum and time-zero footpoint;
for unit initial data no flow regularity is required. The geometry is exactly
the frozen inverse already used by the spectral symbol (`new:lem:scaling`,
`app:ch_background:eq:bg-full-complex-amplitude`).
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
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (hcell : 4 * a < 1 / 2)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) ha
  (And.left (angularWidth_spec hηb hr))
local notation "e₀" => normalizedCarrierData T Q F row col Φ Y initial ha hcell angular₀
  FixedCutoffs.highFrequency 0
local notation "d₀" => coefficientsOfCarrier e₀ (FixedCutoffs.physical ha 1)
local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)

/-- The three original nonzero masks put the input in the exact conic mask
support. This is the supported constructor's primitive support premise for
the literal frozen coefficients (`app:ch_background:defn:bg-row`). -/
theorem canonicalFrozen_primitive_mask_support
    {p : InputVariables n} (hp : p ∈ frozenInputDomain z₀ ηb r (6 * a))
    (hx : (d₀).measurement p.1.1 ≠ 0) (hy : (d₀).measurement p.1.2 ≠ 0)
    (hang : (d₀).angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0) :
    p ∈ conicMaskSupport z₀ ηb r a :=
  primitive_masks_mem_conicMaskSupport hηb hr ha hp.2.2.1 hx hy hang

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

include hP har hcarrier hf hInv htrans hcJ

/-- All primitive regularity fields for the actual measured frozen
coefficients, including its literal Jacobian. The geometric inputs are
outputs of `exists_frozen_conic_inputs`; only primitive initial smoothness
and the retained footpoint's domain/range are used for the scalar multiplier
(`new:lem:scaling`, `app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalizedCarrierData_zero_primitiveRegularity
    {D : Set (Euclidean (n - 1) × Euclidean 3)}
    {Dflow : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hi : ContDiffOn ℝ ∞ initial D) (hY : ContDiffOn ℝ ∞ Y Dflow)
    (hseed : MapsTo (fun z : CarrierParameter ↦ ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z)))
      (ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) (6 * a)) Dflow)
    (hYrange : MapsTo Y Dflow D) :
    PrimitiveRegularity d₀ J₀ (frozenInputDomain z₀ ηb r (6 * a)) := by
  let Z := ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) (6 * a)
  have hZ : Z ⊆ parameter ⁻¹' parameterInterior (2 * P.radius) := by
    intro z hz i
    have hm := hcarrier (a := (z.2, z.1))
      ⟨(ball_subset_closedBall.trans (closedBall_subset_closedBall har)) hz.2,
        (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hz.1⟩ i
    exact hm.trans_le (by linarith [hP.1])
  have hYs := hY.comp
    (contDiffOn_const.prodMk (contDiffOn_const.prodMk parameter.contDiff.contDiffOn)) hseed
  have hn := (frozenSeedNormal_smooth T Q F row col Φ Y hP initial hi hZ hYs
    (hYrange.comp hseed)).comp
      (s := frozenInputDomain z₀ ηb r (6 * a)) contDiffOn_snd.fst
        (fun _ hp ↦ ⟨hp.2.1, hp.1.1⟩)
  have hu := frozenPrimitiveRegularity_unit T Q hP hηb hr ha har hcarrier
    hf hInv htrans hcJ F row col Φ Y
  rw [coefficientsOfCarrier_normalizedCarrierData_zero]
  exact ⟨(FixedCutoffs.physical ha 1).contDiff.comp_contDiffOn contDiffOn_fst.fst,
    (FixedCutoffs.physical ha 1).contDiff.comp_contDiffOn contDiffOn_fst.snd,
    hu.angular, hu.high, hn, hn, hu.leftReduced, hu.rightReduced,
    hu.jacobian, hu.jacobian_ne_zero, hu.covector_ne_zero⟩

/-- The original measured unit-initial carrier satisfies every primitive
regularity field on its exact frozen input cone, without a flow assumption
(`new:lem:scaling`, `app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalizedCarrierData_zero_unit_primitiveRegularity :
    PrimitiveRegularity
      (coefficientsOfCarrier
        (normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) ha hcell angular₀
          FixedCutoffs.highFrequency 0) (FixedCutoffs.physical ha 1))
      J₀ (frozenInputDomain z₀ ηb r (6 * a)) := by
  rw [normalizedCarrierData_zero_unit_independent_flow T Q F row col Φ Y Φ (fun _ ↦ 0)]
  exact normalizedCarrierData_zero_primitiveRegularity T Q F row col Φ (fun _ ↦ 0)
    (fun _ ↦ 1) hηb hr ha hcell hP har hcarrier hf hInv htrans hcJ
    (D := univ) (Dflow := univ) contDiffOn_const contDiffOn_const
    (fun _ _ ↦ mem_univ _) (fun _ _ ↦ mem_univ _)

omit hP har hcarrier hf hcJ in
include hηb hr in
/-- The SAME frozen inverse has the supported constructor's upper frequency
bound `Cupper = 2`. The norm on the right is the physical Euclidean frequency;
the high-cutoff threshold still uses the separate lower comparison
`frozenInverse_frequency_comparison` (`app:ch_background:eq:bg-Psi`). -/
theorem frozenSymbolInverse_norm_le_two {p : Variables n × Euclidean 2}
    (hp : p ∈ frozenSymbolDomain T Q z₀ ηb r (6 * a)) :
    ‖(frozenSymbolInverse T Q z₀ ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖ :=
  symbolInverse_norm_le_two T Q hηb hr hInv htrans hp

end JanetCartan.ContinuumNormal.FrozenModel
