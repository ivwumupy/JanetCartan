module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Coefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Kernel.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedKernel.Coefficients

/-!
# The measured frozen density with smaller masks

The literal unit-initial normal and detector are smooth by the seed theorems.
Here their original masks are retained on the larger frozen inverse domain.
These are the regularity, support, and measurability inputs of
`frozenRefinedKernelChartInputs` and `frozenRefinedKernelSymbolInputs`, consumed by the
supported carrier realization (`new:lem:scaling`,
`app:ch_background:eq:bg-full-complex-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr' : 0 < r') (ha' : 0 < a') (hcell' : 4 * a' < 1 / 2)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) ha'
  (And.left (angularWidth_spec hηb hr'))
local notation "e₀" => normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1)
  ha' hcell' angular₀ FixedCutoffs.highFrequency 0
local notation "d₀" => coefficientsOfCarrier e₀ (FixedCutoffs.physical ha' 1)

/-- The original two-position density is the undivided measured primitive
formula, including both measurement factors and the squared radial mask
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenNormalDensityEntry_eq_inputDensity_one (R : ℝ) (x y : Torus n)
    (u : CarrierVariable n) (i j : Fin n) :
    normalDensityEntry e₀ (radialCarrierMask FixedCutoffs.radialRegularization R) x y u i j =
      inputDensity (regularizedCoefficients d₀ FixedCutoffs.radialRegularization R)
        (fun _ ↦ 1) (((e₀).chartPoint x, (e₀).chartPoint y), u) i j := by
  simp only [normalDensityEntry, radialCarrierMask, inputDensity, inputWeight,
    regularizedCoefficients, coefficientsOfCarrier, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, div_one, normalizedCarrierData, data,
    FixedCutoffs.periodic_apply]
  ring

/-- Outside the outer frozen cone the literal density vanishes by the
original angular mask or the frequency factor (`bg-full-complex-amplitude`). -/
theorem frozenNormalDensityEntry_zero_outside
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r')
    (m : CarrierVariable n → ℝ) (x y : Torus n) (u : CarrierVariable n)
    (hu : (((e₀).chartPoint x, (e₀).chartPoint y), u) ∉ frozenInputDomain z₀ ηb r (6 * a))
    (i j : Fin n) : normalDensityEntry e₀ m x y u i j = 0 := by
  by_cases hη : u.2 = 0
  · simp [normalDensityEntry, hη]
  have hm : angular₀ u.1 (‖u.2‖⁻¹ • u.2) = 0 := by
    by_contra hm
    have hzero : (0 : Euclidean n) ∈ closedBall 0 (4 * a') := by simp; positivity
    have hi := angularMask_mem_symbolInputDomain hηb hr' ha' har' hzero hzero hη hm
    exact hu (symbolInputDomain_mono z₀ ηb hrr
      (mul_le_mul_of_nonneg_left haa (by norm_num)) hi)
  simp only [normalDensityEntry, normalizedCarrierData, data, hm,
    zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]

variable {c C : ℝ} (hP : P.IsValid c C) (hr : 0 < r) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))

include hP hr har hcarrier in
/-- All original measured coefficient fields are smooth on the outer frozen
cone. The constant denominator here is used only for density measurability
(`new:lem:scaling`, `bg-full-complex-amplitude`). -/
theorem frozenRefined_coefficients_regularity_one :
    PrimitiveRegularity d₀ (fun _ ↦ 1) (frozenInputDomain z₀ ηb r (6 * a)) := by
  rw [coefficientsOfCarrier_normalizedCarrierData_zero]
  have hm := frozenInputDomain_carrier_subset (ηb := ηb) hP hr har hcarrier
  have hn := (frozenSeedNormal_unit_smooth T Q F row col Φ Y hP).comp contDiffOn_snd.fst hm
  have hq := (PiLp.contDiff_ofLp.comp_contDiffOn (frozenSeedDetector_smooth T Q hP)).comp
    contDiffOn_snd.fst hm
  exact ⟨(FixedCutoffs.physical ha' 1).contDiff.comp_contDiffOn contDiffOn_fst.fst,
    (FixedCutoffs.physical ha' 1).contDiff.comp_contDiffOn contDiffOn_fst.snd,
    angularMask_smooth z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1,
    FixedCutoffs.highFrequency_smooth, hn, hn, contDiffOn_pi.mp hq, contDiffOn_pi.mp hq,
    contDiffOn_const, fun _ _ ↦ one_ne_zero, fun _ hp ↦ hp.2.2.1⟩

include hP hr har hcarrier in
/-- Global measurability of the literal frozen two-position density follows
from its proved original support and seed coefficient regularity
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenNormalDensityEntry_measurable
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r')
    (R : ℝ) (x y : Torus n) (i j : Fin n) :
    Measurable (fun u ↦ normalDensityEntry e₀
      (radialCarrierMask FixedCutoffs.radialRegularization R) x y u i j) := by
  classical
  let W : Set (CarrierVariable n) :=
    (fun u ↦ (((e₀).chartPoint x, (e₀).chartPoint y), u)) ⁻¹'
      frozenInputDomain z₀ ηb r (6 * a)
  have hW : IsOpen W := (frozenInputDomain_open z₀ ηb r (6 * a)).preimage
    (continuous_const.prodMk continuous_id)
  have hreg := (frozenRefined_coefficients_regularity_one T Q F row col Φ Y
    hηb hr' ha' hcell' hP hr har hcarrier).regularized FixedCutoffs.radialRegularization_smooth R
  have hs := (realMatrixEntry i j).contDiff.comp_contDiffOn (inputDensity_contDiffOn hreg)
  have hc : ContinuousOn (fun u ↦ normalDensityEntry e₀
      (radialCarrierMask FixedCutoffs.radialRegularization R) x y u i j) W := by
    apply ((hs.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hu ↦ hu)).continuousOn).congr
    exact fun u _ ↦ frozenNormalDensityEntry_eq_inputDensity_one T Q F row col Φ Y
      hηb hr' ha' hcell' R x y u i j
  have he : (fun u ↦ normalDensityEntry e₀
      (radialCarrierMask FixedCutoffs.radialRegularization R) x y u i j) =
      W.indicator (fun u ↦ normalDensityEntry e₀
        (radialCarrierMask FixedCutoffs.radialRegularization R) x y u i j) := by
    funext u
    by_cases hu : u ∈ W
    · simp only [indicator_of_mem hu]
    · rw [indicator_of_notMem hu]
      exact frozenNormalDensityEntry_zero_outside T Q F row col Φ Y
        hηb hr' ha' hcell' hrr haa har' _ x y u hu i j
  rw [he]
  exact hc.measurable_piecewise continuousOn_const hW.measurableSet

variable {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hcJ : 0 < cJ)

include hP hr har hcarrier hf hInv htrans hcJ in
/-- The refined measured carrier has primitive regularity with its literal
frozen Jacobian on the retained outer cone. No normal or detector regularity
is assumed (`new:lem:scaling`, `bg-full-complex-amplitude`). -/
theorem frozenRefined_coefficients_regularity :
    PrimitiveRegularity d₀
      (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0))
      (frozenInputDomain z₀ ηb r (6 * a)) :=
  { frozenRefined_coefficients_regularity_one T Q F row col Φ Y hηb hr' ha' hcell'
      hP hr har hcarrier with
    jacobian := frozenJacobian_smooth T Q hP hηb hr har hcarrier hInv htrans hf hcJ
    jacobian_ne_zero := fun _ hp ↦
      (frozenJacobian_pos T Q hP hηb hr har hcarrier hInv htrans hf hcJ hp).ne' }

include hP hr har hcarrier hf hInv htrans hcJ in
/-- Every finite radial band retains those same primitive fields and the
same literal frozen Jacobian (`bg-full-complex-amplitude`). -/
theorem frozenRefined_regularizedCoefficients_regularity (R : ℝ) :
    PrimitiveRegularity (regularizedCoefficients d₀ FixedCutoffs.radialRegularization R)
      (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0))
      (frozenInputDomain z₀ ηb r (6 * a)) :=
  (frozenRefined_coefficients_regularity T Q F row col Φ Y hηb hr' ha' hcell'
    hP hr har hcarrier hf hInv htrans hcJ).regularized FixedCutoffs.radialRegularization_smooth R

end JanetCartan.ContinuumNormal.FrozenModel
