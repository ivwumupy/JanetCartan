module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedKernel.Support
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.KernelCoefficients

/-!
# Primitive regularity for refined masks on the retained outer domain

The normal and detector are smooth on `coefficientDomain z₀ r (6*a)`, as
required from `CanonicalBudgets`/`ActualAmplitude`: the actual producers are
`CanonicalCarrier.exists_projected_normalField_bounds` and
`CanonicalCarrier.quadratic_canonical_smooth`, restricted to this domain.
The parent retains these domain containments. Only the physical and angular
masks use `a'` and `r'`. Both unregularized and regularized primitive inputs are
exposed for `exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option quotPrecheck false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol TransportKernel
open CarrierNormalRealization

variable {n : ℕ}

variable {N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr' : 0 < r') (ha' : 0 < a') (hcell' : 4 * a' < 1 / 2)

local notation "d" => data T Q F row col Φ Y initial ha' hcell'
  (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
  FixedCutoffs.highFrequency

variable
    (hnormal : ContDiffOn ℝ ∞ (Function.uncurry (normalField T Q F row col Φ Y initial))
      (coefficientDomain z₀ r (6 * a)))
    (hdetector : ∀ i : Fin n, ContDiffOn ℝ ∞
      (fun p : Euclidean n × CarrierParameter ↦
        quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2)) i)
      (coefficientDomain z₀ r (6 * a)))

include hnormal hdetector in
/-- The exact unregularized original coefficients with the refined masks.
The Jacobian-one version is only used to prove measurability before division; it asserts no geometric fact (`bg-full-complex-amplitude`). -/
theorem refined_coefficients_regularity_one :
    PrimitiveRegularity (coefficientsOfCarrier d (FixedCutoffs.physical ha' 1))
      (fun _ ↦ 1) (symbolInputDomain z₀ ηb r (6 * a)) := by
  refine ⟨?_, ?_, angularMask_smooth .., FixedCutoffs.highFrequency_smooth,
    ?_, ?_, ?_, ?_, contDiffOn_const, fun _ _ ↦ one_ne_zero, fun _ hp ↦ hp.2.2.1⟩
  · exact (FixedCutoffs.physical ha' 1).contDiff.comp_contDiffOn contDiffOn_fst.fst
  · exact (FixedCutoffs.physical ha' 1).contDiff.comp_contDiffOn contDiffOn_fst.snd
  · exact hnormal.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd.fst)
      (coefficient_evaluation_ranges z₀ ηb r (6 * a)).1
  · exact hnormal.comp (contDiffOn_fst.snd.prodMk contDiffOn_snd.fst)
      (coefficient_evaluation_ranges z₀ ηb r (6 * a)).2
  · intro i
    have hi := (hdetector i).comp (s := symbolInputDomain z₀ ηb r (6 * a))
      (f := fun p : InputVariables n ↦ (p.1.1, p.2.1))
      (contDiffOn_fst.fst.prodMk contDiffOn_snd.fst)
      (coefficient_evaluation_ranges z₀ ηb r (6 * a)).1
    apply hi.congr
    intro p _
    exact congrArg (fun v : Euclidean n ↦ v i)
      (reducedCovector_data T Q F row col Φ Y initial ha' hcell' _ _ _ _)
  · intro i
    have hi := (hdetector i).comp (s := symbolInputDomain z₀ ηb r (6 * a))
      (f := fun p : InputVariables n ↦ (p.1.2, p.2.1))
      (contDiffOn_fst.snd.prodMk contDiffOn_snd.fst)
      (coefficient_evaluation_ranges z₀ ηb r (6 * a)).2
    apply hi.congr
    intro p _
    exact congrArg (fun v : Euclidean n ↦ v i)
      (reducedCovector_data T Q F row col Φ Y initial ha' hcell' _ _ _ _)

include hnormal hdetector in
/-- Global density measurability from the exact primitive regularity and
the proved support of the canonical masks (`bg-full-complex-amplitude`). -/
theorem refined_normalDensityEntry_measurable
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (R : ℝ)
    (x y : Torus n) (hx : x ∈ (d).outputChart) (hy : y ∈ (d).outputChart) (i j : Fin n) :
    Measurable (fun u ↦
      normalDensityEntry d (radialCarrierMask FixedCutoffs.radialRegularization R) x y u i j) := by
  classical
  let W : Set (CarrierVariable n) :=
    (fun u ↦ (((d).chartPoint x, (d).chartPoint y), u)) ⁻¹'
      symbolInputDomain z₀ ηb r (6 * a)
  have hW : IsOpen W := (symbolInputDomain_open z₀ ηb r (6 * a)).preimage
    (continuous_const.prodMk continuous_id)
  have hreg := (refined_coefficients_regularity_one T Q F row col Φ Y initial
    hηb hr' ha' hcell' hnormal hdetector).regularized FixedCutoffs.radialRegularization_smooth R
  have hs := (realMatrixEntry i j).contDiff.comp_contDiffOn (inputDensity_contDiffOn hreg)
  have hc : ContinuousOn
      (fun u ↦ normalDensityEntry d (radialCarrierMask FixedCutoffs.radialRegularization R)
        x y u i j) W := by
    apply ((hs.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hu ↦ hu)).continuousOn).congr
    intro u _
    exact normalDensityEntry_eq_inputDensity_one T Q F row col Φ Y initial hηb hr' ha' hcell' R x y u i j
  have he : (fun u ↦ normalDensityEntry d
      (radialCarrierMask FixedCutoffs.radialRegularization R) x y u i j) =
      W.indicator (fun u ↦ normalDensityEntry d
        (radialCarrierMask FixedCutoffs.radialRegularization R) x y u i j) := by
    funext u
    by_cases hu : u ∈ W
    · simp only [indicator_of_mem hu]
    · rw [indicator_of_notMem hu]
      exact normalDensityEntry_zero_outside_symbolInputDomain T Q F row col Φ Y initial
        hηb hr' ha' har' hcell' _ _ x y hx hy u
        (fun hp ↦ hu (symbolInputDomain_mono z₀ ηb hrr
          (mul_le_mul_of_nonneg_left haa (by norm_num)) hp)) i j
  rw [he]
  exact hc.measurable_piecewise continuousOn_const hW.measurableSet

variable (hr : 0 < r) {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hr hnormal hdetector hf hInv htrans in
/-- Actual primitive regularity for the kernel symbol. The Jacobian fields
are proved from the actual cone; the only analytic inputs are the canonical
normal and detector supplied by `CanonicalBudgets`/`ActualAmplitude`
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem refined_coefficients_regularity (hcJ : 0 < cJ) :
    PrimitiveRegularity (coefficientsOfCarrier d (FixedCutoffs.physical ha' 1))
      (symbolJacobian T Q) (symbolInputDomain z₀ ηb r (6 * a)) := by
  have hreg := refined_coefficients_regularity_one T Q F row col Φ Y initial
    hηb hr' ha' hcell' hnormal hdetector
  have he := symbolJacobian_eq_actual T Q hηb hr hf
  have hj := (transportAbsoluteJacobian_smooth T Q hηb hr hf hInv htrans hcJ).congr he
  have hjne : ∀ p ∈ symbolInputDomain z₀ ηb r (6 * a), symbolJacobian T Q p ≠ 0 := by
    intro p hp
    rw [he hp]
    exact ne_of_gt (transportAbsoluteJacobian_pos T Q hηb hr hf hInv htrans hcJ hp)
  exact { hreg with jacobian := hj, jacobian_ne_zero := hjne }

include hr hnormal hdetector hf hInv htrans in
/-- Radial regularization preserves the same outer-domain primitive regularity
and determinant, with the smaller masks unchanged. Consumer:
`refinedKernelSymbolInputs` (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem refined_regularizedCoefficients_regularity (hcJ : 0 < cJ) (R : ℝ) :
    PrimitiveRegularity (regularizedCoefficients
      (coefficientsOfCarrier d (FixedCutoffs.physical ha' 1)) FixedCutoffs.radialRegularization R)
      (symbolJacobian T Q) (symbolInputDomain z₀ ηb r (6 * a)) :=
  (refined_coefficients_regularity T Q F row col Φ Y initial hηb hr' ha' hcell'
    hnormal hdetector hr hf hInv htrans hcJ).regularized
      FixedCutoffs.radialRegularization_smooth R

end JanetCartan.ContinuumRow.CanonicalConic
